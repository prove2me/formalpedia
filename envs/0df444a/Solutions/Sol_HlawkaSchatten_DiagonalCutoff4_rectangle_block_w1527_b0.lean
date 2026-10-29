-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1527_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:10.463993+00:00
-- url     : https://prove2.me/submissions/bd0def43-2286-418d-8180-ffafebc5af7c

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
theorem support_rectangle_w1527_s0_0 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1670039923/10000000000 : ℝ)*x 0 + (118027451/200000000 : ℝ)*x 1 + (486168111/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1670039923/10000000000 : ℝ)^4551 ≤ (9932528010377/100000000000000 : ℝ)^3527 := by
    have hnat : (1670039923 : ℕ)^4551*100000000000000^3527 ≤ 9932528010377^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670039923 10000000000 9932528010377 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118027451/200000000 : ℝ)^4551 ≤ (5063530503811/10000000000000 : ℝ)^3527 := by
    have hnat : (118027451 : ℕ)^4551*10000000000000^3527 ≤ 5063530503811^3527*200000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118027451 200000000 5063530503811 10000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (486168111/1000000000 : ℝ)^4551 ≤ (39432166930921/100000000000000 : ℝ)^3527 := by
    have hnat : (486168111 : ℕ)^4551*100000000000000^3527 ≤ 39432166930921^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486168111 1000000000 39432166930921 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1670039923/10000000000 : ℝ), (118027451/200000000 : ℝ), (486168111/1000000000 : ℝ)] ![(9932528010377/100000000000000 : ℝ), (5063530503811/10000000000000 : ℝ), (39432166930921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1670039923/10000000000 : ℝ)|^4551 ≤ (9932528010377/100000000000000 : ℝ)^3527
        have hw : |(-1670039923/10000000000 : ℝ)|=(1670039923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118027451/200000000 : ℝ)|^4551 ≤ (5063530503811/10000000000000 : ℝ)^3527
        have hw : |(118027451/200000000 : ℝ)|=(118027451/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(486168111/1000000000 : ℝ)|^4551 ≤ (39432166930921/100000000000000 : ℝ)^3527
        have hw : |(486168111/1000000000 : ℝ)|=(486168111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_1 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2737361707/5000000000 : ℝ)*x 0 + (-1125845567/5000000000 : ℝ)*x 1 + (4861681139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737361707/5000000000 : ℝ)^4551 ≤ (45962159358121/100000000000000 : ℝ)^3527 := by
    have hnat : (2737361707 : ℕ)^4551*100000000000000^3527 ≤ 45962159358121^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737361707 5000000000 45962159358121 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125845567/5000000000 : ℝ)^4551 ≤ (14605673392507/100000000000000 : ℝ)^3527 := by
    have hnat : (1125845567 : ℕ)^4551*100000000000000^3527 ≤ 14605673392507^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125845567 5000000000 14605673392507 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4861681139/10000000000 : ℝ)^4551 ≤ (4929020904303/12500000000000 : ℝ)^3527 := by
    have hnat : (4861681139 : ℕ)^4551*12500000000000^3527 ≤ 4929020904303^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4861681139 10000000000 4929020904303 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737361707/5000000000 : ℝ), (-1125845567/5000000000 : ℝ), (4861681139/10000000000 : ℝ)] ![(45962159358121/100000000000000 : ℝ), (14605673392507/100000000000000 : ℝ), (4929020904303/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737361707/5000000000 : ℝ)|^4551 ≤ (45962159358121/100000000000000 : ℝ)^3527
        have hw : |(2737361707/5000000000 : ℝ)|=(2737361707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1125845567/5000000000 : ℝ)|^4551 ≤ (14605673392507/100000000000000 : ℝ)^3527
        have hw : |(-1125845567/5000000000 : ℝ)|=(1125845567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4861681139/10000000000 : ℝ)|^4551 ≤ (4929020904303/12500000000000 : ℝ)^3527
        have hw : |(4861681139/10000000000 : ℝ)|=(4861681139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_2 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5474723393/10000000000 : ℝ)*x 0 + (4861681129/10000000000 : ℝ)*x 1 + (-1125845587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5474723393/10000000000 : ℝ)^4551 ≤ (45962159130633/100000000000000 : ℝ)^3527 := by
    have hnat : (5474723393 : ℕ)^4551*100000000000000^3527 ≤ 45962159130633^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474723393 10000000000 45962159130633 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4861681129/10000000000 : ℝ)^4551 ≤ (4929020891221/12500000000000 : ℝ)^3527 := by
    have hnat : (4861681129 : ℕ)^4551*12500000000000^3527 ≤ 4929020891221^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4861681129 10000000000 4929020891221 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125845587/5000000000 : ℝ)^4551 ≤ (7302836863649/50000000000000 : ℝ)^3527 := by
    have hnat : (1125845587 : ℕ)^4551*50000000000000^3527 ≤ 7302836863649^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125845587 5000000000 7302836863649 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5474723393/10000000000 : ℝ), (4861681129/10000000000 : ℝ), (-1125845587/5000000000 : ℝ)] ![(45962159130633/100000000000000 : ℝ), (4929020891221/12500000000000 : ℝ), (7302836863649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5474723393/10000000000 : ℝ)|^4551 ≤ (45962159130633/100000000000000 : ℝ)^3527
        have hw : |(5474723393/10000000000 : ℝ)|=(5474723393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4861681129/10000000000 : ℝ)|^4551 ≤ (4929020891221/12500000000000 : ℝ)^3527
        have hw : |(4861681129/10000000000 : ℝ)|=(4861681129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125845587/5000000000 : ℝ)|^4551 ≤ (7302836863649/50000000000000 : ℝ)^3527
        have hw : |(-1125845587/5000000000 : ℝ)|=(1125845587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_3 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4141123179/10000000000 : ℝ)*x 0 + (772872589/2500000000 : ℝ)*x 1 + (5474019727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4141123179/10000000000 : ℝ)^4551 ≤ (2003712545309/6250000000000 : ℝ)^3527 := by
    have hnat : (4141123179 : ℕ)^4551*6250000000000^3527 ≤ 2003712545309^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141123179 10000000000 2003712545309 6250000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (772872589/2500000000 : ℝ)^4551 ≤ (4397212528091/20000000000000 : ℝ)^3527 := by
    have hnat : (772872589 : ℕ)^4551*20000000000000^3527 ≤ 4397212528091^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772872589 2500000000 4397212528091 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474019727/10000000000 : ℝ)^4551 ≤ (45954536619279/100000000000000 : ℝ)^3527 := by
    have hnat : (5474019727 : ℕ)^4551*100000000000000^3527 ≤ 45954536619279^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474019727 10000000000 45954536619279 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4141123179/10000000000 : ℝ), (772872589/2500000000 : ℝ), (5474019727/10000000000 : ℝ)] ![(2003712545309/6250000000000 : ℝ), (4397212528091/20000000000000 : ℝ), (45954536619279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4141123179/10000000000 : ℝ)|^4551 ≤ (2003712545309/6250000000000 : ℝ)^3527
        have hw : |(4141123179/10000000000 : ℝ)|=(4141123179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(772872589/2500000000 : ℝ)|^4551 ≤ (4397212528091/20000000000000 : ℝ)^3527
        have hw : |(772872589/2500000000 : ℝ)|=(772872589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474019727/10000000000 : ℝ)|^4551 ≤ (45954536619279/100000000000000 : ℝ)^3527
        have hw : |(5474019727/10000000000 : ℝ)|=(5474019727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_4 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1673434341/10000000000 : ℝ)*x 0 + (2444061731/5000000000 : ℝ)*x 1 + (587398519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1673434341/10000000000 : ℝ)^4551 ≤ (9958585207781/100000000000000 : ℝ)^3527 := by
    have hnat : (1673434341 : ℕ)^4551*100000000000000^3527 ≤ 9958585207781^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673434341 10000000000 9958585207781 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2444061731/5000000000 : ℝ)^4551 ≤ (992728028243/2500000000000 : ℝ)^3527 := by
    have hnat : (2444061731 : ℕ)^4551*2500000000000^3527 ≤ 992728028243^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2444061731 5000000000 992728028243 2500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587398519/1000000000 : ℝ)^4551 ≤ (25166146827707/50000000000000 : ℝ)^3527 := by
    have hnat : (587398519 : ℕ)^4551*50000000000000^3527 ≤ 25166146827707^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587398519 1000000000 25166146827707 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1673434341/10000000000 : ℝ), (2444061731/5000000000 : ℝ), (587398519/1000000000 : ℝ)] ![(9958585207781/100000000000000 : ℝ), (992728028243/2500000000000 : ℝ), (25166146827707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1673434341/10000000000 : ℝ)|^4551 ≤ (9958585207781/100000000000000 : ℝ)^3527
        have hw : |(-1673434341/10000000000 : ℝ)|=(1673434341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2444061731/5000000000 : ℝ)|^4551 ≤ (992728028243/2500000000000 : ℝ)^3527
        have hw : |(2444061731/5000000000 : ℝ)|=(2444061731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(587398519/1000000000 : ℝ)|^4551 ≤ (25166146827707/50000000000000 : ℝ)^3527
        have hw : |(587398519/1000000000 : ℝ)|=(587398519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_5 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2595303491/5000000000 : ℝ)*x 0 + (-1239387239/10000000000 : ℝ)*x 1 + (1174797049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595303491/5000000000 : ℝ)^4551 ≤ (42907868340209/100000000000000 : ℝ)^3527 := by
    have hnat : (2595303491 : ℕ)^4551*100000000000000^3527 ≤ 42907868340209^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595303491 5000000000 42907868340209 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1239387239/10000000000 : ℝ)^4551 ≤ (1689959346393/25000000000000 : ℝ)^3527 := by
    have hnat : (1239387239 : ℕ)^4551*25000000000000^3527 ≤ 1689959346393^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239387239 10000000000 1689959346393 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174797049/2000000000 : ℝ)^4551 ≤ (25166147131759/50000000000000 : ℝ)^3527 := by
    have hnat : (1174797049 : ℕ)^4551*50000000000000^3527 ≤ 25166147131759^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174797049 2000000000 25166147131759 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595303491/5000000000 : ℝ), (-1239387239/10000000000 : ℝ), (1174797049/2000000000 : ℝ)] ![(42907868340209/100000000000000 : ℝ), (1689959346393/25000000000000 : ℝ), (25166147131759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595303491/5000000000 : ℝ)|^4551 ≤ (42907868340209/100000000000000 : ℝ)^3527
        have hw : |(2595303491/5000000000 : ℝ)|=(2595303491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1239387239/10000000000 : ℝ)|^4551 ≤ (1689959346393/25000000000000 : ℝ)^3527
        have hw : |(-1239387239/10000000000 : ℝ)|=(1239387239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174797049/2000000000 : ℝ)|^4551 ≤ (25166147131759/50000000000000 : ℝ)^3527
        have hw : |(1174797049/2000000000 : ℝ)|=(1174797049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_6 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2595303469/5000000000 : ℝ)*x 0 + (587398547/1000000000 : ℝ)*x 1 + (-1239386953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595303469/5000000000 : ℝ)^4551 ≤ (8581573574177/20000000000000 : ℝ)^3527 := by
    have hnat : (2595303469 : ℕ)^4551*20000000000000^3527 ≤ 8581573574177^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595303469 5000000000 8581573574177 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (587398547/1000000000 : ℝ)^4551 ≤ (50332296751217/100000000000000 : ℝ)^3527 := by
    have hnat : (587398547 : ℕ)^4551*100000000000000^3527 ≤ 50332296751217^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587398547 1000000000 50332296751217 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239386953/10000000000 : ℝ)^4551 ≤ (6759835372791/100000000000000 : ℝ)^3527 := by
    have hnat : (1239386953 : ℕ)^4551*100000000000000^3527 ≤ 6759835372791^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239386953 10000000000 6759835372791 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595303469/5000000000 : ℝ), (587398547/1000000000 : ℝ), (-1239386953/10000000000 : ℝ)] ![(8581573574177/20000000000000 : ℝ), (50332296751217/100000000000000 : ℝ), (6759835372791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595303469/5000000000 : ℝ)|^4551 ≤ (8581573574177/20000000000000 : ℝ)^3527
        have hw : |(2595303469/5000000000 : ℝ)|=(2595303469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(587398547/1000000000 : ℝ)|^4551 ≤ (50332296751217/100000000000000 : ℝ)^3527
        have hw : |(587398547/1000000000 : ℝ)|=(587398547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1239386953/10000000000 : ℝ)|^4551 ≤ (6759835372791/100000000000000 : ℝ)^3527
        have hw : |(-1239386953/10000000000 : ℝ)|=(1239386953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s0_7 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4148900937/10000000000 : ℝ)*x 0 + (2706712543/5000000000 : ℝ)*x 1 + (126170007/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4148900937/10000000000 : ℝ)^4551 ≤ (1004284902989/3125000000000 : ℝ)^3527 := by
    have hnat : (4148900937 : ℕ)^4551*3125000000000^3527 ≤ 1004284902989^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148900937 10000000000 1004284902989 3125000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706712543/5000000000 : ℝ)^4551 ≤ (45299210690187/100000000000000 : ℝ)^3527 := by
    have hnat : (2706712543 : ℕ)^4551*100000000000000^3527 ≤ 45299210690187^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706712543 5000000000 45299210690187 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126170007/400000000 : ℝ)^4551 ≤ (4512734480829/20000000000000 : ℝ)^3527 := by
    have hnat : (126170007 : ℕ)^4551*20000000000000^3527 ≤ 4512734480829^3527*400000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126170007 400000000 4512734480829 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4148900937/10000000000 : ℝ), (2706712543/5000000000 : ℝ), (126170007/400000000 : ℝ)] ![(1004284902989/3125000000000 : ℝ), (45299210690187/100000000000000 : ℝ), (4512734480829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4148900937/10000000000 : ℝ)|^4551 ≤ (1004284902989/3125000000000 : ℝ)^3527
        have hw : |(4148900937/10000000000 : ℝ)|=(4148900937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706712543/5000000000 : ℝ)|^4551 ≤ (45299210690187/100000000000000 : ℝ)^3527
        have hw : |(2706712543/5000000000 : ℝ)|=(2706712543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126170007/400000000 : ℝ)|^4551 ≤ (4512734480829/20000000000000 : ℝ)^3527
        have hw : |(126170007/400000000 : ℝ)|=(126170007/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1527_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3019/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25291/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4549/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4549 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4549*1^1024 ≤ 0^1024*1^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4549/1024 : ℝ) ≤ (170686095966494353/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4549 ≤ (170686095966494353/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4549*10000000000000000000^1024 ≤ 170686095966494353^1024*5^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 170686095966494353 10000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (170686095966494353/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4549 := by
      have hnat : (1 : ℕ)^1024*1^4549 ≤ 1^4549*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10170686095966494353/10000000000000000000 : ℝ) ≤ (2509542659211209/2500000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (10170686095966494353/10000000000000000000 : ℝ)^1024 ≤ (2509542659211209/2500000000000000 : ℝ)^4549 := by
      have hnat : (10170686095966494353 : ℕ)^1024*2500000000000000^4549 ≤ 2509542659211209^4549*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10170686095966494353 10000000000000000000 2509542659211209 2500000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509542659211209/2500000000000000 : ℝ)) (X := (10170686095966494353/10000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5170686095966494353/5000000000000000000 : ℝ) ≤ (1259542659211209/1250000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (5170686095966494353/5000000000000000000 : ℝ)^1024 ≤ (1259542659211209/1250000000000000 : ℝ)^4549 := by
      have hnat : (5170686095966494353 : ℕ)^1024*1250000000000000^4549 ≤ 1259542659211209^4549*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5170686095966494353 5000000000000000000 1259542659211209 1250000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1259542659211209/1250000000000000 : ℝ)) (X := (5170686095966494353/5000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9542659211209/1000000000000000 : ℝ)*(0 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9542659211209/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(170686095966494353/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9542659211209/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4549/1024 : ℝ) := by
    rw [show (1 : ℝ)+(9542659211209/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2509542659211209/2500000000000000 : ℝ) by norm_num, show 1+(170686095966494353/10000000000000000000 : ℝ)+(0 : ℝ)=(10170686095966494353/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(170686095966494353/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9542659211209/1000000000000000 : ℝ)*(2/5 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(9542659211209/1000000000000000 : ℝ)*(2/5 : ℝ)=(1259542659211209/1250000000000000 : ℝ) by norm_num, show 1+2*(170686095966494353/10000000000000000000 : ℝ)=(5170686095966494353/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9542659211209/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9542659211209/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9542659211209/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9542659211209/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9542659211209/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9542659211209/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1670039923/10000000000 : ℝ)*X 0 0+(118027451/200000000 : ℝ)*X 0 1+(486168111/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2737361707/5000000000 : ℝ)*X 1 0+(-1125845567/5000000000 : ℝ)*X 1 1+(4861681139/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5474723393/10000000000 : ℝ)*X 2 0+(4861681129/10000000000 : ℝ)*X 2 1+(-1125845587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4141123179/10000000000 : ℝ)*X 0 0+(772872589/2500000000 : ℝ)*X 0 1+(5474019727/10000000000 : ℝ)*X 0 2+(4141123179/10000000000 : ℝ)*X 1 0+(772872589/2500000000 : ℝ)*X 1 1+(5474019727/10000000000 : ℝ)*X 1 2+(4141123179/10000000000 : ℝ)*X 2 0+(772872589/2500000000 : ℝ)*X 2 1+(5474019727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1673434341/10000000000 : ℝ)*X 0 0+(2444061731/5000000000 : ℝ)*X 0 1+(587398519/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2595303491/5000000000 : ℝ)*X 1 0+(-1239387239/10000000000 : ℝ)*X 1 1+(1174797049/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2595303469/5000000000 : ℝ)*X 2 0+(587398547/1000000000 : ℝ)*X 2 1+(-1239386953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4148900937/10000000000 : ℝ)*X 0 0+(2706712543/5000000000 : ℝ)*X 0 1+(126170007/400000000 : ℝ)*X 0 2+(4148900937/10000000000 : ℝ)*X 1 0+(2706712543/5000000000 : ℝ)*X 1 1+(126170007/400000000 : ℝ)*X 1 2+(4148900937/10000000000 : ℝ)*X 2 0+(2706712543/5000000000 : ℝ)*X 2 1+(126170007/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51397699286854298836377/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (598899/2500000000000 : ℝ)*(base1) + (425898539/100000000000000 : ℝ)*(base19) + (105552289/25000000000000 : ℝ)*(base23) + (60521061/100000000000000 : ℝ)*(upper3) + (9592349/20000000000000 : ℝ)*(upper5) + (690775068899417/100000000000000 : ℝ)*(major0) + (690775068899417/100000000000000 : ℝ)*(major1) + (690775068899417/100000000000000 : ℝ)*(major2) + (480912660296321/50000000000000 : ℝ)*(sp0) + (961826347190377/100000000000000 : ℝ)*(sp1) + (12022829385997/1250000000000 : ℝ)*(sp2) + (419722603810161/100000000000000 : ℝ)*(sp3) + (295290447/20000000000000 : ℝ)*(sp4) + (26736541/4000000000000 : ℝ)*(sp7) + (209861648089823/50000000000000 : ℝ)*(f.failure) + (240456693272229/25000000000000 : ℝ)*(f.sum) + (74420322184847/50000000000000000000000000000 : ℝ)*base66 + (1376704033634847/100000000000000000000000000000 : ℝ)*base68 + (309688539234847/100000000000000000000000000000 : ℝ)*base70 + (615361202234847/100000000000000000000000000000 : ℝ)*base72 + (343841917434847/50000000000000000000000000000 : ℝ)*base74 + (85129252534847/100000000000000000000000000000 : ℝ)*base76 + (427845062434847/100000000000000000000000000000 : ℝ)*base78 + (785047470634847/100000000000000000000000000000 : ℝ)*base80 + (54414254134847/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (18476643/2500000000000000000000 : ℝ)*base89 + (18476643/2500000000000000000000 : ℝ)*base91 + (18476643/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32299771373520249817473/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50235867/10000000000000 : ℝ)*(base19) + (599915693/100000000000000 : ℝ)*(base23) + (13032039/12500000000000 : ℝ)*(base39) + (66365449/100000000000000 : ℝ)*(upper3) + (121581089/100000000000000 : ℝ)*(upper5) + (182122490219459/25000000000000 : ℝ)*(major0) + (182122490219459/25000000000000 : ℝ)*(major1) + (182122464155381/25000000000000 : ℝ)*(major2) + (361767159/25000000000000 : ℝ)*(sp1) + (236997/15625000000 : ℝ)*(sp2) + (507170205073251/50000000000000 : ℝ)*(sp4) + (253584615179799/25000000000000 : ℝ)*(sp5) + (12679229971329/1250000000000 : ℝ)*(sp6) + (44263932122013/10000000000000 : ℝ)*(sp7) + (44263932122013/10000000000000 : ℝ)*(f.failure) + (507170257201407/50000000000000 : ℝ)*(f.sum) + (811070002961/625000000000000000000000000 : ℝ)*base66 + (1410404734371/25000000000000000000000000000 : ℝ)*base68 + (177169960534069/25000000000000000000000000000 : ℝ)*base70 + (27091583215629/25000000000000000000000000000 : ℝ)*base71 + (1787527180461/625000000000000000000000000 : ℝ)*base74 + (62010311634069/25000000000000000000000000000 : ℝ)*base76 + (115639133465931/25000000000000000000000000000 : ℝ)*base77 + (164766373215931/25000000000000000000000000000 : ℝ)*base79 + (57058264659069/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1363433/500000000000000000000 : ℝ)*base89 + (1363433/500000000000000000000 : ℝ)*base91 + (1363433/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1527_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3019/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25291/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1527_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1527_s1_0 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56867547/312500000 : ℝ)*x 0 + (278036461/500000000 : ℝ)*x 1 + (2553014821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56867547/312500000 : ℝ)^4551 ≤ (5548086228441/50000000000000 : ℝ)^3527 := by
    have hnat : (56867547 : ℕ)^4551*50000000000000^3527 ≤ 5548086228441^3527*312500000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56867547 312500000 5548086228441 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278036461/500000000 : ℝ)^4551 ≤ (23447978765859/50000000000000 : ℝ)^3527 := by
    have hnat : (278036461 : ℕ)^4551*50000000000000^3527 ≤ 23447978765859^3527*500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278036461 500000000 23447978765859 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2553014821/5000000000 : ℝ)^4551 ≤ (4200787000339/10000000000000 : ℝ)^3527 := by
    have hnat : (2553014821 : ℕ)^4551*10000000000000^3527 ≤ 4200787000339^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553014821 5000000000 4200787000339 10000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56867547/312500000 : ℝ), (278036461/500000000 : ℝ), (2553014821/5000000000 : ℝ)] ![(5548086228441/50000000000000 : ℝ), (23447978765859/50000000000000 : ℝ), (4200787000339/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56867547/312500000 : ℝ)|^4551 ≤ (5548086228441/50000000000000 : ℝ)^3527
        have hw : |(-56867547/312500000 : ℝ)|=(56867547/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278036461/500000000 : ℝ)|^4551 ≤ (23447978765859/50000000000000 : ℝ)^3527
        have hw : |(278036461/500000000 : ℝ)|=(278036461/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2553014821/5000000000 : ℝ)|^4551 ≤ (4200787000339/10000000000000 : ℝ)^3527
        have hw : |(2553014821/5000000000 : ℝ)|=(2553014821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_1 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383914173/10000000000 : ℝ)*x 0 + (-8235007/40000000 : ℝ)*x 1 + (5106028321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383914173/10000000000 : ℝ)^4551 ≤ (8996164307881/20000000000000 : ℝ)^3527 := by
    have hnat : (5383914173 : ℕ)^4551*20000000000000^3527 ≤ 8996164307881^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383914173 10000000000 8996164307881 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8235007/40000000 : ℝ)^4551 ≤ (13011322457681/100000000000000 : ℝ)^3527 := by
    have hnat : (8235007 : ℕ)^4551*100000000000000^3527 ≤ 13011322457681^3527*40000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8235007 40000000 13011322457681 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5106028321/10000000000 : ℝ)^4551 ≤ (42007855980049/100000000000000 : ℝ)^3527 := by
    have hnat : (5106028321 : ℕ)^4551*100000000000000^3527 ≤ 42007855980049^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106028321 10000000000 42007855980049 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383914173/10000000000 : ℝ), (-8235007/40000000 : ℝ), (5106028321/10000000000 : ℝ)] ![(8996164307881/20000000000000 : ℝ), (13011322457681/100000000000000 : ℝ), (42007855980049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383914173/10000000000 : ℝ)|^4551 ≤ (8996164307881/20000000000000 : ℝ)^3527
        have hw : |(5383914173/10000000000 : ℝ)|=(5383914173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8235007/40000000 : ℝ)|^4551 ≤ (13011322457681/100000000000000 : ℝ)^3527
        have hw : |(-8235007/40000000 : ℝ)|=(8235007/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5106028321/10000000000 : ℝ)|^4551 ≤ (42007855980049/100000000000000 : ℝ)^3527
        have hw : |(5106028321/10000000000 : ℝ)|=(5106028321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_2 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345978307/2500000000 : ℝ)*x 0 + (510602961/1000000000 : ℝ)*x 1 + (-1029375661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345978307/2500000000 : ℝ)^4551 ≤ (44980811352027/100000000000000 : ℝ)^3527 := by
    have hnat : (1345978307 : ℕ)^4551*100000000000000^3527 ≤ 44980811352027^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345978307 2500000000 44980811352027 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510602961/1000000000 : ℝ)^4551 ≤ (5250983707961/12500000000000 : ℝ)^3527 := by
    have hnat : (510602961 : ℕ)^4551*12500000000000^3527 ≤ 5250983707961^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510602961 1000000000 5250983707961 12500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029375661/5000000000 : ℝ)^4551 ≤ (6505659483691/50000000000000 : ℝ)^3527 := by
    have hnat : (1029375661 : ℕ)^4551*50000000000000^3527 ≤ 6505659483691^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029375661 5000000000 6505659483691 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345978307/2500000000 : ℝ), (510602961/1000000000 : ℝ), (-1029375661/5000000000 : ℝ)] ![(44980811352027/100000000000000 : ℝ), (5250983707961/12500000000000 : ℝ), (6505659483691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345978307/2500000000 : ℝ)|^4551 ≤ (44980811352027/100000000000000 : ℝ)^3527
        have hw : |(1345978307/2500000000 : ℝ)|=(1345978307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(510602961/1000000000 : ℝ)|^4551 ≤ (5250983707961/12500000000000 : ℝ)^3527
        have hw : |(510602961/1000000000 : ℝ)|=(510602961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1029375661/5000000000 : ℝ)|^4551 ≤ (6505659483691/50000000000000 : ℝ)^3527
        have hw : |(-1029375661/5000000000 : ℝ)|=(1029375661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_3 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061035237/2500000000 : ℝ)*x 0 + (3749824081/10000000000 : ℝ)*x 1 + (4791803999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061035237/2500000000 : ℝ)^4551 ≤ (33092179233083/100000000000000 : ℝ)^3527 := by
    have hnat : (1061035237 : ℕ)^4551*100000000000000^3527 ≤ 33092179233083^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061035237 2500000000 33092179233083 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3749824081/10000000000 : ℝ)^4551 ≤ (14102715516921/50000000000000 : ℝ)^3527 := by
    have hnat : (3749824081 : ℕ)^4551*50000000000000^3527 ≤ 14102715516921^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749824081 10000000000 14102715516921 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791803999/10000000000 : ℝ)^4551 ≤ (19351194862381/50000000000000 : ℝ)^3527 := by
    have hnat : (4791803999 : ℕ)^4551*50000000000000^3527 ≤ 19351194862381^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791803999 10000000000 19351194862381 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061035237/2500000000 : ℝ), (3749824081/10000000000 : ℝ), (4791803999/10000000000 : ℝ)] ![(33092179233083/100000000000000 : ℝ), (14102715516921/50000000000000 : ℝ), (19351194862381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061035237/2500000000 : ℝ)|^4551 ≤ (33092179233083/100000000000000 : ℝ)^3527
        have hw : |(1061035237/2500000000 : ℝ)|=(1061035237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3749824081/10000000000 : ℝ)|^4551 ≤ (14102715516921/50000000000000 : ℝ)^3527
        have hw : |(3749824081/10000000000 : ℝ)|=(3749824081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791803999/10000000000 : ℝ)|^4551 ≤ (19351194862381/50000000000000 : ℝ)^3527
        have hw : |(4791803999/10000000000 : ℝ)|=(4791803999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_4 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-910018087/5000000000 : ℝ)*x 0 + (319438017/625000000 : ℝ)*x 1 + (1388918107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910018087/5000000000 : ℝ)^4551 ≤ (5549166793319/50000000000000 : ℝ)^3527 := by
    have hnat : (910018087 : ℕ)^4551*50000000000000^3527 ≤ 5549166793319^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910018087 5000000000 5549166793319 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319438017/625000000 : ℝ)^4551 ≤ (21030364566667/50000000000000 : ℝ)^3527 := by
    have hnat : (319438017 : ℕ)^4551*50000000000000^3527 ≤ 21030364566667^3527*625000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319438017 625000000 21030364566667 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1388918107/2500000000 : ℝ)^4551 ≤ (46840937253919/100000000000000 : ℝ)^3527 := by
    have hnat : (1388918107 : ℕ)^4551*100000000000000^3527 ≤ 46840937253919^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388918107 2500000000 46840937253919 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-910018087/5000000000 : ℝ), (319438017/625000000 : ℝ), (1388918107/2500000000 : ℝ)] ![(5549166793319/50000000000000 : ℝ), (21030364566667/50000000000000 : ℝ), (46840937253919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-910018087/5000000000 : ℝ)|^4551 ≤ (5549166793319/50000000000000 : ℝ)^3527
        have hw : |(-910018087/5000000000 : ℝ)|=(910018087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319438017/625000000 : ℝ)|^4551 ≤ (21030364566667/50000000000000 : ℝ)^3527
        have hw : |(319438017/625000000 : ℝ)|=(319438017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1388918107/2500000000 : ℝ)|^4551 ≤ (46840937253919/100000000000000 : ℝ)^3527
        have hw : |(1388918107/2500000000 : ℝ)|=(1388918107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_5 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526393699/1000000000 : ℝ)*x 0 + (-1609108191/10000000000 : ℝ)*x 1 + (5555672569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526393699/1000000000 : ℝ)^4551 ≤ (43691638450369/100000000000000 : ℝ)^3527 := by
    have hnat : (526393699 : ℕ)^4551*100000000000000^3527 ≤ 43691638450369^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526393699 1000000000 43691638450369 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1609108191/10000000000 : ℝ)^4551 ≤ (9467422745503/100000000000000 : ℝ)^3527 := by
    have hnat : (1609108191 : ℕ)^4551*100000000000000^3527 ≤ 9467422745503^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609108191 10000000000 9467422745503 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5555672569/10000000000 : ℝ)^4551 ≤ (23420469393931/50000000000000 : ℝ)^3527 := by
    have hnat : (5555672569 : ℕ)^4551*50000000000000^3527 ≤ 23420469393931^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5555672569 10000000000 23420469393931 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526393699/1000000000 : ℝ), (-1609108191/10000000000 : ℝ), (5555672569/10000000000 : ℝ)] ![(43691638450369/100000000000000 : ℝ), (9467422745503/100000000000000 : ℝ), (23420469393931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526393699/1000000000 : ℝ)|^4551 ≤ (43691638450369/100000000000000 : ℝ)^3527
        have hw : |(526393699/1000000000 : ℝ)|=(526393699/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1609108191/10000000000 : ℝ)|^4551 ≤ (9467422745503/100000000000000 : ℝ)^3527
        have hw : |(-1609108191/10000000000 : ℝ)|=(1609108191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5555672569/10000000000 : ℝ)|^4551 ≤ (23420469393931/50000000000000 : ℝ)^3527
        have hw : |(5555672569/10000000000 : ℝ)|=(5555672569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_6 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263936749/10000000000 : ℝ)*x 0 + (1111134543/2000000000 : ℝ)*x 1 + (-1609108323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263936749/10000000000 : ℝ)^4551 ≤ (21845817934631/50000000000000 : ℝ)^3527 := by
    have hnat : (5263936749 : ℕ)^4551*50000000000000^3527 ≤ 21845817934631^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263936749 10000000000 21845817934631 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111134543/2000000000 : ℝ)^4551 ≤ (46840940376201/100000000000000 : ℝ)^3527 := by
    have hnat : (1111134543 : ℕ)^4551*100000000000000^3527 ≤ 46840940376201^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111134543 2000000000 46840940376201 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1609108323/10000000000 : ℝ)^4551 ≤ (2366855936907/25000000000000 : ℝ)^3527 := by
    have hnat : (1609108323 : ℕ)^4551*25000000000000^3527 ≤ 2366855936907^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609108323 10000000000 2366855936907 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263936749/10000000000 : ℝ), (1111134543/2000000000 : ℝ), (-1609108323/10000000000 : ℝ)] ![(21845817934631/50000000000000 : ℝ), (46840940376201/100000000000000 : ℝ), (2366855936907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263936749/10000000000 : ℝ)|^4551 ≤ (21845817934631/50000000000000 : ℝ)^3527
        have hw : |(5263936749/10000000000 : ℝ)|=(5263936749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111134543/2000000000 : ℝ)|^4551 ≤ (46840940376201/100000000000000 : ℝ)^3527
        have hw : |(1111134543/2000000000 : ℝ)|=(1111134543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1609108323/10000000000 : ℝ)|^4551 ≤ (2366855936907/25000000000000 : ℝ)^3527
        have hw : |(-1609108323/10000000000 : ℝ)|=(1609108323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s1_7 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244770003/10000000000 : ℝ)*x 0 + (149387343/312500000 : ℝ)*x 1 + (3761413377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244770003/10000000000 : ℝ)^4551 ≤ (16549254115173/50000000000000 : ℝ)^3527 := by
    have hnat : (4244770003 : ℕ)^4551*50000000000000^3527 ≤ 16549254115173^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244770003 10000000000 16549254115173 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149387343/312500000 : ℝ)^4551 ≤ (38583529006297/100000000000000 : ℝ)^3527 := by
    have hnat : (149387343 : ℕ)^4551*100000000000000^3527 ≤ 38583529006297^3527*312500000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149387343 312500000 38583529006297 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3761413377/10000000000 : ℝ)^4551 ≤ (28317962749449/100000000000000 : ℝ)^3527 := by
    have hnat : (3761413377 : ℕ)^4551*100000000000000^3527 ≤ 28317962749449^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761413377 10000000000 28317962749449 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244770003/10000000000 : ℝ), (149387343/312500000 : ℝ), (3761413377/10000000000 : ℝ)] ![(16549254115173/50000000000000 : ℝ), (38583529006297/100000000000000 : ℝ), (28317962749449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244770003/10000000000 : ℝ)|^4551 ≤ (16549254115173/50000000000000 : ℝ)^3527
        have hw : |(4244770003/10000000000 : ℝ)|=(4244770003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(149387343/312500000 : ℝ)|^4551 ≤ (38583529006297/100000000000000 : ℝ)^3527
        have hw : |(149387343/312500000 : ℝ)|=(149387343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3761413377/10000000000 : ℝ)|^4551 ≤ (28317962749449/100000000000000 : ℝ)^3527
        have hw : |(3761413377/10000000000 : ℝ)|=(3761413377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1527_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8553/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18173/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25291/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3019/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25291/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3019/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25291/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3019/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3019/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (17659159152813/100000000000000000000 : ℝ) := by
    have hpowers : (3019/100000 : ℝ)^4549 ≤ (17659159152813/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3019 : ℕ)^4549*100000000000000000000^1024 ≤ 17659159152813^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3019 100000 17659159152813 100000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3019/100000 : ℝ)) (X := (17659159152813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25291/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (222713440476169479/100000000000000000000 : ℝ) := by
    have hpowers : (25291/100000 : ℝ)^4549 ≤ (222713440476169479/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25291 : ℕ)^4549*100000000000000000000^1024 ≤ 222713440476169479^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25291 100000 222713440476169479 100000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25291/100000 : ℝ)) (X := (222713440476169479/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000017659159152813/50000000000000000000 : ℝ) ≤ (5000000397515421/5000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (50000017659159152813/50000000000000000000 : ℝ)^1024 ≤ (5000000397515421/5000000000000000 : ℝ)^4549 := by
      have hnat : (50000017659159152813 : ℕ)^1024*5000000000000000^4549 ≤ 5000000397515421^4549*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000017659159152813 50000000000000000000 5000000397515421 5000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000397515421/5000000000000000 : ℝ)) (X := (50000017659159152813/50000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25055682774908830573/25000000000000000000 : ℝ) ≤ (500250472721953/500000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (25055682774908830573/25000000000000000000 : ℝ)^1024 ≤ (500250472721953/500000000000000 : ℝ)^4549 := by
      have hnat : (25055682774908830573 : ℕ)^1024*500000000000000^4549 ≤ 500250472721953^4549*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25055682774908830573 25000000000000000000 500250472721953 500000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500250472721953/500000000000000 : ℝ)) (X := (25055682774908830573/25000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50222713440476169479/50000000000000000000 : ℝ) ≤ (5005009056923639/5000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (50222713440476169479/50000000000000000000 : ℝ)^1024 ≤ (5005009056923639/5000000000000000 : ℝ)^4549 := by
      have hnat : (50222713440476169479 : ℕ)^1024*5000000000000000^4549 ≤ 5005009056923639^4549*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50222713440476169479 50000000000000000000 5005009056923639 5000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005009056923639/5000000000000000 : ℝ)) (X := (50222713440476169479/50000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17659159152813/100000000000000000000 : ℝ) ≤ ((11134488771071004637/11136000000000000000 : ℝ)+2*(2504329704109/1113600000000000 : ℝ)*(3019/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (11134488771071004637/11136000000000000000 : ℝ)+2*(2504329704109/1113600000000000 : ℝ)*(3019/100000 : ℝ)=(5000000397515421/5000000000000000 : ℝ) by norm_num, show 1+2*(17659159152813/100000000000000000000 : ℝ)=(50000017659159152813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(222713440476169479/100000000000000000000 : ℝ)+(17659159152813/100000000000000000000 : ℝ) ≤ ((11134488771071004637/11136000000000000000 : ℝ)+(2504329704109/1113600000000000 : ℝ)*((25291/100000 : ℝ)+(3019/100000 : ℝ)))^(4549/1024 : ℝ) := by
    rw [show (11134488771071004637/11136000000000000000 : ℝ)+(2504329704109/1113600000000000 : ℝ)*((25291/100000 : ℝ)+(3019/100000 : ℝ))=(500250472721953/500000000000000 : ℝ) by norm_num, show 1+(222713440476169479/100000000000000000000 : ℝ)+(17659159152813/100000000000000000000 : ℝ)=(25055682774908830573/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(222713440476169479/100000000000000000000 : ℝ) ≤ ((11134488771071004637/11136000000000000000 : ℝ)+2*(2504329704109/1113600000000000 : ℝ)*(25291/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (11134488771071004637/11136000000000000000 : ℝ)+2*(2504329704109/1113600000000000 : ℝ)*(25291/100000 : ℝ)=(5005009056923639/5000000000000000 : ℝ) by norm_num, show 1+2*(222713440476169479/100000000000000000000 : ℝ)=(50222713440476169479/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11134488771071004637/11136000000000000000 : ℝ)*(X 1 0+X 2 0)+(2504329704109/1113600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (3019/100000 : ℝ)) (hi := (25291/100000 : ℝ)) (c := (11134488771071004637/11136000000000000000 : ℝ)) (alpha := (2504329704109/1113600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11134488771071004637/11136000000000000000 : ℝ)*(X 0 1+X 2 1)+(2504329704109/1113600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (3019/100000 : ℝ)) (hi := (25291/100000 : ℝ)) (c := (11134488771071004637/11136000000000000000 : ℝ)) (alpha := (2504329704109/1113600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11134488771071004637/11136000000000000000 : ℝ)*(X 0 2+X 1 2)+(2504329704109/1113600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (3019/100000 : ℝ)) (hi := (25291/100000 : ℝ)) (c := (11134488771071004637/11136000000000000000 : ℝ)) (alpha := (2504329704109/1113600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-56867547/312500000 : ℝ)*X 0 0+(278036461/500000000 : ℝ)*X 0 1+(2553014821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5383914173/10000000000 : ℝ)*X 1 0+(-8235007/40000000 : ℝ)*X 1 1+(5106028321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1345978307/2500000000 : ℝ)*X 2 0+(510602961/1000000000 : ℝ)*X 2 1+(-1029375661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061035237/2500000000 : ℝ)*X 0 0+(3749824081/10000000000 : ℝ)*X 0 1+(4791803999/10000000000 : ℝ)*X 0 2+(1061035237/2500000000 : ℝ)*X 1 0+(3749824081/10000000000 : ℝ)*X 1 1+(4791803999/10000000000 : ℝ)*X 1 2+(1061035237/2500000000 : ℝ)*X 2 0+(3749824081/10000000000 : ℝ)*X 2 1+(4791803999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-910018087/5000000000 : ℝ)*X 0 0+(319438017/625000000 : ℝ)*X 0 1+(1388918107/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((526393699/1000000000 : ℝ)*X 1 0+(-1609108191/10000000000 : ℝ)*X 1 1+(5555672569/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263936749/10000000000 : ℝ)*X 2 0+(1111134543/2000000000 : ℝ)*X 2 1+(-1609108323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244770003/10000000000 : ℝ)*X 0 0+(149387343/312500000 : ℝ)*X 0 1+(3761413377/10000000000 : ℝ)*X 0 2+(4244770003/10000000000 : ℝ)*X 1 0+(149387343/312500000 : ℝ)*X 1 1+(3761413377/10000000000 : ℝ)*X 1 2+(4244770003/10000000000 : ℝ)*X 2 0+(149387343/312500000 : ℝ)*X 2 1+(3761413377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222287575185302857280307123/46400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142073017/100000000000000 : ℝ)*(base1) + (1660691943/100000000000000 : ℝ)*(base19) + (1274670109/100000000000000 : ℝ)*(base23) + (15234869/20000000000000 : ℝ)*(upper3) + (55593413/25000000000000 : ℝ)*(upper5) + (789747462163479/50000000000000 : ℝ)*(major0) + (789747462163479/50000000000000 : ℝ)*(major1) + (789747462163479/50000000000000 : ℝ)*(major2) + (1099630641509467/50000000000000 : ℝ)*(sp0) + (439853557357071/20000000000000 : ℝ)*(sp1) + (2199268172807189/100000000000000 : ℝ)*(sp2) + (959716336577763/100000000000000 : ℝ)*(sp3) + (8306531381/100000000000000 : ℝ)*(sp4) + (1881418243/50000000000000 : ℝ)*(sp7) + (191944048297453/20000000000000 : ℝ)*(f.failure) + (1099634723738649/50000000000000 : ℝ)*(f.sum) + (3577886966823/9280000000000000000000000000 : ℝ)*base66 + (410572051114545959/185600000000000000000000000000000 : ℝ)*base68 + (269870900496945959/185600000000000000000000000000000 : ℝ)*base70 + (577252905092145959/185600000000000000000000000000000 : ℝ)*base72 + (30655957521817/9280000000000000000000000000 : ℝ)*base73 + (66374261032654041/185600000000000000000000000000000 : ℝ)*base75 + (550760301143345959/185600000000000000000000000000000 : ℝ)*base78 + (7677357751345959/185600000000000000000000000000000 : ℝ)*base80 + (27989723394457/9280000000000000000000000000 : ℝ)*base81 + (651527/1000000000000000000000 : ℝ)*base90 + (651527/1000000000000000000000 : ℝ)*base92 + (651527/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96632869239995327155037653/46400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208643949/50000000000000 : ℝ)*(base19) + (48373171/12500000000000 : ℝ)*(base23) + (58942373/100000000000000 : ℝ)*(upper3) + (34538717/100000000000000 : ℝ)*(lower4) + (1615129587548677/100000000000000 : ℝ)*(major0) + (1615129587548677/100000000000000 : ℝ)*(major1) + (807564793774339/50000000000000 : ℝ)*(major2) + (1759428003/50000000000000 : ℝ)*(sp1) + (3827969331/100000000000000 : ℝ)*(sp2) + (9941259/10000000000000 : ℝ)*(sp3) + (562221702832663/25000000000000 : ℝ)*(sp4) + (562220718796687/25000000000000 : ℝ)*(sp5) + (2248882596375953/100000000000000 : ℝ)*(sp6) + (490686097466969/50000000000000 : ℝ)*(sp7) + (30667884198329/3125000000000 : ℝ)*(f.failure) + (562221702832663/25000000000000 : ℝ)*(f.sum) + (54268614425249/7424000000000000000000000000 : ℝ)*base65 + (1328913303916654917/371200000000000000000000000000000 : ℝ)*base68 + (1491711234481324981/185600000000000000000000000000000 : ℝ)*base69 + (590540849900654917/371200000000000000000000000000000 : ℝ)*base72 + (26414358682273/7424000000000000000000000000 : ℝ)*base73 + (1590970396222124981/185600000000000000000000000000000 : ℝ)*base75 + (3312526794058254751/1113600000000000000000000000000000 : ℝ)*base78 + (9048551421360654751/1113600000000000000000000000000000 : ℝ)*base80 + (232231160416993/55680000000000000000000000000 : ℝ)*base81 + (1101311/156250000000000000000 : ℝ)*base90 + (1101311/156250000000000000000 : ℝ)*base92 + (2663811/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1527_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25291/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3019/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8553/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18173/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1527_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1527_s2_0 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1842607049/10000000000 : ℝ)*x 0 + (1090653289/2000000000 : ℝ)*x 1 + (5198670853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1842607049/10000000000 : ℝ)^4551 ≤ (11276246054697/100000000000000 : ℝ)^3527 := by
    have hnat : (1842607049 : ℕ)^4551*100000000000000^3527 ≤ 11276246054697^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842607049 10000000000 11276246054697 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090653289/2000000000 : ℝ)^4551 ≤ (45729853265169/100000000000000 : ℝ)^3527 := by
    have hnat : (1090653289 : ℕ)^4551*100000000000000^3527 ≤ 45729853265169^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090653289 2000000000 45729853265169 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198670853/10000000000 : ℝ)^4551 ≤ (42993900660587/100000000000000 : ℝ)^3527 := by
    have hnat : (5198670853 : ℕ)^4551*100000000000000^3527 ≤ 42993900660587^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198670853 10000000000 42993900660587 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1842607049/10000000000 : ℝ), (1090653289/2000000000 : ℝ), (5198670853/10000000000 : ℝ)] ![(11276246054697/100000000000000 : ℝ), (45729853265169/100000000000000 : ℝ), (42993900660587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1842607049/10000000000 : ℝ)|^4551 ≤ (11276246054697/100000000000000 : ℝ)^3527
        have hw : |(-1842607049/10000000000 : ℝ)|=(1842607049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090653289/2000000000 : ℝ)|^4551 ≤ (45729853265169/100000000000000 : ℝ)^3527
        have hw : |(1090653289/2000000000 : ℝ)|=(1090653289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198670853/10000000000 : ℝ)|^4551 ≤ (42993900660587/100000000000000 : ℝ)^3527
        have hw : |(5198670853/10000000000 : ℝ)|=(5198670853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_1 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339120799/2500000000 : ℝ)*x 0 + (-15418403/78125000 : ℝ)*x 1 + (1299667751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339120799/2500000000 : ℝ)^4551 ≤ (11171331626161/25000000000000 : ℝ)^3527 := by
    have hnat : (1339120799 : ℕ)^4551*25000000000000^3527 ≤ 11171331626161^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339120799 2500000000 11171331626161 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15418403/78125000 : ℝ)^4551 ≤ (308019280291/2500000000000 : ℝ)^3527 := by
    have hnat : (15418403 : ℕ)^4551*2500000000000^3527 ≤ 308019280291^3527*78125000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15418403 78125000 308019280291 2500000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299667751/2500000000 : ℝ)^4551 ≤ (10748475567987/25000000000000 : ℝ)^3527 := by
    have hnat : (1299667751 : ℕ)^4551*25000000000000^3527 ≤ 10748475567987^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299667751 2500000000 10748475567987 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339120799/2500000000 : ℝ), (-15418403/78125000 : ℝ), (1299667751/2500000000 : ℝ)] ![(11171331626161/25000000000000 : ℝ), (308019280291/2500000000000 : ℝ), (10748475567987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339120799/2500000000 : ℝ)|^4551 ≤ (11171331626161/25000000000000 : ℝ)^3527
        have hw : |(1339120799/2500000000 : ℝ)|=(1339120799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15418403/78125000 : ℝ)|^4551 ≤ (308019280291/2500000000000 : ℝ)^3527
        have hw : |(-15418403/78125000 : ℝ)|=(15418403/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299667751/2500000000 : ℝ)|^4551 ≤ (10748475567987/25000000000000 : ℝ)^3527
        have hw : |(1299667751/2500000000 : ℝ)|=(1299667751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_2 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071296593/2000000000 : ℝ)*x 0 + (1039734217/2000000000 : ℝ)*x 1 + (-394711157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071296593/2000000000 : ℝ)^4551 ≤ (44685324018087/100000000000000 : ℝ)^3527 := by
    have hnat : (1071296593 : ℕ)^4551*100000000000000^3527 ≤ 44685324018087^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071296593 2000000000 44685324018087 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039734217/2000000000 : ℝ)^4551 ≤ (42993903136321/100000000000000 : ℝ)^3527 := by
    have hnat : (1039734217 : ℕ)^4551*100000000000000^3527 ≤ 42993903136321^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039734217 2000000000 42993903136321 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394711157/2000000000 : ℝ)^4551 ≤ (6160386415393/50000000000000 : ℝ)^3527 := by
    have hnat : (394711157 : ℕ)^4551*50000000000000^3527 ≤ 6160386415393^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394711157 2000000000 6160386415393 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071296593/2000000000 : ℝ), (1039734217/2000000000 : ℝ), (-394711157/2000000000 : ℝ)] ![(44685324018087/100000000000000 : ℝ), (42993903136321/100000000000000 : ℝ), (6160386415393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071296593/2000000000 : ℝ)|^4551 ≤ (44685324018087/100000000000000 : ℝ)^3527
        have hw : |(1071296593/2000000000 : ℝ)|=(1071296593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039734217/2000000000 : ℝ)|^4551 ≤ (42993903136321/100000000000000 : ℝ)^3527
        have hw : |(1039734217/2000000000 : ℝ)|=(1039734217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394711157/2000000000 : ℝ)|^4551 ≤ (6160386415393/50000000000000 : ℝ)^3527
        have hw : |(-394711157/2000000000 : ℝ)|=(394711157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_3 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260582047/10000000000 : ℝ)*x 0 + (3977237713/10000000000 : ℝ)*x 1 + (2280330099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260582047/10000000000 : ℝ)^4551 ≤ (8314421115823/25000000000000 : ℝ)^3527 := by
    have hnat : (4260582047 : ℕ)^4551*25000000000000^3527 ≤ 8314421115823^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260582047 10000000000 8314421115823 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3977237713/10000000000 : ℝ)^4551 ≤ (30431780902623/100000000000000 : ℝ)^3527 := by
    have hnat : (3977237713 : ℕ)^4551*100000000000000^3527 ≤ 30431780902623^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977237713 10000000000 30431780902623 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280330099/5000000000 : ℝ)^4551 ≤ (36310534613543/100000000000000 : ℝ)^3527 := by
    have hnat : (2280330099 : ℕ)^4551*100000000000000^3527 ≤ 36310534613543^3527*5000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280330099 5000000000 36310534613543 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260582047/10000000000 : ℝ), (3977237713/10000000000 : ℝ), (2280330099/5000000000 : ℝ)] ![(8314421115823/25000000000000 : ℝ), (30431780902623/100000000000000 : ℝ), (36310534613543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260582047/10000000000 : ℝ)|^4551 ≤ (8314421115823/25000000000000 : ℝ)^3527
        have hw : |(4260582047/10000000000 : ℝ)|=(4260582047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3977237713/10000000000 : ℝ)|^4551 ≤ (30431780902623/100000000000000 : ℝ)^3527
        have hw : |(3977237713/10000000000 : ℝ)|=(3977237713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280330099/5000000000 : ℝ)|^4551 ≤ (36310534613543/100000000000000 : ℝ)^3527
        have hw : |(2280330099/5000000000 : ℝ)|=(2280330099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_4 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1842654537/10000000000 : ℝ)*x 0 + (1040048303/2000000000 : ℝ)*x 1 + (1090336529/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1842654537/10000000000 : ℝ)^4551 ≤ (5638310521921/50000000000000 : ℝ)^3527 := by
    have hnat : (1842654537 : ℕ)^4551*50000000000000^3527 ≤ 5638310521921^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842654537 10000000000 5638310521921 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040048303/2000000000 : ℝ)^4551 ≤ (43010662346001/100000000000000 : ℝ)^3527 := by
    have hnat : (1040048303 : ℕ)^4551*100000000000000^3527 ≤ 43010662346001^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040048303 2000000000 43010662346001 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1090336529/2000000000 : ℝ)^4551 ≤ (22856358296417/50000000000000 : ℝ)^3527 := by
    have hnat : (1090336529 : ℕ)^4551*50000000000000^3527 ≤ 22856358296417^3527*2000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090336529 2000000000 22856358296417 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1842654537/10000000000 : ℝ), (1040048303/2000000000 : ℝ), (1090336529/2000000000 : ℝ)] ![(5638310521921/50000000000000 : ℝ), (43010662346001/100000000000000 : ℝ), (22856358296417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1842654537/10000000000 : ℝ)|^4551 ≤ (5638310521921/50000000000000 : ℝ)^3527
        have hw : |(-1842654537/10000000000 : ℝ)|=(1842654537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040048303/2000000000 : ℝ)|^4551 ≤ (43010662346001/100000000000000 : ℝ)^3527
        have hw : |(1040048303/2000000000 : ℝ)|=(1040048303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1090336529/2000000000 : ℝ)|^4551 ≤ (22856358296417/50000000000000 : ℝ)^3527
        have hw : |(1090336529/2000000000 : ℝ)|=(1090336529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_5 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528948653/1000000000 : ℝ)*x 0 + (-1720544969/10000000000 : ℝ)*x 1 + (5451683813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528948653/1000000000 : ℝ)^4551 ≤ (43965466322809/100000000000000 : ℝ)^3527 := by
    have hnat : (528948653 : ℕ)^4551*100000000000000^3527 ≤ 43965466322809^3527*1000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528948653 1000000000 43965466322809 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1720544969/10000000000 : ℝ)^4551 ≤ (2580451107971/25000000000000 : ℝ)^3527 := by
    have hnat : (1720544969 : ℕ)^4551*25000000000000^3527 ≤ 2580451107971^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720544969 10000000000 2580451107971 25000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451683813/10000000000 : ℝ)^4551 ≤ (4571272923003/10000000000000 : ℝ)^3527 := by
    have hnat : (5451683813 : ℕ)^4551*10000000000000^3527 ≤ 4571272923003^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451683813 10000000000 4571272923003 10000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528948653/1000000000 : ℝ), (-1720544969/10000000000 : ℝ), (5451683813/10000000000 : ℝ)] ![(43965466322809/100000000000000 : ℝ), (2580451107971/25000000000000 : ℝ), (4571272923003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528948653/1000000000 : ℝ)|^4551 ≤ (43965466322809/100000000000000 : ℝ)^3527
        have hw : |(528948653/1000000000 : ℝ)|=(528948653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1720544969/10000000000 : ℝ)|^4551 ≤ (2580451107971/25000000000000 : ℝ)^3527
        have hw : |(-1720544969/10000000000 : ℝ)|=(1720544969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451683813/10000000000 : ℝ)|^4551 ≤ (4571272923003/10000000000000 : ℝ)^3527
        have hw : |(5451683813/10000000000 : ℝ)|=(5451683813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_6 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322371847/2500000000 : ℝ)*x 0 + (1362920939/2500000000 : ℝ)*x 1 + (-1720543859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322371847/2500000000 : ℝ)^4551 ≤ (43965475524907/100000000000000 : ℝ)^3527 := by
    have hnat : (1322371847 : ℕ)^4551*100000000000000^3527 ≤ 43965475524907^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322371847 2500000000 43965475524907 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362920939/2500000000 : ℝ)^4551 ≤ (45712728613317/100000000000000 : ℝ)^3527 := by
    have hnat : (1362920939 : ℕ)^4551*100000000000000^3527 ≤ 45712728613317^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362920939 2500000000 45712728613317 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720543859/10000000000 : ℝ)^4551 ≤ (2064359167899/20000000000000 : ℝ)^3527 := by
    have hnat : (1720543859 : ℕ)^4551*20000000000000^3527 ≤ 2064359167899^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720543859 10000000000 2064359167899 20000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322371847/2500000000 : ℝ), (1362920939/2500000000 : ℝ), (-1720543859/10000000000 : ℝ)] ![(43965475524907/100000000000000 : ℝ), (45712728613317/100000000000000 : ℝ), (2064359167899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322371847/2500000000 : ℝ)|^4551 ≤ (43965475524907/100000000000000 : ℝ)^3527
        have hw : |(1322371847/2500000000 : ℝ)|=(1322371847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362920939/2500000000 : ℝ)|^4551 ≤ (45712728613317/100000000000000 : ℝ)^3527
        have hw : |(1362920939/2500000000 : ℝ)|=(1362920939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720543859/10000000000 : ℝ)|^4551 ≤ (2064359167899/20000000000000 : ℝ)^3527
        have hw : |(-1720543859/10000000000 : ℝ)|=(1720543859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1527_s2_7 (p : ℝ) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260693539/10000000000 : ℝ)*x 0 + (4557064401/10000000000 : ℝ)*x 1 + (995216159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260693539/10000000000 : ℝ)^4551 ≤ (16629403718783/50000000000000 : ℝ)^3527 := by
    have hnat : (4260693539 : ℕ)^4551*50000000000000^3527 ≤ 16629403718783^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260693539 10000000000 16629403718783 50000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4557064401/10000000000 : ℝ)^4551 ≤ (36273598452893/100000000000000 : ℝ)^3527 := by
    have hnat : (4557064401 : ℕ)^4551*100000000000000^3527 ≤ 36273598452893^3527*10000000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4557064401 10000000000 36273598452893 100000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995216159/2500000000 : ℝ)^4551 ≤ (3046759409261/10000000000000 : ℝ)^3527 := by
    have hnat : (995216159 : ℕ)^4551*10000000000000^3527 ≤ 3046759409261^3527*2500000000^4551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995216159 2500000000 3046759409261 10000000000000 4551 3527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4551/1024 : ℝ)) 4551 3527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260693539/10000000000 : ℝ), (4557064401/10000000000 : ℝ), (995216159/2500000000 : ℝ)] ![(16629403718783/50000000000000 : ℝ), (36273598452893/100000000000000 : ℝ), (3046759409261/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260693539/10000000000 : ℝ)|^4551 ≤ (16629403718783/50000000000000 : ℝ)^3527
        have hw : |(4260693539/10000000000 : ℝ)|=(4260693539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4557064401/10000000000 : ℝ)|^4551 ≤ (36273598452893/100000000000000 : ℝ)^3527
        have hw : |(4557064401/10000000000 : ℝ)|=(4557064401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995216159/2500000000 : ℝ)|^4551 ≤ (3046759409261/10000000000000 : ℝ)^3527
        have hw : |(995216159/2500000000 : ℝ)|=(995216159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1527_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10551/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7971/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (8553/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (901636446462339/50000000000000000000 : ℝ) := by
    have hpowers : (8553/100000 : ℝ)^4549 ≤ (901636446462339/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8553 : ℕ)^4549*50000000000000000000^1024 ≤ 901636446462339^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8553 100000 901636446462339 50000000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8553/100000 : ℝ)) (X := (901636446462339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18173/100000 : ℝ) ^ (4549/1024 : ℝ) ≤ (6412089676474681/12500000000000000000 : ℝ) := by
    have hpowers : (18173/100000 : ℝ)^4549 ≤ (6412089676474681/12500000000000000000 : ℝ)^1024 := by
      have hnat : (18173 : ℕ)^4549*12500000000000000000^1024 ≤ 6412089676474681^1024*100000^4549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18173 100000 6412089676474681 12500000000000000000 4549 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18173/100000 : ℝ)) (X := (6412089676474681/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000901636446462339/25000000000000000000 : ℝ) ≤ (10000081183804799/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (25000901636446462339/25000000000000000000 : ℝ)^1024 ≤ (10000081183804799/10000000000000000 : ℝ)^4549 := by
      have hnat : (25000901636446462339 : ℕ)^1024*10000000000000000^4549 ≤ 10000081183804799^4549*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000901636446462339 25000000000000000000 10000081183804799 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000081183804799/10000000000000000 : ℝ)) (X := (25000901636446462339/25000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026549995152361063/50000000000000000000 : ℝ) ≤ (2000239011681179/2000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (50026549995152361063/50000000000000000000 : ℝ)^1024 ≤ (2000239011681179/2000000000000000 : ℝ)^4549 := by
      have hnat : (50026549995152361063 : ℕ)^1024*2000000000000000^4549 ≤ 2000239011681179^4549*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026549995152361063 50000000000000000000 2000239011681179 2000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000239011681179/2000000000000000 : ℝ)) (X := (50026549995152361063/50000000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6256412089676474681/6250000000000000000 : ℝ) ≤ (10002308933006991/10000000000000000 : ℝ) ^ (4549/1024 : ℝ) := by
    have hpowers : (6256412089676474681/6250000000000000000 : ℝ)^1024 ≤ (10002308933006991/10000000000000000 : ℝ)^4549 := by
      have hnat : (6256412089676474681 : ℕ)^1024*10000000000000000^4549 ≤ 10002308933006991^4549*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6256412089676474681 6250000000000000000 10002308933006991 10000000000000000 1024 4549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002308933006991/10000000000000000 : ℝ)) (X := (6256412089676474681/6250000000000000000 : ℝ)) (by norm_num) 4549 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(901636446462339/50000000000000000000 : ℝ) ≤ ((24045431762318954551/24050000000000000000 : ℝ)+2*(139234325137/120250000000000 : ℝ)*(8553/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (24045431762318954551/24050000000000000000 : ℝ)+2*(139234325137/120250000000000 : ℝ)*(8553/100000 : ℝ)=(10000081183804799/10000000000000000 : ℝ) by norm_num, show 1+2*(901636446462339/50000000000000000000 : ℝ)=(25000901636446462339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6412089676474681/12500000000000000000 : ℝ)+(901636446462339/50000000000000000000 : ℝ) ≤ ((24045431762318954551/24050000000000000000 : ℝ)+(139234325137/120250000000000 : ℝ)*((18173/100000 : ℝ)+(8553/100000 : ℝ)))^(4549/1024 : ℝ) := by
    rw [show (24045431762318954551/24050000000000000000 : ℝ)+(139234325137/120250000000000 : ℝ)*((18173/100000 : ℝ)+(8553/100000 : ℝ))=(2000239011681179/2000000000000000 : ℝ) by norm_num, show 1+(6412089676474681/12500000000000000000 : ℝ)+(901636446462339/50000000000000000000 : ℝ)=(50026549995152361063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6412089676474681/12500000000000000000 : ℝ) ≤ ((24045431762318954551/24050000000000000000 : ℝ)+2*(139234325137/120250000000000 : ℝ)*(18173/100000 : ℝ))^(4549/1024 : ℝ) := by
    rw [show (24045431762318954551/24050000000000000000 : ℝ)+2*(139234325137/120250000000000 : ℝ)*(18173/100000 : ℝ)=(10002308933006991/10000000000000000 : ℝ) by norm_num, show 1+2*(6412089676474681/12500000000000000000 : ℝ)=(6256412089676474681/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24045431762318954551/24050000000000000000 : ℝ)*(X 1 0+X 2 0)+(139234325137/120250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (8553/100000 : ℝ)) (hi := (18173/100000 : ℝ)) (c := (24045431762318954551/24050000000000000000 : ℝ)) (alpha := (139234325137/120250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24045431762318954551/24050000000000000000 : ℝ)*(X 0 1+X 2 1)+(139234325137/120250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (8553/100000 : ℝ)) (hi := (18173/100000 : ℝ)) (c := (24045431762318954551/24050000000000000000 : ℝ)) (alpha := (139234325137/120250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24045431762318954551/24050000000000000000 : ℝ)*(X 0 2+X 1 2)+(139234325137/120250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4549/1024 : ℝ)) (lo := (8553/100000 : ℝ)) (hi := (18173/100000 : ℝ)) (c := (24045431762318954551/24050000000000000000 : ℝ)) (alpha := (139234325137/120250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1842607049/10000000000 : ℝ)*X 0 0+(1090653289/2000000000 : ℝ)*X 0 1+(5198670853/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339120799/2500000000 : ℝ)*X 1 0+(-15418403/78125000 : ℝ)*X 1 1+(1299667751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071296593/2000000000 : ℝ)*X 2 0+(1039734217/2000000000 : ℝ)*X 2 1+(-394711157/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260582047/10000000000 : ℝ)*X 0 0+(3977237713/10000000000 : ℝ)*X 0 1+(2280330099/5000000000 : ℝ)*X 0 2+(4260582047/10000000000 : ℝ)*X 1 0+(3977237713/10000000000 : ℝ)*X 1 1+(2280330099/5000000000 : ℝ)*X 1 2+(4260582047/10000000000 : ℝ)*X 2 0+(3977237713/10000000000 : ℝ)*X 2 1+(2280330099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1842654537/10000000000 : ℝ)*X 0 0+(1040048303/2000000000 : ℝ)*X 0 1+(1090336529/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528948653/1000000000 : ℝ)*X 1 0+(-1720544969/10000000000 : ℝ)*X 1 1+(5451683813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322371847/2500000000 : ℝ)*X 2 0+(1362920939/2500000000 : ℝ)*X 2 1+(-1720543859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260693539/10000000000 : ℝ)*X 0 0+(4557064401/10000000000 : ℝ)*X 0 1+(995216159/2500000000 : ℝ)*X 0 2+(4260693539/10000000000 : ℝ)*X 1 0+(4557064401/10000000000 : ℝ)*X 1 1+(995216159/2500000000 : ℝ)*X 1 2+(4260693539/10000000000 : ℝ)*X 2 0+(4557064401/10000000000 : ℝ)*X 2 1+(995216159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1527_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (557219241842071015342888323/150312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183925171/25000000000000 : ℝ)*(base19) + (608809971/100000000000000 : ℝ)*(base23) + (109393867/100000000000000 : ℝ)*(upper3) + (14430773/50000000000000 : ℝ)*(lower4) + (352615980474609/12500000000000 : ℝ)*(major0) + (352615980474609/12500000000000 : ℝ)*(major1) + (352615980474609/12500000000000 : ℝ)*(major2) + (981953416746669/25000000000000 : ℝ)*(sp0) + (3927824912956901/100000000000000 : ℝ)*(sp1) + (1963912064850063/50000000000000 : ℝ)*(sp2) + (68561062885413/4000000000000 : ℝ)*(sp3) + (1198167091/10000000000000 : ℝ)*(sp4) + (28442109/3125000000000 : ℝ)*(sp6) + (668646353/20000000000000 : ℝ)*(sp7) + (171402991536709/10000000000000 : ℝ)*(f.failure) + (1963912824328793/50000000000000 : ℝ)*(f.sum) + (2393726226217/751562500000000000000000000 : ℝ)*base66 + (1201974827632904441/300625000000000000000000000000000 : ℝ)*base68 + (1139848719725404441/300625000000000000000000000000000 : ℝ)*base70 + (542766319038345559/300625000000000000000000000000000 : ℝ)*base71 + (9878808318361/6012500000000000000000000000 : ℝ)*base74 + (26129243083345559/300625000000000000000000000000000 : ℝ)*base75 + (3069669955552095559/300625000000000000000000000000000 : ℝ)*base77 + (1531263730612095559/300625000000000000000000000000000 : ℝ)*base79 + (5856257598057/3006250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (918769/500000000000000000000 : ℝ)*base89 + (918769/500000000000000000000 : ℝ)*base91 + (918769/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6252593869814021395233/601250000000000000000000000 : ℝ) := by norm_num
    linear_combination (338946113/50000000000000 : ℝ)*(base15) + (325996279/100000000000000 : ℝ)*(lower2) + (47478327/50000000000000 : ℝ)*(upper3) + (20734777/10000000000000 : ℝ)*(lower4) + (17655949/50000000000000 : ℝ)*(upper5) + (142814829451571/5000000000000 : ℝ)*(major0) + (142814829451571/5000000000000 : ℝ)*(major1) + (142814829451571/5000000000000 : ℝ)*(major2) + (3609855409/25000000000000 : ℝ)*(sp2) + (5390917691/100000000000000 : ℝ)*(sp3) + (994268109545307/25000000000000 : ℝ)*(sp4) + (1988535880144501/50000000000000 : ℝ)*(sp5) + (497132249844949/12500000000000 : ℝ)*(sp6) + (433878750579941/25000000000000 : ℝ)*(sp7) + (347104078647491/20000000000000 : ℝ)*(f.failure) + (994268109545307/25000000000000 : ℝ)*(f.sum) + (12478206778831/2405000000000000000000000000 : ℝ)*base65 + (728405715793199621/120250000000000000000000000000000 : ℝ)*base67 + (1879363960585550379/120250000000000000000000000000000 : ℝ)*base70 + (213584337156699621/120250000000000000000000000000000 : ℝ)*base71 + (5079454504671/2405000000000000000000000000 : ℝ)*base73 + (959804582647050379/120250000000000000000000000000000 : ℝ)*base76 + (2110129653692699621/120250000000000000000000000000000 : ℝ)*base77 + (6670772794800379/120250000000000000000000000000000 : ℝ)*base80 + (110880757227/1202500000000000000000000000 : ℝ)*base82 + (5693431/1000000000000000000000 : ℝ)*base89 + (5693431/1000000000000000000000 : ℝ)*base91 + (5693431/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1527_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1527_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1527_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1527_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1527_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1527_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4549/1024 : ℝ) ≤ p) (hpb : p ≤ (4551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82289341/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7971/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1527_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

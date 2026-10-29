-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:08.272144+00:00
-- url     : https://prove2.me/submissions/fc70e248-6d4a-4bfc-9a09-85732b1171ec

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
theorem support_rectangle_w1610_box_0 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1431010147/10000000000 : ℝ)*x 0 + (541809627/1000000000 : ℝ)*x 1 + (5418096233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1431010147/10000000000 : ℝ)^4759 ≤ (4198758737907/50000000000000 : ℝ)^3735 := by
    have hnat : (1431010147 : ℕ)^4759*50000000000000^3735 ≤ 4198758737907^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1431010147 10000000000 4198758737907 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541809627/1000000000 : ℝ)^4759 ≤ (2862577591003/6250000000000 : ℝ)^3735 := by
    have hnat : (541809627 : ℕ)^4759*6250000000000^3735 ≤ 2862577591003^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541809627 1000000000 2862577591003 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418096233/10000000000 : ℝ)^4759 ≤ (22900620528761/50000000000000 : ℝ)^3735 := by
    have hnat : (5418096233 : ℕ)^4759*50000000000000^3735 ≤ 22900620528761^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418096233 10000000000 22900620528761 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1431010147/10000000000 : ℝ), (541809627/1000000000 : ℝ), (5418096233/10000000000 : ℝ)] ![(4198758737907/50000000000000 : ℝ), (2862577591003/6250000000000 : ℝ), (22900620528761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1431010147/10000000000 : ℝ)|^4759 ≤ (4198758737907/50000000000000 : ℝ)^3735
        have hw : |(-1431010147/10000000000 : ℝ)|=(1431010147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541809627/1000000000 : ℝ)|^4759 ≤ (2862577591003/6250000000000 : ℝ)^3735
        have hw : |(541809627/1000000000 : ℝ)|=(541809627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418096233/10000000000 : ℝ)|^4759 ≤ (22900620528761/50000000000000 : ℝ)^3735
        have hw : |(5418096233/10000000000 : ℝ)|=(5418096233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_1 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625580111/5000000000 : ℝ)*x 0 + (-1665395627/10000000000 : ℝ)*x 1 + (5418096233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625580111/5000000000 : ℝ)^4759 ≤ (5501353326101/12500000000000 : ℝ)^3735 := by
    have hnat : (2625580111 : ℕ)^4759*12500000000000^3735 ≤ 5501353326101^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625580111 5000000000 5501353326101 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1665395627/10000000000 : ℝ)^4759 ≤ (2037586464327/20000000000000 : ℝ)^3735 := by
    have hnat : (1665395627 : ℕ)^4759*20000000000000^3735 ≤ 2037586464327^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665395627 10000000000 2037586464327 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418096233/10000000000 : ℝ)^4759 ≤ (22900620528761/50000000000000 : ℝ)^3735 := by
    have hnat : (5418096233 : ℕ)^4759*50000000000000^3735 ≤ 22900620528761^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418096233 10000000000 22900620528761 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625580111/5000000000 : ℝ), (-1665395627/10000000000 : ℝ), (5418096233/10000000000 : ℝ)] ![(5501353326101/12500000000000 : ℝ), (2037586464327/20000000000000 : ℝ), (22900620528761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625580111/5000000000 : ℝ)|^4759 ≤ (5501353326101/12500000000000 : ℝ)^3735
        have hw : |(2625580111/5000000000 : ℝ)|=(2625580111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1665395627/10000000000 : ℝ)|^4759 ≤ (2037586464327/20000000000000 : ℝ)^3735
        have hw : |(-1665395627/10000000000 : ℝ)|=(1665395627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418096233/10000000000 : ℝ)|^4759 ≤ (22900620528761/50000000000000 : ℝ)^3735
        have hw : |(5418096233/10000000000 : ℝ)|=(5418096233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_2 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625580129/5000000000 : ℝ)*x 0 + (5418096197/10000000000 : ℝ)*x 1 + (-1665395627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625580129/5000000000 : ℝ)^4759 ≤ (44010826993251/100000000000000 : ℝ)^3735 := by
    have hnat : (2625580129 : ℕ)^4759*100000000000000^3735 ≤ 44010826993251^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625580129 5000000000 44010826993251 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418096197/10000000000 : ℝ)^4759 ≤ (22900620334883/50000000000000 : ℝ)^3735 := by
    have hnat : (5418096197 : ℕ)^4759*50000000000000^3735 ≤ 22900620334883^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418096197 10000000000 22900620334883 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1665395627/10000000000 : ℝ)^4759 ≤ (2037586464327/20000000000000 : ℝ)^3735 := by
    have hnat : (1665395627 : ℕ)^4759*20000000000000^3735 ≤ 2037586464327^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665395627 10000000000 2037586464327 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625580129/5000000000 : ℝ), (5418096197/10000000000 : ℝ), (-1665395627/10000000000 : ℝ)] ![(44010826993251/100000000000000 : ℝ), (22900620334883/50000000000000 : ℝ), (2037586464327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625580129/5000000000 : ℝ)|^4759 ≤ (44010826993251/100000000000000 : ℝ)^3735
        have hw : |(2625580129/5000000000 : ℝ)|=(2625580129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418096197/10000000000 : ℝ)|^4759 ≤ (22900620334883/50000000000000 : ℝ)^3735
        have hw : |(5418096197/10000000000 : ℝ)|=(5418096197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1665395627/10000000000 : ℝ)|^4759 ≤ (2037586464327/20000000000000 : ℝ)^3735
        have hw : |(-1665395627/10000000000 : ℝ)|=(1665395627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_3 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2246203119/5000000000 : ℝ)*x 0 + (4085356407/10000000000 : ℝ)*x 1 + (2042678203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246203119/5000000000 : ℝ)^4759 ≤ (36074599348711/100000000000000 : ℝ)^3735 := by
    have hnat : (2246203119 : ℕ)^4759*100000000000000^3735 ≤ 36074599348711^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246203119 5000000000 36074599348711 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4085356407/10000000000 : ℝ)^4759 ≤ (31962700322919/100000000000000 : ℝ)^3735 := by
    have hnat : (4085356407 : ℕ)^4759*100000000000000^3735 ≤ 31962700322919^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085356407 10000000000 31962700322919 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2042678203/5000000000 : ℝ)^4759 ≤ (639254006259/2000000000000 : ℝ)^3735 := by
    have hnat : (2042678203 : ℕ)^4759*2000000000000^3735 ≤ 639254006259^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042678203 5000000000 639254006259 2000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246203119/5000000000 : ℝ), (4085356407/10000000000 : ℝ), (2042678203/5000000000 : ℝ)] ![(36074599348711/100000000000000 : ℝ), (31962700322919/100000000000000 : ℝ), (639254006259/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246203119/5000000000 : ℝ)|^4759 ≤ (36074599348711/100000000000000 : ℝ)^3735
        have hw : |(2246203119/5000000000 : ℝ)|=(2246203119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4085356407/10000000000 : ℝ)|^4759 ≤ (31962700322919/100000000000000 : ℝ)^3735
        have hw : |(4085356407/10000000000 : ℝ)|=(4085356407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2042678203/5000000000 : ℝ)|^4759 ≤ (639254006259/2000000000000 : ℝ)^3735
        have hw : |(2042678203/5000000000 : ℝ)|=(2042678203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_4 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-198831767/1000000000 : ℝ)*x 0 + (2607053037/5000000000 : ℝ)*x 1 + (1303526457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198831767/1000000000 : ℝ)^4759 ≤ (638449140559/5000000000000 : ℝ)^3735 := by
    have hnat : (198831767 : ℕ)^4759*5000000000000^3735 ≤ 638449140559^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198831767 1000000000 638449140559 5000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607053037/5000000000 : ℝ)^4759 ≤ (43615509900699/100000000000000 : ℝ)^3735 := by
    have hnat : (2607053037 : ℕ)^4759*100000000000000^3735 ≤ 43615509900699^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607053037 5000000000 43615509900699 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303526457/2500000000 : ℝ)^4759 ≤ (2725969204923/6250000000000 : ℝ)^3735 := by
    have hnat : (1303526457 : ℕ)^4759*6250000000000^3735 ≤ 2725969204923^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303526457 2500000000 2725969204923 6250000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198831767/1000000000 : ℝ), (2607053037/5000000000 : ℝ), (1303526457/2500000000 : ℝ)] ![(638449140559/5000000000000 : ℝ), (43615509900699/100000000000000 : ℝ), (2725969204923/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198831767/1000000000 : ℝ)|^4759 ≤ (638449140559/5000000000000 : ℝ)^3735
        have hw : |(-198831767/1000000000 : ℝ)|=(198831767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607053037/5000000000 : ℝ)|^4759 ≤ (43615509900699/100000000000000 : ℝ)^3735
        have hw : |(2607053037/5000000000 : ℝ)|=(2607053037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303526457/2500000000 : ℝ)|^4759 ≤ (2725969204923/6250000000000 : ℝ)^3735
        have hw : |(1303526457/2500000000 : ℝ)|=(1303526457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_5 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695974663/5000000000 : ℝ)*x 0 + (-1751615593/10000000000 : ℝ)*x 1 + (1042821163/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695974663/5000000000 : ℝ)^4759 ≤ (45519799503651/100000000000000 : ℝ)^3735 := by
    have hnat : (2695974663 : ℕ)^4759*100000000000000^3735 ≤ 45519799503651^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695974663 5000000000 45519799503651 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1751615593/10000000000 : ℝ)^4759 ≤ (5432346674289/50000000000000 : ℝ)^3735 := by
    have hnat : (1751615593 : ℕ)^4759*50000000000000^3735 ≤ 5432346674289^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751615593 10000000000 5432346674289 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042821163/2000000000 : ℝ)^4759 ≤ (43615507140211/100000000000000 : ℝ)^3735 := by
    have hnat : (1042821163 : ℕ)^4759*100000000000000^3735 ≤ 43615507140211^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042821163 2000000000 43615507140211 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695974663/5000000000 : ℝ), (-1751615593/10000000000 : ℝ), (1042821163/2000000000 : ℝ)] ![(45519799503651/100000000000000 : ℝ), (5432346674289/50000000000000 : ℝ), (43615507140211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695974663/5000000000 : ℝ)|^4759 ≤ (45519799503651/100000000000000 : ℝ)^3735
        have hw : |(2695974663/5000000000 : ℝ)|=(2695974663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1751615593/10000000000 : ℝ)|^4759 ≤ (5432346674289/50000000000000 : ℝ)^3735
        have hw : |(-1751615593/10000000000 : ℝ)|=(1751615593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042821163/2000000000 : ℝ)|^4759 ≤ (43615507140211/100000000000000 : ℝ)^3735
        have hw : |(1042821163/2000000000 : ℝ)|=(1042821163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_6 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168498421/312500000 : ℝ)*x 0 + (651763199/1250000000 : ℝ)*x 1 + (-875807847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168498421/312500000 : ℝ)^4759 ≤ (45519801074131/100000000000000 : ℝ)^3735 := by
    have hnat : (168498421 : ℕ)^4759*100000000000000^3735 ≤ 45519801074131^3735*312500000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168498421 312500000 45519801074131 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651763199/1250000000 : ℝ)^4759 ≤ (2180775238171/5000000000000 : ℝ)^3735 := by
    have hnat : (651763199 : ℕ)^4759*5000000000000^3735 ≤ 2180775238171^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651763199 1250000000 2180775238171 5000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875807847/5000000000 : ℝ)^4759 ≤ (10864694146803/100000000000000 : ℝ)^3735 := by
    have hnat : (875807847 : ℕ)^4759*100000000000000^3735 ≤ 10864694146803^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875807847 5000000000 10864694146803 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168498421/312500000 : ℝ), (651763199/1250000000 : ℝ), (-875807847/5000000000 : ℝ)] ![(45519801074131/100000000000000 : ℝ), (2180775238171/5000000000000 : ℝ), (10864694146803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168498421/312500000 : ℝ)|^4759 ≤ (45519801074131/100000000000000 : ℝ)^3735
        have hw : |(168498421/312500000 : ℝ)|=(168498421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651763199/1250000000 : ℝ)|^4759 ≤ (2180775238171/5000000000000 : ℝ)^3735
        have hw : |(651763199/1250000000 : ℝ)|=(651763199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-875807847/5000000000 : ℝ)|^4759 ≤ (10864694146803/100000000000000 : ℝ)^3735
        have hw : |(-875807847/5000000000 : ℝ)|=(875807847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_7 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (785364913/2000000000 : ℝ)*x 0 + (4367803897/10000000000 : ℝ)*x 1 + (2183901783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (785364913/2000000000 : ℝ)^4759 ≤ (30390830530823/100000000000000 : ℝ)^3735 := by
    have hnat : (785364913 : ℕ)^4759*100000000000000^3735 ≤ 30390830530823^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785364913 2000000000 30390830530823 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4367803897/10000000000 : ℝ)^4759 ≤ (3480458640499/10000000000000 : ℝ)^3735 := by
    have hnat : (4367803897 : ℕ)^4759*10000000000000^3735 ≤ 3480458640499^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367803897 10000000000 3480458640499 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183901783/5000000000 : ℝ)^4759 ≤ (6960916608863/20000000000000 : ℝ)^3735 := by
    have hnat : (2183901783 : ℕ)^4759*20000000000000^3735 ≤ 6960916608863^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183901783 5000000000 6960916608863 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(785364913/2000000000 : ℝ), (4367803897/10000000000 : ℝ), (2183901783/5000000000 : ℝ)] ![(30390830530823/100000000000000 : ℝ), (3480458640499/10000000000000 : ℝ), (6960916608863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(785364913/2000000000 : ℝ)|^4759 ≤ (30390830530823/100000000000000 : ℝ)^3735
        have hw : |(785364913/2000000000 : ℝ)|=(785364913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4367803897/10000000000 : ℝ)|^4759 ≤ (3480458640499/10000000000000 : ℝ)^3735
        have hw : |(4367803897/10000000000 : ℝ)|=(4367803897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2183901783/5000000000 : ℝ)|^4759 ≤ (6960916608863/20000000000000 : ℝ)^3735
        have hw : |(2183901783/5000000000 : ℝ)|=(2183901783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_8 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-934914737/5000000000 : ℝ)*x 0 + (5068399287/10000000000 : ℝ)*x 1 + (5448040229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934914737/5000000000 : ℝ)^4759 ≤ (11807469171581/100000000000000 : ℝ)^3735 := by
    have hnat : (934914737 : ℕ)^4759*100000000000000^3735 ≤ 11807469171581^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934914737 5000000000 11807469171581 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5068399287/10000000000 : ℝ)^4759 ≤ (657320613137/1562500000000 : ℝ)^3735 := by
    have hnat : (5068399287 : ℕ)^4759*1562500000000^3735 ≤ 657320613137^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5068399287 10000000000 657320613137 1562500000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448040229/10000000000 : ℝ)^4759 ≤ (4612401156611/10000000000000 : ℝ)^3735 := by
    have hnat : (5448040229 : ℕ)^4759*10000000000000^3735 ≤ 4612401156611^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448040229 10000000000 4612401156611 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-934914737/5000000000 : ℝ), (5068399287/10000000000 : ℝ), (5448040229/10000000000 : ℝ)] ![(11807469171581/100000000000000 : ℝ), (657320613137/1562500000000 : ℝ), (4612401156611/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-934914737/5000000000 : ℝ)|^4759 ≤ (11807469171581/100000000000000 : ℝ)^3735
        have hw : |(-934914737/5000000000 : ℝ)|=(934914737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5068399287/10000000000 : ℝ)|^4759 ≤ (657320613137/1562500000000 : ℝ)^3735
        have hw : |(5068399287/10000000000 : ℝ)|=(5068399287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448040229/10000000000 : ℝ)|^4759 ≤ (4612401156611/10000000000000 : ℝ)^3735
        have hw : |(5448040229/10000000000 : ℝ)|=(5448040229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_9 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26152441/50000000 : ℝ)*x 0 + (-1652276767/10000000000 : ℝ)*x 1 + (5448041319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26152441/50000000 : ℝ)^4759 ≤ (1751607598209/4000000000000 : ℝ)^3735 := by
    have hnat : (26152441 : ℕ)^4759*4000000000000^3735 ≤ 1751607598209^3735*50000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26152441 50000000 1751607598209 4000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1652276767/10000000000 : ℝ)^4759 ≤ (1260723338871/12500000000000 : ℝ)^3735 := by
    have hnat : (1652276767 : ℕ)^4759*12500000000000^3735 ≤ 1260723338871^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652276767 10000000000 1260723338871 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5448041319/10000000000 : ℝ)^4759 ≤ (46124023324243/100000000000000 : ℝ)^3735 := by
    have hnat : (5448041319 : ℕ)^4759*100000000000000^3735 ≤ 46124023324243^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448041319 10000000000 46124023324243 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26152441/50000000 : ℝ), (-1652276767/10000000000 : ℝ), (5448041319/10000000000 : ℝ)] ![(1751607598209/4000000000000 : ℝ), (1260723338871/12500000000000 : ℝ), (46124023324243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26152441/50000000 : ℝ)|^4759 ≤ (1751607598209/4000000000000 : ℝ)^3735
        have hw : |(26152441/50000000 : ℝ)|=(26152441/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1652276767/10000000000 : ℝ)|^4759 ≤ (1260723338871/12500000000000 : ℝ)^3735
        have hw : |(-1652276767/10000000000 : ℝ)|=(1652276767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5448041319/10000000000 : ℝ)|^4759 ≤ (46124023324243/100000000000000 : ℝ)^3735
        have hw : |(5448041319/10000000000 : ℝ)|=(5448041319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_10 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307622111/2500000000 : ℝ)*x 0 + (681005229/1250000000 : ℝ)*x 1 + (-41306893/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307622111/2500000000 : ℝ)^4759 ≤ (43790192558077/100000000000000 : ℝ)^3735 := by
    have hnat : (1307622111 : ℕ)^4759*100000000000000^3735 ≤ 43790192558077^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307622111 2500000000 43790192558077 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681005229/1250000000 : ℝ)^4759 ≤ (46124028858117/100000000000000 : ℝ)^3735 := by
    have hnat : (681005229 : ℕ)^4759*100000000000000^3735 ≤ 46124028858117^3735*1250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681005229 1250000000 46124028858117 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41306893/250000000 : ℝ)^4759 ≤ (100857785677/1000000000000 : ℝ)^3735 := by
    have hnat : (41306893 : ℕ)^4759*1000000000000^3735 ≤ 100857785677^3735*250000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41306893 250000000 100857785677 1000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307622111/2500000000 : ℝ), (681005229/1250000000 : ℝ), (-41306893/250000000 : ℝ)] ![(43790192558077/100000000000000 : ℝ), (46124028858117/100000000000000 : ℝ), (100857785677/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307622111/2500000000 : ℝ)|^4759 ≤ (43790192558077/100000000000000 : ℝ)^3735
        have hw : |(1307622111/2500000000 : ℝ)|=(1307622111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681005229/1250000000 : ℝ)|^4759 ≤ (46124028858117/100000000000000 : ℝ)^3735
        have hw : |(681005229/1250000000 : ℝ)|=(681005229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41306893/250000000 : ℝ)|^4759 ≤ (100857785677/1000000000000 : ℝ)^3735
        have hw : |(-41306893/250000000 : ℝ)|=(41306893/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_11 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2286517181/5000000000 : ℝ)*x 0 + (4043819983/10000000000 : ℝ)*x 1 + (1010954697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2286517181/5000000000 : ℝ)^4759 ≤ (36901582640361/100000000000000 : ℝ)^3735 := by
    have hnat : (2286517181 : ℕ)^4759*100000000000000^3735 ≤ 36901582640361^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286517181 5000000000 36901582640361 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4043819983/10000000000 : ℝ)^4759 ≤ (6309842922327/20000000000000 : ℝ)^3735 := by
    have hnat : (4043819983 : ℕ)^4759*20000000000000^3735 ≤ 6309842922327^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043819983 10000000000 6309842922327 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010954697/2500000000 : ℝ)^4759 ≤ (15774601366183/50000000000000 : ℝ)^3735 := by
    have hnat : (1010954697 : ℕ)^4759*50000000000000^3735 ≤ 15774601366183^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010954697 2500000000 15774601366183 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2286517181/5000000000 : ℝ), (4043819983/10000000000 : ℝ), (1010954697/2500000000 : ℝ)] ![(36901582640361/100000000000000 : ℝ), (6309842922327/20000000000000 : ℝ), (15774601366183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2286517181/5000000000 : ℝ)|^4759 ≤ (36901582640361/100000000000000 : ℝ)^3735
        have hw : |(2286517181/5000000000 : ℝ)|=(2286517181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4043819983/10000000000 : ℝ)|^4759 ≤ (6309842922327/20000000000000 : ℝ)^3735
        have hw : |(4043819983/10000000000 : ℝ)|=(4043819983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010954697/2500000000 : ℝ)|^4759 ≤ (15774601366183/50000000000000 : ℝ)^3735
        have hw : |(1010954697/2500000000 : ℝ)|=(1010954697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_12 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1548277319/10000000000 : ℝ)*x 0 + (5557882783/10000000000 : ℝ)*x 1 + (103884701/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1548277319/10000000000 : ℝ)^4759 ≤ (9283997095279/100000000000000 : ℝ)^3735 := by
    have hnat : (1548277319 : ℕ)^4759*100000000000000^3735 ≤ 9283997095279^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548277319 10000000000 9283997095279 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5557882783/10000000000 : ℝ)^4759 ≤ (2365608636717/5000000000000 : ℝ)^3735 := by
    have hnat : (5557882783 : ℕ)^4759*5000000000000^3735 ≤ 2365608636717^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557882783 10000000000 2365608636717 5000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103884701/200000000 : ℝ)^4759 ≤ (21701915082269/50000000000000 : ℝ)^3735 := by
    have hnat : (103884701 : ℕ)^4759*50000000000000^3735 ≤ 21701915082269^3735*200000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103884701 200000000 21701915082269 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1548277319/10000000000 : ℝ), (5557882783/10000000000 : ℝ), (103884701/200000000 : ℝ)] ![(9283997095279/100000000000000 : ℝ), (2365608636717/5000000000000 : ℝ), (21701915082269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1548277319/10000000000 : ℝ)|^4759 ≤ (9283997095279/100000000000000 : ℝ)^3735
        have hw : |(-1548277319/10000000000 : ℝ)|=(1548277319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5557882783/10000000000 : ℝ)|^4759 ≤ (2365608636717/5000000000000 : ℝ)^3735
        have hw : |(5557882783/10000000000 : ℝ)|=(5557882783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103884701/200000000 : ℝ)|^4759 ≤ (21701915082269/50000000000000 : ℝ)^3735
        have hw : |(103884701/200000000 : ℝ)|=(103884701/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_13 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081134089/2000000000 : ℝ)*x 0 + (-439928057/2500000000 : ℝ)*x 1 + (5194235183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081134089/2000000000 : ℝ)^4759 ≤ (4566744511643/10000000000000 : ℝ)^3735 := by
    have hnat : (1081134089 : ℕ)^4759*10000000000000^3735 ≤ 4566744511643^3735*2000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081134089 2000000000 4566744511643 10000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439928057/2500000000 : ℝ)^4759 ≤ (1366090411617/12500000000000 : ℝ)^3735 := by
    have hnat : (439928057 : ℕ)^4759*12500000000000^3735 ≤ 1366090411617^3735*2500000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439928057 2500000000 1366090411617 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194235183/10000000000 : ℝ)^4759 ≤ (43403831580603/100000000000000 : ℝ)^3735 := by
    have hnat : (5194235183 : ℕ)^4759*100000000000000^3735 ≤ 43403831580603^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194235183 10000000000 43403831580603 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081134089/2000000000 : ℝ), (-439928057/2500000000 : ℝ), (5194235183/10000000000 : ℝ)] ![(4566744511643/10000000000000 : ℝ), (1366090411617/12500000000000 : ℝ), (43403831580603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081134089/2000000000 : ℝ)|^4759 ≤ (4566744511643/10000000000000 : ℝ)^3735
        have hw : |(1081134089/2000000000 : ℝ)|=(1081134089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-439928057/2500000000 : ℝ)|^4759 ≤ (1366090411617/12500000000000 : ℝ)^3735
        have hw : |(-439928057/2500000000 : ℝ)|=(439928057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194235183/10000000000 : ℝ)|^4759 ≤ (43403831580603/100000000000000 : ℝ)^3735
        have hw : |(5194235183/10000000000 : ℝ)|=(5194235183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_14 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405671199/10000000000 : ℝ)*x 0 + (2597117247/5000000000 : ℝ)*x 1 + (-1759712129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405671199/10000000000 : ℝ)^4759 ≤ (22833726616323/50000000000000 : ℝ)^3735 := by
    have hnat : (5405671199 : ℕ)^4759*50000000000000^3735 ≤ 22833726616323^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405671199 10000000000 22833726616323 50000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597117247/5000000000 : ℝ)^4759 ≤ (43403824244747/100000000000000 : ℝ)^3735 := by
    have hnat : (2597117247 : ℕ)^4759*100000000000000^3735 ≤ 43403824244747^3735*5000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597117247 5000000000 43403824244747 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759712129/10000000000 : ℝ)^4759 ≤ (1366090313691/12500000000000 : ℝ)^3735 := by
    have hnat : (1759712129 : ℕ)^4759*12500000000000^3735 ≤ 1366090313691^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759712129 10000000000 1366090313691 12500000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405671199/10000000000 : ℝ), (2597117247/5000000000 : ℝ), (-1759712129/10000000000 : ℝ)] ![(22833726616323/50000000000000 : ℝ), (43403824244747/100000000000000 : ℝ), (1366090313691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405671199/10000000000 : ℝ)|^4759 ≤ (22833726616323/50000000000000 : ℝ)^3735
        have hw : |(5405671199/10000000000 : ℝ)|=(5405671199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597117247/5000000000 : ℝ)|^4759 ≤ (43403824244747/100000000000000 : ℝ)^3735
        have hw : |(2597117247/5000000000 : ℝ)|=(2597117247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759712129/10000000000 : ℝ)|^4759 ≤ (1366090313691/12500000000000 : ℝ)^3735
        have hw : |(-1759712129/10000000000 : ℝ)|=(1759712129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1610_box_15 (p : ℝ) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (387011021/1000000000 : ℝ)*x 0 + (4395266657/10000000000 : ℝ)*x 1 + (4395267493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387011021/1000000000 : ℝ)^4759 ≤ (29832674722159/100000000000000 : ℝ)^3735 := by
    have hnat : (387011021 : ℕ)^4759*100000000000000^3735 ≤ 29832674722159^3735*1000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387011021 1000000000 29832674722159 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4395266657/10000000000 : ℝ)^4759 ≤ (35083658375459/100000000000000 : ℝ)^3735 := by
    have hnat : (4395266657 : ℕ)^4759*100000000000000^3735 ≤ 35083658375459^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395266657 10000000000 35083658375459 100000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4395267493/10000000000 : ℝ)^4759 ≤ (7016733375609/20000000000000 : ℝ)^3735 := by
    have hnat : (4395267493 : ℕ)^4759*20000000000000^3735 ≤ 7016733375609^3735*10000000000^4759 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395267493 10000000000 7016733375609 20000000000000 4759 3735 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4759/1024 : ℝ)) 4759 3735 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(387011021/1000000000 : ℝ), (4395266657/10000000000 : ℝ), (4395267493/10000000000 : ℝ)] ![(29832674722159/100000000000000 : ℝ), (35083658375459/100000000000000 : ℝ), (7016733375609/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(387011021/1000000000 : ℝ)|^4759 ≤ (29832674722159/100000000000000 : ℝ)^3735
        have hw : |(387011021/1000000000 : ℝ)|=(387011021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4395266657/10000000000 : ℝ)|^4759 ≤ (35083658375459/100000000000000 : ℝ)^3735
        have hw : |(4395266657/10000000000 : ℝ)|=(4395266657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4395267493/10000000000 : ℝ)|^4759 ≤ (7016733375609/20000000000000 : ℝ)^3735
        have hw : |(4395267493/10000000000 : ℝ)|=(4395267493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1610_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64919/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29097/50000 : ℝ) ∧ (40217/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5489/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16341/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2609/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16341/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2609/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16341/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2609/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16341/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2609/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16341/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2609/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16341/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2609/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2609/25000 : ℝ) ^ (4755/1024 : ℝ) ≤ (277018824537711/10000000000000000000 : ℝ) := by
    have hpowers : (2609/25000 : ℝ)^4755 ≤ (277018824537711/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2609 : ℕ)^4755*10000000000000000000^1024 ≤ 277018824537711^1024*25000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2609 25000 277018824537711 10000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2609/25000 : ℝ)) (X := (277018824537711/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16341/100000 : ℝ) ^ (4755/1024 : ℝ) ≤ (11111848175698093/50000000000000000000 : ℝ) := by
    have hpowers : (16341/100000 : ℝ)^4755 ≤ (11111848175698093/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16341 : ℕ)^4755*50000000000000000000^1024 ≤ 11111848175698093^1024*100000^4755 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16341 100000 11111848175698093 50000000000000000000 4755 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16341/100000 : ℝ)) (X := (11111848175698093/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000277018824537711/5000000000000000000 : ℝ) ≤ (10000119310666951/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (5000277018824537711/5000000000000000000 : ℝ)^1024 ≤ (10000119310666951/10000000000000000 : ℝ)^4755 := by
      have hnat : (5000277018824537711 : ℕ)^1024*10000000000000000^4755 ≤ 10000119310666951^4755*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000277018824537711 5000000000000000000 10000119310666951 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000119310666951/10000000000000000 : ℝ)) (X := (5000277018824537711/5000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251562117787298331/6250000000000000000 : ℝ) ≤ (1250067274523017/1250000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (6251562117787298331/6250000000000000000 : ℝ)^1024 ≤ (1250067274523017/1250000000000000 : ℝ)^4755 := by
      have hnat : (6251562117787298331 : ℕ)^1024*1250000000000000^4755 ≤ 1250067274523017^4755*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251562117787298331 6250000000000000000 1250067274523017 1250000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250067274523017/1250000000000000 : ℝ)) (X := (6251562117787298331/6250000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011111848175698093/25000000000000000000 : ℝ) ≤ (10000957081701321/10000000000000000 : ℝ) ^ (4755/1024 : ℝ) := by
    have hpowers : (25011111848175698093/25000000000000000000 : ℝ)^1024 ≤ (10000957081701321/10000000000000000 : ℝ)^4755 := by
      have hnat : (25011111848175698093 : ℕ)^1024*10000000000000000^4755 ≤ 10000957081701321^4755*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011111848175698093 25000000000000000000 10000957081701321 10000000000000000 1024 4755 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000957081701321/10000000000000000 : ℝ)) (X := (25011111848175698093/25000000000000000000 : ℝ)) (by norm_num) 4755 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(277018824537711/10000000000000000000 : ℝ) ≤ ((11808392310194732067/11810000000000000000 : ℝ)+2*(83777103437/118100000000000 : ℝ)*(2609/25000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (11808392310194732067/11810000000000000000 : ℝ)+2*(83777103437/118100000000000 : ℝ)*(2609/25000 : ℝ)=(10000119310666951/10000000000000000 : ℝ) by norm_num, show 1+2*(277018824537711/10000000000000000000 : ℝ)=(5000277018824537711/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11111848175698093/50000000000000000000 : ℝ)+(277018824537711/10000000000000000000 : ℝ) ≤ ((11808392310194732067/11810000000000000000 : ℝ)+(83777103437/118100000000000 : ℝ)*((16341/100000 : ℝ)+(2609/25000 : ℝ)))^(4755/1024 : ℝ) := by
    rw [show (11808392310194732067/11810000000000000000 : ℝ)+(83777103437/118100000000000 : ℝ)*((16341/100000 : ℝ)+(2609/25000 : ℝ))=(1250067274523017/1250000000000000 : ℝ) by norm_num, show 1+(11111848175698093/50000000000000000000 : ℝ)+(277018824537711/10000000000000000000 : ℝ)=(6251562117787298331/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11111848175698093/50000000000000000000 : ℝ) ≤ ((11808392310194732067/11810000000000000000 : ℝ)+2*(83777103437/118100000000000 : ℝ)*(16341/100000 : ℝ))^(4755/1024 : ℝ) := by
    rw [show (11808392310194732067/11810000000000000000 : ℝ)+2*(83777103437/118100000000000 : ℝ)*(16341/100000 : ℝ)=(10000957081701321/10000000000000000 : ℝ) by norm_num, show 1+2*(11111848175698093/50000000000000000000 : ℝ)=(25011111848175698093/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11808392310194732067/11810000000000000000 : ℝ)*(X 1 0+X 2 0)+(83777103437/118100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2609/25000 : ℝ)) (hi := (16341/100000 : ℝ)) (c := (11808392310194732067/11810000000000000000 : ℝ)) (alpha := (83777103437/118100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11808392310194732067/11810000000000000000 : ℝ)*(X 0 1+X 2 1)+(83777103437/118100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2609/25000 : ℝ)) (hi := (16341/100000 : ℝ)) (c := (11808392310194732067/11810000000000000000 : ℝ)) (alpha := (83777103437/118100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11808392310194732067/11810000000000000000 : ℝ)*(X 0 2+X 1 2)+(83777103437/118100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4755/1024 : ℝ)) (lo := (2609/25000 : ℝ)) (hi := (16341/100000 : ℝ)) (c := (11808392310194732067/11810000000000000000 : ℝ)) (alpha := (83777103437/118100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1431010147/10000000000 : ℝ)*X 0 0+(541809627/1000000000 : ℝ)*X 0 1+(5418096233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625580111/5000000000 : ℝ)*X 1 0+(-1665395627/10000000000 : ℝ)*X 1 1+(5418096233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625580129/5000000000 : ℝ)*X 2 0+(5418096197/10000000000 : ℝ)*X 2 1+(-1665395627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2246203119/5000000000 : ℝ)*X 0 0+(4085356407/10000000000 : ℝ)*X 0 1+(2042678203/5000000000 : ℝ)*X 0 2+(2246203119/5000000000 : ℝ)*X 1 0+(4085356407/10000000000 : ℝ)*X 1 1+(2042678203/5000000000 : ℝ)*X 1 2+(2246203119/5000000000 : ℝ)*X 2 0+(4085356407/10000000000 : ℝ)*X 2 1+(2042678203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-198831767/1000000000 : ℝ)*X 0 0+(2607053037/5000000000 : ℝ)*X 0 1+(1303526457/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2695974663/5000000000 : ℝ)*X 1 0+(-1751615593/10000000000 : ℝ)*X 1 1+(1042821163/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((168498421/312500000 : ℝ)*X 2 0+(651763199/1250000000 : ℝ)*X 2 1+(-875807847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((785364913/2000000000 : ℝ)*X 0 0+(4367803897/10000000000 : ℝ)*X 0 1+(2183901783/5000000000 : ℝ)*X 0 2+(785364913/2000000000 : ℝ)*X 1 0+(4367803897/10000000000 : ℝ)*X 1 1+(2183901783/5000000000 : ℝ)*X 1 2+(785364913/2000000000 : ℝ)*X 2 0+(4367803897/10000000000 : ℝ)*X 2 1+(2183901783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-934914737/5000000000 : ℝ)*X 0 0+(5068399287/10000000000 : ℝ)*X 0 1+(5448040229/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((26152441/50000000 : ℝ)*X 1 0+(-1652276767/10000000000 : ℝ)*X 1 1+(5448041319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307622111/2500000000 : ℝ)*X 2 0+(681005229/1250000000 : ℝ)*X 2 1+(-41306893/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2286517181/5000000000 : ℝ)*X 0 0+(4043819983/10000000000 : ℝ)*X 0 1+(1010954697/2500000000 : ℝ)*X 0 2+(2286517181/5000000000 : ℝ)*X 1 0+(4043819983/10000000000 : ℝ)*X 1 1+(1010954697/2500000000 : ℝ)*X 1 2+(2286517181/5000000000 : ℝ)*X 2 0+(4043819983/10000000000 : ℝ)*X 2 1+(1010954697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1548277319/10000000000 : ℝ)*X 0 0+(5557882783/10000000000 : ℝ)*X 0 1+(103884701/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1081134089/2000000000 : ℝ)*X 1 0+(-439928057/2500000000 : ℝ)*X 1 1+(5194235183/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5405671199/10000000000 : ℝ)*X 2 0+(2597117247/5000000000 : ℝ)*X 2 1+(-1759712129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((387011021/1000000000 : ℝ)*X 0 0+(4395266657/10000000000 : ℝ)*X 0 1+(4395267493/10000000000 : ℝ)*X 0 2+(387011021/1000000000 : ℝ)*X 1 0+(4395266657/10000000000 : ℝ)*X 1 1+(4395267493/10000000000 : ℝ)*X 1 2+(387011021/1000000000 : ℝ)*X 2 0+(4395266657/10000000000 : ℝ)*X 2 1+(4395267493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1610_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64919/100000 : ℝ) ≤ (-95833086448820219994754497402831/147625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (572099/3125000000000 : ℝ)*(lower2) + (3207883/50000000000000 : ℝ)*(lower3) + (13156059/25000000000000 : ℝ)*(lower5) + (840874896950631/50000000000000 : ℝ)*(major0) + (840874896950631/50000000000000 : ℝ)*(major1) + (840874896950631/50000000000000 : ℝ)*(major2) + (1120711107/100000000000000 : ℝ)*(sp1) + (2321948331/100000000000000 : ℝ)*(sp2) + (36415947/2000000000000 : ℝ)*(sp3) + (2412280009629331/100000000000000 : ℝ)*(sp4) + (1206140003189099/50000000000000 : ℝ)*(sp5) + (1206139402570487/50000000000000 : ℝ)*(sp6) + (972855496579441/100000000000000 : ℝ)*(sp7) + (44698399/4000000000000 : ℝ)*(sp8) + (972857317376791/100000000000000 : ℝ)*(f.failure) + (1206140563544653/50000000000000 : ℝ)*(f.sum) + (859412655731/5905000000000000000000000000 : ℝ)*base66 + (1363298677433284277/590500000000000000000000000000000 : ℝ)*base67 + (270076701688215723/590500000000000000000000000000000 : ℝ)*base70 + (450550768832784277/590500000000000000000000000000000 : ℝ)*base71 + (14267611391637/2952500000000000000000000000 : ℝ)*base73 + (1256480380112784277/590500000000000000000000000000000 : ℝ)*base75 + (2409643865260784277/590500000000000000000000000000000 : ℝ)*base77 + (2008933960045284277/590500000000000000000000000000000 : ℝ)*base79 + (16114742099729/5905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2895899/2000000000000000000000 : ℝ)*base90 + (2895899/2000000000000000000000 : ℝ)*base92 + (2895899/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29097/50000 : ℝ) ≤ (687301148806956614069140083/1181000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1821043/20000000000000 : ℝ)*(lower1) + (2280259/25000000000000 : ℝ)*(lower2) + (1195763/50000000000000 : ℝ)*(lower3) + (11694293/100000000000000 : ℝ)*(lower5) + (176653533183199/10000000000000 : ℝ)*(major0) + (176653533183199/10000000000000 : ℝ)*(major1) + (176653533183199/10000000000000 : ℝ)*(major2) + (622941956756839/25000000000000 : ℝ)*(sp0) + (2491765585027607/100000000000000 : ℝ)*(sp1) + (622941414473103/25000000000000 : ℝ)*(sp2) + (1021903941547173/100000000000000 : ℝ)*(sp3) + (2405041/5000000000000 : ℝ)*(sp7) + (2241999749/100000000000000 : ℝ)*(sp9) + (67785467/3125000000000 : ℝ)*(sp10) + (1021903989647993/100000000000000 : ℝ)*(f.failure) + (622941956756839/25000000000000 : ℝ)*(f.sum) + (183054819403/147625000000000000000000000 : ℝ)*base65 + (23087649957857667/118100000000000000000000000000000 : ℝ)*base68 + (566388513388642333/118100000000000000000000000000000 : ℝ)*base69 + (414338064279557667/118100000000000000000000000000000 : ℝ)*base72 + (3073022184173/1181000000000000000000000000 : ℝ)*base74 + (2302956492195242333/118100000000000000000000000000000 : ℝ)*base75 + (81086844228642333/118100000000000000000000000000000 : ℝ)*base77 + (250521376539057667/118100000000000000000000000000000 : ℝ)*base80 + (8666267627463/295250000000000000000000000 : ℝ)*base81 + (7314123/2000000000000000000000 : ℝ)*base89 + (7314123/2000000000000000000000 : ℝ)*base91 + (7314123/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40217/50000 : ℝ) ≤ (29685982488268993818122969476821/36906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55148379/100000000000000 : ℝ)*(lower3) + (279068529/100000000000000 : ℝ)*(upper4) + (22545173/50000000000000 : ℝ)*(lower5) + (116991603217871/6250000000000 : ℝ)*(major0) + (116991603217871/6250000000000 : ℝ)*(major1) + (116991603217871/6250000000000 : ℝ)*(major2) + (11094958911/100000000000000 : ℝ)*(sp0) + (125391611431/100000000000000 : ℝ)*(sp1) + (114650484383/50000000000000 : ℝ)*(sp2) + (79753098441/100000000000000 : ℝ)*(sp3) + (1317036376171799/50000000000000 : ℝ)*(sp8) + (2633958455691079/100000000000000 : ℝ)*(sp9) + (164615909145859/6250000000000 : ℝ)*(sp10) + (270688909557317/25000000000000 : ℝ)*(sp11) + (1082835391327709/100000000000000 : ℝ)*(f.failure) + (263408384730251/10000000000000 : ℝ)*(f.sum) + (24265763930493/5905000000000000000000000000 : ℝ)*base66 + (506856129484681857/73812500000000000000000000000000 : ℝ)*base67 + (372212097775431857/73812500000000000000000000000000 : ℝ)*base69 + (516417403212130643/73812500000000000000000000000000 : ℝ)*base72 + (16989249915627/5905000000000000000000000000 : ℝ)*base73 + (91260016027005643/73812500000000000000000000000000 : ℝ)*base76 + (145531031914755643/73812500000000000000000000000000 : ℝ)*base78 + (72644724004943143/73812500000000000000000000000000 : ℝ)*base80 + (2761440034873/1476250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1054601/2000000000000000000000 : ℝ)*base90 + (1054601/2000000000000000000000 : ℝ)*base92 + (1054601/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-5489/6250 : ℝ) ≤ (-518587621896844567958985946532277/590500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41527553/50000000000000 : ℝ)*(lower0) + (122867523/50000000000000 : ℝ)*(lower1) + (166386261/100000000000000 : ℝ)*(lower2) + (31757889/100000000000000 : ℝ)*(lower4) + (1913897200735123/100000000000000 : ℝ)*(major0) + (1913897200735123/100000000000000 : ℝ)*(major1) + (1913897200735123/100000000000000 : ℝ)*(major2) + (2378620527/100000000000000 : ℝ)*(sp0) + (66029407061/50000000000000 : ℝ)*(sp5) + (185045921231/100000000000000 : ℝ)*(sp6) + (343739522596911/12500000000000 : ℝ)*(sp12) + (687446625145423/25000000000000 : ℝ)*(sp13) + (343716689184323/12500000000000 : ℝ)*(sp14) + (1107149769361851/100000000000000 : ℝ)*(sp15) + (1107149769361851/100000000000000 : ℝ)*(f.failure) + (1374959279697907/50000000000000 : ℝ)*(f.sum) + (72337415724403/2952500000000000000000000000 : ℝ)*base65 + (6171174539884610759/1181000000000000000000000000000000 : ℝ)*base68 + (4393445748657610759/1181000000000000000000000000000000 : ℝ)*base70 + (9593205325185610759/1181000000000000000000000000000000 : ℝ)*base72 + (15248348016837/2952500000000000000000000000 : ℝ)*base74 + (451288028967389241/1181000000000000000000000000000000 : ℝ)*base75 + (26826860590798389241/1181000000000000000000000000000000 : ℝ)*base77 + (19755654739058610759/1181000000000000000000000000000000 : ℝ)*base80 + (14038451627707/2952500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (22343761/2000000000000000000000 : ℝ)*base89 + (22343761/2000000000000000000000 : ℝ)*base91 + (22343761/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1610_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64919/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29097/50000 : ℝ) else (40217/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5489/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1610_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1610_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64919/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29097/50000 : ℝ) else (40217/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5489/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1610_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4755/1024 : ℝ) ≤ p) (hpb : p ≤ (4759/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34573411/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16341/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2609/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64919/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29097/50000 : ℝ) else (40217/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5489/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1610_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

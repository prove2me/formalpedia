-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:58:45.563633+00:00
-- url     : https://prove2.me/submissions/3df24a4a-2769-4e27-a232-44f4b72a9a64

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
theorem support_rectangle_w1095_s6_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094763173/5000000000 : ℝ)*x 0 + (1348582467/2500000000 : ℝ)*x 1 + (5264518481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094763173/5000000000 : ℝ)^259 ≤ (1329994117261/10000000000000 : ℝ)^195 := by
    have hnat : (1094763173 : ℕ)^259*10000000000000^195 ≤ 1329994117261^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094763173 5000000000 1329994117261 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348582467/2500000000 : ℝ)^259 ≤ (1376600855313/3125000000000 : ℝ)^195 := by
    have hnat : (1348582467 : ℕ)^259*3125000000000^195 ≤ 1376600855313^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348582467 2500000000 1376600855313 3125000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264518481/10000000000 : ℝ)^259 ≤ (42648831434101/100000000000000 : ℝ)^195 := by
    have hnat : (5264518481 : ℕ)^259*100000000000000^195 ≤ 42648831434101^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264518481 10000000000 42648831434101 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094763173/5000000000 : ℝ), (1348582467/2500000000 : ℝ), (5264518481/10000000000 : ℝ)] ![(1329994117261/10000000000000 : ℝ), (1376600855313/3125000000000 : ℝ), (42648831434101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094763173/5000000000 : ℝ)|^259 ≤ (1329994117261/10000000000000 : ℝ)^195
        have hw : |(-1094763173/5000000000 : ℝ)|=(1094763173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348582467/2500000000 : ℝ)|^259 ≤ (1376600855313/3125000000000 : ℝ)^195
        have hw : |(1348582467/2500000000 : ℝ)|=(1348582467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264518481/10000000000 : ℝ)|^259 ≤ (42648831434101/100000000000000 : ℝ)^195
        have hw : |(5264518481/10000000000 : ℝ)|=(5264518481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2672512823/5000000000 : ℝ)*x 0 + (-2255387359/10000000000 : ℝ)*x 1 + (329032399/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672512823/5000000000 : ℝ)^259 ≤ (21758628875011/50000000000000 : ℝ)^195 := by
    have hnat : (2672512823 : ℕ)^259*50000000000000^195 ≤ 21758628875011^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672512823 5000000000 21758628875011 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255387359/10000000000 : ℝ)^259 ≤ (13833911847841/100000000000000 : ℝ)^195 := by
    have hnat : (2255387359 : ℕ)^259*100000000000000^195 ≤ 13833911847841^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255387359 10000000000 13833911847841 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329032399/625000000 : ℝ)^259 ≤ (42648830390377/100000000000000 : ℝ)^195 := by
    have hnat : (329032399 : ℕ)^259*100000000000000^195 ≤ 42648830390377^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329032399 625000000 42648830390377 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672512823/5000000000 : ℝ), (-2255387359/10000000000 : ℝ), (329032399/625000000 : ℝ)] ![(21758628875011/50000000000000 : ℝ), (13833911847841/100000000000000 : ℝ), (42648830390377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672512823/5000000000 : ℝ)|^259 ≤ (21758628875011/50000000000000 : ℝ)^195
        have hw : |(2672512823/5000000000 : ℝ)|=(2672512823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255387359/10000000000 : ℝ)|^259 ≤ (13833911847841/100000000000000 : ℝ)^195
        have hw : |(-2255387359/10000000000 : ℝ)|=(2255387359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329032399/625000000 : ℝ)|^259 ≤ (42648830390377/100000000000000 : ℝ)^195
        have hw : |(329032399/625000000 : ℝ)|=(329032399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5345025479/10000000000 : ℝ)*x 0 + (329032413/625000000 : ℝ)*x 1 + (-451077457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345025479/10000000000 : ℝ)^259 ≤ (43517255944123/100000000000000 : ℝ)^195 := by
    have hnat : (5345025479 : ℕ)^259*100000000000000^195 ≤ 43517255944123^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345025479 10000000000 43517255944123 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329032413/625000000 : ℝ)^259 ≤ (68238132481/160000000000 : ℝ)^195 := by
    have hnat : (329032413 : ℕ)^259*160000000000^195 ≤ 68238132481^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329032413 625000000 68238132481 160000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451077457/2000000000 : ℝ)^259 ≤ (553356449799/4000000000000 : ℝ)^195 := by
    have hnat : (451077457 : ℕ)^259*4000000000000^195 ≤ 553356449799^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451077457 2000000000 553356449799 4000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345025479/10000000000 : ℝ), (329032413/625000000 : ℝ), (-451077457/2000000000 : ℝ)] ![(43517255944123/100000000000000 : ℝ), (68238132481/160000000000 : ℝ), (553356449799/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345025479/10000000000 : ℝ)|^259 ≤ (43517255944123/100000000000000 : ℝ)^195
        have hw : |(5345025479/10000000000 : ℝ)|=(5345025479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329032413/625000000 : ℝ)|^259 ≤ (68238132481/160000000000 : ℝ)^195
        have hw : |(329032413/625000000 : ℝ)|=(329032413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451077457/2000000000 : ℝ)|^259 ≤ (553356449799/4000000000000 : ℝ)^195
        have hw : |(-451077457/2000000000 : ℝ)|=(451077457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4371314199/10000000000 : ℝ)*x 0 + (4245258751/10000000000 : ℝ)*x 1 + (2250568327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371314199/10000000000 : ℝ)^259 ≤ (8329118777713/25000000000000 : ℝ)^195 := by
    have hnat : (4371314199 : ℕ)^259*25000000000000^195 ≤ 8329118777713^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371314199 10000000000 8329118777713 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245258751/10000000000 : ℝ)^259 ≤ (32046485281851/100000000000000 : ℝ)^195 := by
    have hnat : (4245258751 : ℕ)^259*100000000000000^195 ≤ 32046485281851^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245258751 10000000000 32046485281851 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250568327/5000000000 : ℝ)^259 ≤ (17318519791107/50000000000000 : ℝ)^195 := by
    have hnat : (2250568327 : ℕ)^259*50000000000000^195 ≤ 17318519791107^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250568327 5000000000 17318519791107 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371314199/10000000000 : ℝ), (4245258751/10000000000 : ℝ), (2250568327/5000000000 : ℝ)] ![(8329118777713/25000000000000 : ℝ), (32046485281851/100000000000000 : ℝ), (17318519791107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371314199/10000000000 : ℝ)|^259 ≤ (8329118777713/25000000000000 : ℝ)^195
        have hw : |(4371314199/10000000000 : ℝ)|=(4371314199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245258751/10000000000 : ℝ)|^259 ≤ (32046485281851/100000000000000 : ℝ)^195
        have hw : |(4245258751/10000000000 : ℝ)|=(4245258751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250568327/5000000000 : ℝ)|^259 ≤ (17318519791107/50000000000000 : ℝ)^195
        have hw : |(2250568327/5000000000 : ℝ)|=(2250568327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094765711/5000000000 : ℝ)*x 0 + (105296927/200000000 : ℝ)*x 1 + (1348500207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094765711/5000000000 : ℝ)^259 ≤ (13299982125681/100000000000000 : ℝ)^195 := by
    have hnat : (1094765711 : ℕ)^259*100000000000000^195 ≤ 13299982125681^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094765711 5000000000 13299982125681 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105296927/200000000 : ℝ)^259 ≤ (42652359351667/100000000000000 : ℝ)^195 := by
    have hnat : (105296927 : ℕ)^259*100000000000000^195 ≤ 42652359351667^195*200000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105296927 200000000 42652359351667 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348500207/2500000000 : ℝ)^259 ≤ (44047658505881/100000000000000 : ℝ)^195 := by
    have hnat : (1348500207 : ℕ)^259*100000000000000^195 ≤ 44047658505881^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348500207 2500000000 44047658505881 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094765711/5000000000 : ℝ), (105296927/200000000 : ℝ), (1348500207/2500000000 : ℝ)] ![(13299982125681/100000000000000 : ℝ), (42652359351667/100000000000000 : ℝ), (44047658505881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094765711/5000000000 : ℝ)|^259 ≤ (13299982125681/100000000000000 : ℝ)^195
        have hw : |(-1094765711/5000000000 : ℝ)|=(1094765711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105296927/200000000 : ℝ)|^259 ≤ (42652359351667/100000000000000 : ℝ)^195
        have hw : |(105296927/200000000 : ℝ)|=(105296927/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348500207/2500000000 : ℝ)|^259 ≤ (44047658505881/100000000000000 : ℝ)^195
        have hw : |(1348500207/2500000000 : ℝ)|=(1348500207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312254033/10000000000 : ℝ)*x 0 + (-1062952631/5000000000 : ℝ)*x 1 + (539400081/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312254033/10000000000 : ℝ)^259 ≤ (43163230322579/100000000000000 : ℝ)^195 := by
    have hnat : (5312254033 : ℕ)^259*100000000000000^195 ≤ 43163230322579^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312254033 10000000000 43163230322579 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062952631/5000000000 : ℝ)^259 ≤ (12789111350519/100000000000000 : ℝ)^195 := by
    have hnat : (1062952631 : ℕ)^259*100000000000000^195 ≤ 12789111350519^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062952631 5000000000 12789111350519 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539400081/1000000000 : ℝ)^259 ≤ (880953166213/2000000000000 : ℝ)^195 := by
    have hnat : (539400081 : ℕ)^259*2000000000000^195 ≤ 880953166213^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539400081 1000000000 880953166213 2000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312254033/10000000000 : ℝ), (-1062952631/5000000000 : ℝ), (539400081/1000000000 : ℝ)] ![(43163230322579/100000000000000 : ℝ), (12789111350519/100000000000000 : ℝ), (880953166213/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312254033/10000000000 : ℝ)|^259 ≤ (43163230322579/100000000000000 : ℝ)^195
        have hw : |(5312254033/10000000000 : ℝ)|=(5312254033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1062952631/5000000000 : ℝ)|^259 ≤ (12789111350519/100000000000000 : ℝ)^195
        have hw : |(-1062952631/5000000000 : ℝ)|=(1062952631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539400081/1000000000 : ℝ)|^259 ≤ (880953166213/2000000000000 : ℝ)^195
        have hw : |(539400081/1000000000 : ℝ)|=(539400081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (664031753/1250000000 : ℝ)*x 0 + (2697000401/5000000000 : ℝ)*x 1 + (-425181057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664031753/1250000000 : ℝ)^259 ≤ (43163230225451/100000000000000 : ℝ)^195 := by
    have hnat : (664031753 : ℕ)^259*100000000000000^195 ≤ 43163230225451^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664031753 1250000000 43163230225451 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697000401/5000000000 : ℝ)^259 ≤ (1101191455597/2500000000000 : ℝ)^195 := by
    have hnat : (2697000401 : ℕ)^259*2500000000000^195 ≤ 1101191455597^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697000401 5000000000 1101191455597 2500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425181057/2000000000 : ℝ)^259 ≤ (2557822306859/20000000000000 : ℝ)^195 := by
    have hnat : (425181057 : ℕ)^259*20000000000000^195 ≤ 2557822306859^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425181057 2000000000 2557822306859 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664031753/1250000000 : ℝ), (2697000401/5000000000 : ℝ), (-425181057/2000000000 : ℝ)] ![(43163230225451/100000000000000 : ℝ), (1101191455597/2500000000000 : ℝ), (2557822306859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664031753/1250000000 : ℝ)|^259 ≤ (43163230225451/100000000000000 : ℝ)^195
        have hw : |(664031753/1250000000 : ℝ)|=(664031753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697000401/5000000000 : ℝ)|^259 ≤ (1101191455597/2500000000000 : ℝ)^195
        have hw : |(2697000401/5000000000 : ℝ)|=(2697000401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425181057/2000000000 : ℝ)|^259 ≤ (2557822306859/20000000000000 : ℝ)^195
        have hw : |(-425181057/2000000000 : ℝ)|=(425181057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s6_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4371324117/10000000000 : ℝ)*x 0 + (900098069/2000000000 : ℝ)*x 1 + (84918151/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371324117/10000000000 : ℝ)^259 ≤ (33316575511483/100000000000000 : ℝ)^195 := by
    have hnat : (4371324117 : ℕ)^259*100000000000000^195 ≤ 33316575511483^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371324117 10000000000 33316575511483 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900098069/2000000000 : ℝ)^259 ≤ (17315216980319/50000000000000 : ℝ)^195 := by
    have hnat : (900098069 : ℕ)^259*50000000000000^195 ≤ 17315216980319^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900098069 2000000000 17315216980319 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84918151/200000000 : ℝ)^259 ≤ (32052990508839/100000000000000 : ℝ)^195 := by
    have hnat : (84918151 : ℕ)^259*100000000000000^195 ≤ 32052990508839^195*200000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84918151 200000000 32052990508839 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371324117/10000000000 : ℝ), (900098069/2000000000 : ℝ), (84918151/200000000 : ℝ)] ![(33316575511483/100000000000000 : ℝ), (17315216980319/50000000000000 : ℝ), (32052990508839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371324117/10000000000 : ℝ)|^259 ≤ (33316575511483/100000000000000 : ℝ)^195
        have hw : |(4371324117/10000000000 : ℝ)|=(4371324117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900098069/2000000000 : ℝ)|^259 ≤ (17315216980319/50000000000000 : ℝ)^195
        have hw : |(900098069/2000000000 : ℝ)|=(900098069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84918151/200000000 : ℝ)|^259 ≤ (32052990508839/100000000000000 : ℝ)^195
        have hw : |(84918151/200000000 : ℝ)|=(84918151/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/25000 : ℝ) ^ (8287/2048 : ℝ) ≤ (14443042178458973/100000000000000000000 : ℝ) := by
    have hpowers : (2811/25000 : ℝ)^8287 ≤ (14443042178458973/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2811 : ℕ)^8287*100000000000000000000^2048 ≤ 14443042178458973^2048*25000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 25000 14443042178458973 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/25000 : ℝ)) (X := (14443042178458973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/10000 : ℝ) ^ (8287/2048 : ℝ) ≤ (35782324309530691/100000000000000000000 : ℝ) := by
    have hpowers : (1407/10000 : ℝ)^8287 ≤ (35782324309530691/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1407 : ℕ)^8287*100000000000000000000^2048 ≤ 35782324309530691^2048*10000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 10000 35782324309530691 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/10000 : ℝ)) (X := (35782324309530691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014443042178458973/50000000000000000000 : ℝ) ≤ (5000356897967443/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50014443042178458973/50000000000000000000 : ℝ)^2048 ≤ (5000356897967443/5000000000000000 : ℝ)^8287 := by
      have hnat : (50014443042178458973 : ℕ)^2048*5000000000000000^8287 ≤ 5000356897967443^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014443042178458973 50000000000000000000 5000356897967443 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000356897967443/5000000000000000 : ℝ)) (X := (50014443042178458973/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126569542702749677/3125000000000000000 : ℝ) ≤ (10001241005294681/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (3126569542702749677/3125000000000000000 : ℝ)^2048 ≤ (10001241005294681/10000000000000000 : ℝ)^8287 := by
      have hnat : (3126569542702749677 : ℕ)^2048*10000000000000000^8287 ≤ 10001241005294681^8287*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126569542702749677 3125000000000000000 10001241005294681 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001241005294681/10000000000000000 : ℝ)) (X := (3126569542702749677/3125000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035782324309530691/50000000000000000000 : ℝ) ≤ (2500442053663619/2500000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50035782324309530691/50000000000000000000 : ℝ)^2048 ≤ (2500442053663619/2500000000000000 : ℝ)^8287 := by
      have hnat : (50035782324309530691 : ℕ)^2048*2500000000000000^8287 ≤ 2500442053663619^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035782324309530691 50000000000000000000 2500442053663619 2500000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500442053663619/2500000000000000 : ℝ)) (X := (50035782324309530691/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14443042178458973/100000000000000000000 : ℝ) ≤ ((784726702867469941/785000000000000000 : ℝ)+2*(11715763551/6280000000000 : ℝ)*(2811/25000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (784726702867469941/785000000000000000 : ℝ)+2*(11715763551/6280000000000 : ℝ)*(2811/25000 : ℝ)=(5000356897967443/5000000000000000 : ℝ) by norm_num, show 1+2*(14443042178458973/100000000000000000000 : ℝ)=(50014443042178458973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35782324309530691/100000000000000000000 : ℝ)+(14443042178458973/100000000000000000000 : ℝ) ≤ ((784726702867469941/785000000000000000 : ℝ)+(11715763551/6280000000000 : ℝ)*((1407/10000 : ℝ)+(2811/25000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (784726702867469941/785000000000000000 : ℝ)+(11715763551/6280000000000 : ℝ)*((1407/10000 : ℝ)+(2811/25000 : ℝ))=(10001241005294681/10000000000000000 : ℝ) by norm_num, show 1+(35782324309530691/100000000000000000000 : ℝ)+(14443042178458973/100000000000000000000 : ℝ)=(3126569542702749677/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35782324309530691/100000000000000000000 : ℝ) ≤ ((784726702867469941/785000000000000000 : ℝ)+2*(11715763551/6280000000000 : ℝ)*(1407/10000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (784726702867469941/785000000000000000 : ℝ)+2*(11715763551/6280000000000 : ℝ)*(1407/10000 : ℝ)=(2500442053663619/2500000000000000 : ℝ) by norm_num, show 1+2*(35782324309530691/100000000000000000000 : ℝ)=(50035782324309530691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (784726702867469941/785000000000000000 : ℝ)*(X 1 0+X 2 0)+(11715763551/6280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (784726702867469941/785000000000000000 : ℝ)) (alpha := (11715763551/6280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (784726702867469941/785000000000000000 : ℝ)*(X 0 1+X 2 1)+(11715763551/6280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (784726702867469941/785000000000000000 : ℝ)) (alpha := (11715763551/6280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (784726702867469941/785000000000000000 : ℝ)*(X 0 2+X 1 2)+(11715763551/6280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (784726702867469941/785000000000000000 : ℝ)) (alpha := (11715763551/6280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094763173/5000000000 : ℝ)*X 0 0+(1348582467/2500000000 : ℝ)*X 0 1+(5264518481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672512823/5000000000 : ℝ)*X 1 0+(-2255387359/10000000000 : ℝ)*X 1 1+(329032399/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345025479/10000000000 : ℝ)*X 2 0+(329032413/625000000 : ℝ)*X 2 1+(-451077457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371314199/10000000000 : ℝ)*X 0 0+(4245258751/10000000000 : ℝ)*X 0 1+(2250568327/5000000000 : ℝ)*X 0 2+(4371314199/10000000000 : ℝ)*X 1 0+(4245258751/10000000000 : ℝ)*X 1 1+(2250568327/5000000000 : ℝ)*X 1 2+(4371314199/10000000000 : ℝ)*X 2 0+(4245258751/10000000000 : ℝ)*X 2 1+(2250568327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094765711/5000000000 : ℝ)*X 0 0+(105296927/200000000 : ℝ)*X 0 1+(1348500207/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312254033/10000000000 : ℝ)*X 1 0+(-1062952631/5000000000 : ℝ)*X 1 1+(539400081/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664031753/1250000000 : ℝ)*X 2 0+(2697000401/5000000000 : ℝ)*X 2 1+(-425181057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371324117/10000000000 : ℝ)*X 0 0+(900098069/2000000000 : ℝ)*X 0 1+(84918151/200000000 : ℝ)*X 0 2+(4371324117/10000000000 : ℝ)*X 1 0+(900098069/2000000000 : ℝ)*X 1 1+(84918151/200000000 : ℝ)*X 1 2+(4371324117/10000000000 : ℝ)*X 2 0+(900098069/2000000000 : ℝ)*X 2 1+(84918151/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11530838821005193741911261/1570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143012369/5000000000000 : ℝ)*(base19) + (2515615873/100000000000000 : ℝ)*(base23) + (55555523/100000000000000 : ℝ)*(lower2) + (54232901/25000000000000 : ℝ)*(upper3) + (105491269/50000000000000 : ℝ)*(upper5) + (232236994727507/4000000000000 : ℝ)*(major0) + (232236994727507/4000000000000 : ℝ)*(major1) + (232236994727507/4000000000000 : ℝ)*(major2) + (3851783643134209/50000000000000 : ℝ)*(sp0) + (3851823253658497/50000000000000 : ℝ)*(sp1) + (7703646851948501/100000000000000 : ℝ)*(sp2) + (977039303182051/25000000000000 : ℝ)*(sp3) + (20520323989/25000000000000 : ℝ)*(sp4) + (42911266653/100000000000000 : ℝ)*(sp7) + (1954100061997429/50000000000000 : ℝ)*(f.failure) + (3851824683782187/50000000000000 : ℝ)*(f.sum) + (2682007187707/314000000000000000000000000 : ℝ)*base65 + (19939716468827913/3140000000000000000000000000000 : ℝ)*base68 + (25891546815112087/3140000000000000000000000000000 : ℝ)*base69 + (15031328781947913/3140000000000000000000000000000 : ℝ)*base72 + (383046546023/314000000000000000000000000 : ℝ)*base73 + (9791203024687913/3140000000000000000000000000000 : ℝ)*base76 + (19322692613352087/3140000000000000000000000000000 : ℝ)*base77 + (32101995226587913/3140000000000000000000000000000 : ℝ)*base80 + (734503562691/314000000000000000000000000 : ℝ)*base81 + (6579581/625000000000000000000 : ℝ)*base89 + (6579581/625000000000000000000 : ℝ)*base91 + (6579581/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56589951496927161790421163/9812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1405705797/100000000000000 : ℝ)*(base19) + (698878413/50000000000000 : ℝ)*(base23) + (25812131/20000000000000 : ℝ)*(upper3) + (2414859/25000000000000 : ℝ)*(lower4) + (39302887/25000000000000 : ℝ)*(upper5) + (2917665386456081/50000000000000 : ℝ)*(major0) + (2917665386456081/50000000000000 : ℝ)*(major1) + (2917665386456081/50000000000000 : ℝ)*(major2) + (608758433/1562500000000 : ℝ)*(sp1) + (36851046443/100000000000000 : ℝ)*(sp2) + (3871333469801831/50000000000000 : ℝ)*(sp4) + (7742626573358153/100000000000000 : ℝ)*(sp5) + (7742628690800393/100000000000000 : ℝ)*(sp6) + (157119776559321/4000000000000 : ℝ)*(sp7) + (157119776559321/4000000000000 : ℝ)*(f.failure) + (3871333469801831/50000000000000 : ℝ)*(f.sum) + (426107096777/78500000000000000000000000 : ℝ)*base65 + (173660623768213779/39250000000000000000000000000000 : ℝ)*base68 + (813154733537463779/39250000000000000000000000000000 : ℝ)*base70 + (33127153392536221/39250000000000000000000000000000 : ℝ)*base71 + (30385242827/4906250000000000000000000 : ℝ)*base73 + (1098436968715963779/39250000000000000000000000000000 : ℝ)*base76 + (118896638506463779/39250000000000000000000000000000 : ℝ)*base78 + (1075715617345713779/39250000000000000000000000000000 : ℝ)*base80 + (296742238701/157000000000000000000000000 : ℝ)*base81 + (21169/50000000000000000000 : ℝ)*base89 + (21169/50000000000000000000 : ℝ)*base91 + (21169/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1095_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_s7_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189562101/10000000000 : ℝ)*x 0 + (1348481627/2500000000 : ℝ)*x 1 + (263244913/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189562101/10000000000 : ℝ)^259 ≤ (13300229643931/100000000000000 : ℝ)^195 := by
    have hnat : (2189562101 : ℕ)^259*100000000000000^195 ≤ 13300229643931^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189562101 10000000000 13300229643931 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348481627/2500000000 : ℝ)^259 ≤ (44046852419303/100000000000000 : ℝ)^195 := by
    have hnat : (1348481627 : ℕ)^259*100000000000000^195 ≤ 44046852419303^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348481627 2500000000 44046852419303 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263244913/500000000 : ℝ)^259 ≤ (2132645895867/5000000000000 : ℝ)^195 := by
    have hnat : (263244913 : ℕ)^259*5000000000000^195 ≤ 2132645895867^195*500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263244913 500000000 2132645895867 5000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189562101/10000000000 : ℝ), (1348481627/2500000000 : ℝ), (263244913/500000000 : ℝ)] ![(13300229643931/100000000000000 : ℝ), (44046852419303/100000000000000 : ℝ), (2132645895867/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189562101/10000000000 : ℝ)|^259 ≤ (13300229643931/100000000000000 : ℝ)^195
        have hw : |(-2189562101/10000000000 : ℝ)|=(2189562101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348481627/2500000000 : ℝ)|^259 ≤ (44046852419303/100000000000000 : ℝ)^195
        have hw : |(1348481627/2500000000 : ℝ)|=(1348481627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263244913/500000000 : ℝ)|^259 ≤ (2132645895867/5000000000000 : ℝ)^195
        have hw : |(263244913/500000000 : ℝ)|=(263244913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (334057747/625000000 : ℝ)*x 0 + (-17617347/78125000 : ℝ)*x 1 + (6581123/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334057747/625000000 : ℝ)^259 ≤ (21758079029279/50000000000000 : ℝ)^195 := by
    have hnat : (334057747 : ℕ)^259*50000000000000^195 ≤ 21758079029279^195*625000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334057747 625000000 21758079029279 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17617347/78125000 : ℝ)^259 ≤ (6915461251467/50000000000000 : ℝ)^195 := by
    have hnat : (17617347 : ℕ)^259*50000000000000^195 ≤ 6915461251467^195*78125000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17617347 78125000 6915461251467 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6581123/12500000 : ℝ)^259 ≤ (42652919423781/100000000000000 : ℝ)^195 := by
    have hnat : (6581123 : ℕ)^259*100000000000000^195 ≤ 42652919423781^195*12500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6581123 12500000 42652919423781 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334057747/625000000 : ℝ), (-17617347/78125000 : ℝ), (6581123/12500000 : ℝ)] ![(21758079029279/50000000000000 : ℝ), (6915461251467/50000000000000 : ℝ), (42652919423781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334057747/625000000 : ℝ)|^259 ≤ (21758079029279/50000000000000 : ℝ)^195
        have hw : |(334057747/625000000 : ℝ)|=(334057747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17617347/78125000 : ℝ)|^259 ≤ (6915461251467/50000000000000 : ℝ)^195
        have hw : |(-17617347/78125000 : ℝ)|=(17617347/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6581123/12500000 : ℝ)|^259 ≤ (42652919423781/100000000000000 : ℝ)^195
        have hw : |(6581123/12500000 : ℝ)|=(6581123/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (534492427/1000000000 : ℝ)*x 0 + (5264898177/10000000000 : ℝ)*x 1 + (-8808673/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534492427/1000000000 : ℝ)^259 ≤ (43516161497313/100000000000000 : ℝ)^195 := by
    have hnat : (534492427 : ℕ)^259*100000000000000^195 ≤ 43516161497313^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534492427 1000000000 43516161497313 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264898177/10000000000 : ℝ)^259 ≤ (10663229256059/25000000000000 : ℝ)^195 := by
    have hnat : (5264898177 : ℕ)^259*25000000000000^195 ≤ 10663229256059^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264898177 10000000000 10663229256059 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8808673/39062500 : ℝ)^259 ≤ (2766184292039/20000000000000 : ℝ)^195 := by
    have hnat : (8808673 : ℕ)^259*20000000000000^195 ≤ 2766184292039^195*39062500^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8808673 39062500 2766184292039 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534492427/1000000000 : ℝ), (5264898177/10000000000 : ℝ), (-8808673/39062500 : ℝ)] ![(43516161497313/100000000000000 : ℝ), (10663229256059/25000000000000 : ℝ), (2766184292039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534492427/1000000000 : ℝ)|^259 ≤ (43516161497313/100000000000000 : ℝ)^195
        have hw : |(534492427/1000000000 : ℝ)|=(534492427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264898177/10000000000 : ℝ)|^259 ≤ (10663229256059/25000000000000 : ℝ)^195
        have hw : |(5264898177/10000000000 : ℝ)|=(5264898177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8808673/39062500 : ℝ)|^259 ≤ (2766184292039/20000000000000 : ℝ)^195
        have hw : |(-8808673/39062500 : ℝ)|=(8808673/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4371334157/10000000000 : ℝ)*x 0 + (4246028319/10000000000 : ℝ)*x 1 + (4500361917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371334157/10000000000 : ℝ)^259 ≤ (8329169286801/25000000000000 : ℝ)^195 := by
    have hnat : (4371334157 : ℕ)^259*25000000000000^195 ≤ 8329169286801^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371334157 10000000000 8329169286801 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246028319/10000000000 : ℝ)^259 ≤ (32054201443391/100000000000000 : ℝ)^195 := by
    have hnat : (4246028319 : ℕ)^259*100000000000000^195 ≤ 32054201443391^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246028319 10000000000 32054201443391 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500361917/10000000000 : ℝ)^259 ≤ (432864017441/1250000000000 : ℝ)^195 := by
    have hnat : (4500361917 : ℕ)^259*1250000000000^195 ≤ 432864017441^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500361917 10000000000 432864017441 1250000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371334157/10000000000 : ℝ), (4246028319/10000000000 : ℝ), (4500361917/10000000000 : ℝ)] ![(8329169286801/25000000000000 : ℝ), (32054201443391/100000000000000 : ℝ), (432864017441/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371334157/10000000000 : ℝ)|^259 ≤ (8329169286801/25000000000000 : ℝ)^195
        have hw : |(4371334157/10000000000 : ℝ)|=(4371334157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246028319/10000000000 : ℝ)|^259 ≤ (32054201443391/100000000000000 : ℝ)^195
        have hw : |(4246028319/10000000000 : ℝ)|=(4246028319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500361917/10000000000 : ℝ)|^259 ≤ (432864017441/1250000000000 : ℝ)^195
        have hw : |(4500361917/10000000000 : ℝ)|=(4500361917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189567239/10000000000 : ℝ)*x 0 + (5265222209/10000000000 : ℝ)*x 1 + (1078720259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189567239/10000000000 : ℝ)^259 ≤ (83126694359/625000000000 : ℝ)^195 := by
    have hnat : (2189567239 : ℕ)^259*625000000000^195 ≤ 83126694359^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189567239 10000000000 83126694359 625000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265222209/10000000000 : ℝ)^259 ≤ (42656403737243/100000000000000 : ℝ)^195 := by
    have hnat : (5265222209 : ℕ)^259*100000000000000^195 ≤ 42656403737243^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265222209 10000000000 42656403737243 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078720259/2000000000 : ℝ)^259 ≤ (4404332515009/10000000000000 : ℝ)^195 := by
    have hnat : (1078720259 : ℕ)^259*10000000000000^195 ≤ 4404332515009^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078720259 2000000000 4404332515009 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189567239/10000000000 : ℝ), (5265222209/10000000000 : ℝ), (1078720259/2000000000 : ℝ)] ![(83126694359/625000000000 : ℝ), (42656403737243/100000000000000 : ℝ), (4404332515009/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189567239/10000000000 : ℝ)|^259 ≤ (83126694359/625000000000 : ℝ)^195
        have hw : |(-2189567239/10000000000 : ℝ)|=(2189567239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265222209/10000000000 : ℝ)|^259 ≤ (42656403737243/100000000000000 : ℝ)^195
        have hw : |(5265222209/10000000000 : ℝ)|=(5265222209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078720259/2000000000 : ℝ)|^259 ≤ (4404332515009/10000000000000 : ℝ)^195
        have hw : |(1078720259/2000000000 : ℝ)|=(1078720259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656175183/5000000000 : ℝ)*x 0 + (-1063158721/5000000000 : ℝ)*x 1 + (1078720259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656175183/5000000000 : ℝ)^259 ≤ (43164269947389/100000000000000 : ℝ)^195 := by
    have hnat : (2656175183 : ℕ)^259*100000000000000^195 ≤ 43164269947389^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656175183 5000000000 43164269947389 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063158721/5000000000 : ℝ)^259 ≤ (6396202443/50000000000 : ℝ)^195 := by
    have hnat : (1063158721 : ℕ)^259*50000000000^195 ≤ 6396202443^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063158721 5000000000 6396202443 50000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078720259/2000000000 : ℝ)^259 ≤ (4404332515009/10000000000000 : ℝ)^195 := by
    have hnat : (1078720259 : ℕ)^259*10000000000000^195 ≤ 4404332515009^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078720259 2000000000 4404332515009 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656175183/5000000000 : ℝ), (-1063158721/5000000000 : ℝ), (1078720259/2000000000 : ℝ)] ![(43164269947389/100000000000000 : ℝ), (6396202443/50000000000 : ℝ), (4404332515009/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656175183/5000000000 : ℝ)|^259 ≤ (43164269947389/100000000000000 : ℝ)^195
        have hw : |(2656175183/5000000000 : ℝ)|=(2656175183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063158721/5000000000 : ℝ)|^259 ≤ (6396202443/50000000000 : ℝ)^195
        have hw : |(-1063158721/5000000000 : ℝ)|=(1063158721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078720259/2000000000 : ℝ)|^259 ≤ (4404332515009/10000000000000 : ℝ)^195
        have hw : |(1078720259/2000000000 : ℝ)|=(1078720259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2656175183/5000000000 : ℝ)*x 0 + (1078720259/2000000000 : ℝ)*x 1 + (-1063158721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656175183/5000000000 : ℝ)^259 ≤ (43164269947389/100000000000000 : ℝ)^195 := by
    have hnat : (2656175183 : ℕ)^259*100000000000000^195 ≤ 43164269947389^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656175183 5000000000 43164269947389 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078720259/2000000000 : ℝ)^259 ≤ (4404332515009/10000000000000 : ℝ)^195 := by
    have hnat : (1078720259 : ℕ)^259*10000000000000^195 ≤ 4404332515009^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078720259 2000000000 4404332515009 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063158721/5000000000 : ℝ)^259 ≤ (6396202443/50000000000 : ℝ)^195 := by
    have hnat : (1063158721 : ℕ)^259*50000000000^195 ≤ 6396202443^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063158721 5000000000 6396202443 50000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656175183/5000000000 : ℝ), (1078720259/2000000000 : ℝ), (-1063158721/5000000000 : ℝ)] ![(43164269947389/100000000000000 : ℝ), (4404332515009/10000000000000 : ℝ), (6396202443/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656175183/5000000000 : ℝ)|^259 ≤ (43164269947389/100000000000000 : ℝ)^195
        have hw : |(2656175183/5000000000 : ℝ)|=(2656175183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078720259/2000000000 : ℝ)|^259 ≤ (4404332515009/10000000000000 : ℝ)^195
        have hw : |(1078720259/2000000000 : ℝ)|=(1078720259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063158721/5000000000 : ℝ)|^259 ≤ (6396202443/50000000000 : ℝ)^195
        have hw : |(-1063158721/5000000000 : ℝ)|=(1063158721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s7_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4371343937/10000000000 : ℝ)*x 0 + (140616361/312500000 : ℝ)*x 1 + (849333817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371343937/10000000000 : ℝ)^259 ≤ (33316776150999/100000000000000 : ℝ)^195 := by
    have hnat : (4371343937 : ℕ)^259*100000000000000^195 ≤ 33316776150999^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371343937 10000000000 33316776150999 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140616361/312500000 : ℝ)^259 ≤ (17311298666167/50000000000000 : ℝ)^195 := by
    have hnat : (140616361 : ℕ)^259*50000000000000^195 ≤ 17311298666167^195*312500000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140616361 312500000 17311298666167 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849333817/2000000000 : ℝ)^259 ≤ (16030313253579/50000000000000 : ℝ)^195 := by
    have hnat : (849333817 : ℕ)^259*50000000000000^195 ≤ 16030313253579^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849333817 2000000000 16030313253579 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371343937/10000000000 : ℝ), (140616361/312500000 : ℝ), (849333817/2000000000 : ℝ)] ![(33316776150999/100000000000000 : ℝ), (17311298666167/50000000000000 : ℝ), (16030313253579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371343937/10000000000 : ℝ)|^259 ≤ (33316776150999/100000000000000 : ℝ)^195
        have hw : |(4371343937/10000000000 : ℝ)|=(4371343937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140616361/312500000 : ℝ)|^259 ≤ (17311298666167/50000000000000 : ℝ)^195
        have hw : |(140616361/312500000 : ℝ)|=(140616361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849333817/2000000000 : ℝ)|^259 ≤ (16030313253579/50000000000000 : ℝ)^195
        have hw : |(849333817/2000000000 : ℝ)|=(849333817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11289/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14031/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14031/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11281/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (365908013000671/2500000000000000000 : ℝ) := by
    have hpowers : (11281/100000 : ℝ)^8287 ≤ (365908013000671/2500000000000000000 : ℝ)^2048 := by
      have hnat : (11281 : ℕ)^8287*2500000000000000000^2048 ≤ 365908013000671^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 100000 365908013000671 2500000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/100000 : ℝ)) (X := (365908013000671/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14031/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (2211417569859113/6250000000000000000 : ℝ) := by
    have hpowers : (14031/100000 : ℝ)^8287 ≤ (2211417569859113/6250000000000000000 : ℝ)^2048 := by
      have hnat : (14031 : ℕ)^8287*6250000000000000000^2048 ≤ 2211417569859113^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14031 100000 2211417569859113 6250000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14031/100000 : ℝ)) (X := (2211417569859113/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250365908013000671/1250000000000000000 : ℝ) ≤ (5000361673488213/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (1250365908013000671/1250000000000000000 : ℝ)^2048 ≤ (5000361673488213/5000000000000000 : ℝ)^8287 := by
      have hnat : (1250365908013000671 : ℕ)^2048*5000000000000000^8287 ≤ 5000361673488213^8287*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250365908013000671 1250000000000000000 5000361673488213 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361673488213/5000000000000000 : ℝ)) (X := (1250365908013000671/1250000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506252375204721581/12500000000000000000 : ℝ) ≤ (625077244202493/625000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (12506252375204721581/12500000000000000000 : ℝ)^2048 ≤ (625077244202493/625000000000000 : ℝ)^8287 := by
      have hnat : (12506252375204721581 : ℕ)^2048*625000000000000^8287 ≤ 625077244202493^8287*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506252375204721581 12500000000000000000 625077244202493 625000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625077244202493/625000000000000 : ℝ)) (X := (12506252375204721581/12500000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127211417569859113/3125000000000000000 : ℝ) ≤ (200034969350067/200000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (3127211417569859113/3125000000000000000 : ℝ)^2048 ≤ (200034969350067/200000000000000 : ℝ)^8287 := by
      have hnat : (3127211417569859113 : ℕ)^2048*200000000000000^8287 ≤ 200034969350067^8287*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127211417569859113 3125000000000000000 200034969350067 200000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200034969350067/200000000000000 : ℝ)) (X := (3127211417569859113/3125000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(365908013000671/2500000000000000000 : ℝ) ≤ ((859075775610029433/859375000000000000 : ℝ)+2*(256280131731/137500000000000 : ℝ)*(11281/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (859075775610029433/859375000000000000 : ℝ)+2*(256280131731/137500000000000 : ℝ)*(11281/100000 : ℝ)=(5000361673488213/5000000000000000 : ℝ) by norm_num, show 1+2*(365908013000671/2500000000000000000 : ℝ)=(1250365908013000671/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2211417569859113/6250000000000000000 : ℝ)+(365908013000671/2500000000000000000 : ℝ) ≤ ((859075775610029433/859375000000000000 : ℝ)+(256280131731/137500000000000 : ℝ)*((14031/100000 : ℝ)+(11281/100000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (859075775610029433/859375000000000000 : ℝ)+(256280131731/137500000000000 : ℝ)*((14031/100000 : ℝ)+(11281/100000 : ℝ))=(625077244202493/625000000000000 : ℝ) by norm_num, show 1+(2211417569859113/6250000000000000000 : ℝ)+(365908013000671/2500000000000000000 : ℝ)=(12506252375204721581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2211417569859113/6250000000000000000 : ℝ) ≤ ((859075775610029433/859375000000000000 : ℝ)+2*(256280131731/137500000000000 : ℝ)*(14031/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (859075775610029433/859375000000000000 : ℝ)+2*(256280131731/137500000000000 : ℝ)*(14031/100000 : ℝ)=(200034969350067/200000000000000 : ℝ) by norm_num, show 1+2*(2211417569859113/6250000000000000000 : ℝ)=(3127211417569859113/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (859075775610029433/859375000000000000 : ℝ)*(X 1 0+X 2 0)+(256280131731/137500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (859075775610029433/859375000000000000 : ℝ)) (alpha := (256280131731/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (859075775610029433/859375000000000000 : ℝ)*(X 0 1+X 2 1)+(256280131731/137500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (859075775610029433/859375000000000000 : ℝ)) (alpha := (256280131731/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (859075775610029433/859375000000000000 : ℝ)*(X 0 2+X 1 2)+(256280131731/137500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (14031/100000 : ℝ)) (c := (859075775610029433/859375000000000000 : ℝ)) (alpha := (256280131731/137500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189562101/10000000000 : ℝ)*X 0 0+(1348481627/2500000000 : ℝ)*X 0 1+(263244913/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334057747/625000000 : ℝ)*X 1 0+(-17617347/78125000 : ℝ)*X 1 1+(6581123/12500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534492427/1000000000 : ℝ)*X 2 0+(5264898177/10000000000 : ℝ)*X 2 1+(-8808673/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371334157/10000000000 : ℝ)*X 0 0+(4246028319/10000000000 : ℝ)*X 0 1+(4500361917/10000000000 : ℝ)*X 0 2+(4371334157/10000000000 : ℝ)*X 1 0+(4246028319/10000000000 : ℝ)*X 1 1+(4500361917/10000000000 : ℝ)*X 1 2+(4371334157/10000000000 : ℝ)*X 2 0+(4246028319/10000000000 : ℝ)*X 2 1+(4500361917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2189567239/10000000000 : ℝ)*X 0 0+(5265222209/10000000000 : ℝ)*X 0 1+(1078720259/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656175183/5000000000 : ℝ)*X 1 0+(-1063158721/5000000000 : ℝ)*X 1 1+(1078720259/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656175183/5000000000 : ℝ)*X 2 0+(1078720259/2000000000 : ℝ)*X 2 1+(-1063158721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371343937/10000000000 : ℝ)*X 0 0+(140616361/312500000 : ℝ)*X 0 1+(849333817/2000000000 : ℝ)*X 0 2+(4371343937/10000000000 : ℝ)*X 1 0+(140616361/312500000 : ℝ)*X 1 1+(849333817/2000000000 : ℝ)*X 1 2+(4371343937/10000000000 : ℝ)*X 2 0+(140616361/312500000 : ℝ)*X 2 1+(849333817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20991963106866464179253781/1953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87135777/4000000000000 : ℝ)*(base19) + (2236126009/100000000000000 : ℝ)*(base23) + (21560483/10000000000000 : ℝ)*(lower2) + (6030711/3125000000000 : ℝ)*(upper3) + (182570747/100000000000000 : ℝ)*(upper5) + (730142724244373/12500000000000 : ℝ)*(major0) + (730142724244373/12500000000000 : ℝ)*(major1) + (730142724244373/12500000000000 : ℝ)*(major2) + (7750303603742431/100000000000000 : ℝ)*(sp0) + (7750375006706811/100000000000000 : ℝ)*(sp1) + (7750374948975227/100000000000000 : ℝ)*(sp2) + (122871014543541/3125000000000 : ℝ)*(sp3) + (14716271761/20000000000000 : ℝ)*(sp4) + (33579152577/100000000000000 : ℝ)*(sp7) + (3931906044545889/100000000000000 : ℝ)*(f.failure) + (1937594296275309/25000000000000 : ℝ)*(f.sum) + (1098500148789/625000000000000000000000000 : ℝ)*base65 + (9766002552800987/1953125000000000000000000000000 : ℝ)*base68 + (2190566177767681/976562500000000000000000000000 : ℝ)*base70 + (787317943425987/1953125000000000000000000000000 : ℝ)*base72 + (517836383667/78125000000000000000000000 : ℝ)*base74 + (34723475841863487/1953125000000000000000000000000 : ℝ)*base76 + (15759236337957237/1953125000000000000000000000000 : ℝ)*base78 + (18375599037042763/1953125000000000000000000000000 : ℝ)*base79 + (2816774267461/625000000000000000000000000 : ℝ)*base82 + (4958521/1250000000000000000000 : ℝ)*base89 + (4958521/1250000000000000000000 : ℝ)*base91 + (4958521/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23035809540146440715046459/2148437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (99089601/5000000000000 : ℝ)*(base19) + (2154837827/100000000000000 : ℝ)*(base23) + (215195127/100000000000000 : ℝ)*(upper3) + (39342113/50000000000000 : ℝ)*(lower4) + (218671337/100000000000000 : ℝ)*(upper5) + (1174114691856693/20000000000000 : ℝ)*(major0) + (1174114691856693/20000000000000 : ℝ)*(major1) + (1174114691856693/20000000000000 : ℝ)*(major2) + (13552478631/25000000000000 : ℝ)*(sp1) + (3642196627/6250000000000 : ℝ)*(sp2) + (3894714443068221/50000000000000 : ℝ)*(sp4) + (3894686347214949/50000000000000 : ℝ)*(sp5) + (3894684228076291/50000000000000 : ℝ)*(sp6) + (3951717675026399/100000000000000 : ℝ)*(sp7) + (3951717675026399/100000000000000 : ℝ)*(f.failure) + (3894714443068221/50000000000000 : ℝ)*(f.sum) + (1034063292651/171875000000000000000000000 : ℝ)*base65 + (63254836611063819/17187500000000000000000000000000 : ℝ)*base67 + (194299467246748681/17187500000000000000000000000000 : ℝ)*base70 + (203255192418876319/17187500000000000000000000000000 : ℝ)*base71 + (9225275297083/1375000000000000000000000000 : ℝ)*base73 + (19410129128251319/17187500000000000000000000000000 : ℝ)*base75 + (234732033831376319/17187500000000000000000000000000 : ℝ)*base77 + (86359357336063819/17187500000000000000000000000000 : ℝ)*base79 + (1812803425021/687500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (16280089/1250000000000000000000 : ℝ)*base90 + (16280089/1250000000000000000000 : ℝ)*base92 + (16280089/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1095_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1095_s8_0 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094784141/5000000000 : ℝ)*x 0 + (1078768641/2000000000 : ℝ)*x 1 + (5264977593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094784141/5000000000 : ℝ)^259 ≤ (13300279512393/100000000000000 : ℝ)^195 := by
    have hnat : (1094784141 : ℕ)^259*100000000000000^195 ≤ 13300279512393^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094784141 5000000000 13300279512393 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078768641/2000000000 : ℝ)^259 ≤ (22022974453003/50000000000000 : ℝ)^195 := by
    have hnat : (1078768641 : ℕ)^259*50000000000000^195 ≤ 22022974453003^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078768641 2000000000 22022974453003 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264977593/10000000000 : ℝ)^259 ≤ (2132688578271/5000000000000 : ℝ)^195 := by
    have hnat : (5264977593 : ℕ)^259*5000000000000^195 ≤ 2132688578271^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264977593 10000000000 2132688578271 5000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094784141/5000000000 : ℝ), (1078768641/2000000000 : ℝ), (5264977593/10000000000 : ℝ)] ![(13300279512393/100000000000000 : ℝ), (22022974453003/50000000000000 : ℝ), (2132688578271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094784141/5000000000 : ℝ)|^259 ≤ (13300279512393/100000000000000 : ℝ)^195
        have hw : |(-1094784141/5000000000 : ℝ)|=(1094784141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078768641/2000000000 : ℝ)|^259 ≤ (22022974453003/50000000000000 : ℝ)^195
        have hw : |(1078768641/2000000000 : ℝ)|=(1078768641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264977593/10000000000 : ℝ)|^259 ≤ (2132688578271/5000000000000 : ℝ)^195
        have hw : |(5264977593/10000000000 : ℝ)|=(5264977593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_1 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1068980711/2000000000 : ℝ)*x 0 + (-1127471443/5000000000 : ℝ)*x 1 + (2632488797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068980711/2000000000 : ℝ)^259 ≤ (43515937491733/100000000000000 : ℝ)^195 := by
    have hnat : (1068980711 : ℕ)^259*100000000000000^195 ≤ 43515937491733^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068980711 2000000000 43515937491733 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127471443/5000000000 : ℝ)^259 ≤ (3457572728993/25000000000000 : ℝ)^195 := by
    have hnat : (1127471443 : ℕ)^259*25000000000000^195 ≤ 3457572728993^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127471443 5000000000 3457572728993 25000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632488797/5000000000 : ℝ)^259 ≤ (42653771576181/100000000000000 : ℝ)^195 := by
    have hnat : (2632488797 : ℕ)^259*100000000000000^195 ≤ 42653771576181^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632488797 5000000000 42653771576181 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068980711/2000000000 : ℝ), (-1127471443/5000000000 : ℝ), (2632488797/5000000000 : ℝ)] ![(43515937491733/100000000000000 : ℝ), (3457572728993/25000000000000 : ℝ), (42653771576181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068980711/2000000000 : ℝ)|^259 ≤ (43515937491733/100000000000000 : ℝ)^195
        have hw : |(1068980711/2000000000 : ℝ)|=(1068980711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1127471443/5000000000 : ℝ)|^259 ≤ (3457572728993/25000000000000 : ℝ)^195
        have hw : |(-1127471443/5000000000 : ℝ)|=(1127471443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632488797/5000000000 : ℝ)|^259 ≤ (42653771576181/100000000000000 : ℝ)^195
        have hw : |(2632488797/5000000000 : ℝ)|=(2632488797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_2 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1068980711/2000000000 : ℝ)*x 0 + (2632488797/5000000000 : ℝ)*x 1 + (-450988577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068980711/2000000000 : ℝ)^259 ≤ (43515937491733/100000000000000 : ℝ)^195 := by
    have hnat : (1068980711 : ℕ)^259*100000000000000^195 ≤ 43515937491733^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068980711 2000000000 43515937491733 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632488797/5000000000 : ℝ)^259 ≤ (42653771576181/100000000000000 : ℝ)^195 := by
    have hnat : (2632488797 : ℕ)^259*100000000000000^195 ≤ 42653771576181^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632488797 5000000000 42653771576181 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450988577/2000000000 : ℝ)^259 ≤ (6915145453913/50000000000000 : ℝ)^195 := by
    have hnat : (450988577 : ℕ)^259*50000000000000^195 ≤ 6915145453913^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450988577 2000000000 6915145453913 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068980711/2000000000 : ℝ), (2632488797/5000000000 : ℝ), (-450988577/2000000000 : ℝ)] ![(43515937491733/100000000000000 : ℝ), (42653771576181/100000000000000 : ℝ), (6915145453913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068980711/2000000000 : ℝ)|^259 ≤ (43515937491733/100000000000000 : ℝ)^195
        have hw : |(1068980711/2000000000 : ℝ)|=(1068980711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632488797/5000000000 : ℝ)|^259 ≤ (42653771576181/100000000000000 : ℝ)^195
        have hw : |(2632488797/5000000000 : ℝ)|=(2632488797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-450988577/2000000000 : ℝ)|^259 ≤ (6915145453913/50000000000000 : ℝ)^195
        have hw : |(-450988577/2000000000 : ℝ)|=(450988577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_3 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2185669099/5000000000 : ℝ)*x 0 + (849237577/2000000000 : ℝ)*x 1 + (1125050341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185669099/5000000000 : ℝ)^259 ≤ (520573719603/1562500000000 : ℝ)^195 := by
    have hnat : (2185669099 : ℕ)^259*1562500000000^195 ≤ 520573719603^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185669099 5000000000 520573719603 1562500000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849237577/2000000000 : ℝ)^259 ≤ (3205580140759/10000000000000 : ℝ)^195 := by
    have hnat : (849237577 : ℕ)^259*10000000000000^195 ≤ 3205580140759^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849237577 2000000000 3205580140759 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125050341/2500000000 : ℝ)^259 ≤ (34627480521909/100000000000000 : ℝ)^195 := by
    have hnat : (1125050341 : ℕ)^259*100000000000000^195 ≤ 34627480521909^195*2500000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125050341 2500000000 34627480521909 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185669099/5000000000 : ℝ), (849237577/2000000000 : ℝ), (1125050341/2500000000 : ℝ)] ![(520573719603/1562500000000 : ℝ), (3205580140759/10000000000000 : ℝ), (34627480521909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185669099/5000000000 : ℝ)|^259 ≤ (520573719603/1562500000000 : ℝ)^195
        have hw : |(2185669099/5000000000 : ℝ)|=(2185669099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849237577/2000000000 : ℝ)|^259 ≤ (3205580140759/10000000000000 : ℝ)^195
        have hw : |(849237577/2000000000 : ℝ)|=(849237577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125050341/2500000000 : ℝ)|^259 ≤ (34627480521909/100000000000000 : ℝ)^195
        have hw : |(1125050341/2500000000 : ℝ)|=(1125050341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_4 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1094786653/5000000000 : ℝ)*x 0 + (2632650319/5000000000 : ℝ)*x 1 + (539351897/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094786653/5000000000 : ℝ)^259 ≤ (1662540005773/12500000000000 : ℝ)^195 := by
    have hnat : (1094786653 : ℕ)^259*12500000000000^195 ≤ 1662540005773^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094786653 5000000000 1662540005773 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632650319/5000000000 : ℝ)^259 ≤ (5332155959377/12500000000000 : ℝ)^195 := by
    have hnat : (2632650319 : ℕ)^259*12500000000000^195 ≤ 5332155959377^195*5000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632650319 5000000000 5332155959377 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539351897/1000000000 : ℝ)^259 ≤ (4404243226193/10000000000000 : ℝ)^195 := by
    have hnat : (539351897 : ℕ)^259*10000000000000^195 ≤ 4404243226193^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539351897 1000000000 4404243226193 10000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1094786653/5000000000 : ℝ), (2632650319/5000000000 : ℝ), (539351897/1000000000 : ℝ)] ![(1662540005773/12500000000000 : ℝ), (5332155959377/12500000000000 : ℝ), (4404243226193/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1094786653/5000000000 : ℝ)|^259 ≤ (1662540005773/12500000000000 : ℝ)^195
        have hw : |(-1094786653/5000000000 : ℝ)|=(1094786653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632650319/5000000000 : ℝ)|^259 ≤ (5332155959377/12500000000000 : ℝ)^195
        have hw : |(2632650319/5000000000 : ℝ)|=(2632650319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539351897/1000000000 : ℝ)|^259 ≤ (4404243226193/10000000000000 : ℝ)^195
        have hw : |(539351897/1000000000 : ℝ)|=(539351897/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_5 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (664046369/1250000000 : ℝ)*x 0 + (-2126401297/10000000000 : ℝ)*x 1 + (5393519031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664046369/1250000000 : ℝ)^259 ≤ (21582246056053/50000000000000 : ℝ)^195 := by
    have hnat : (664046369 : ℕ)^259*50000000000000^195 ≤ 21582246056053^195*1250000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664046369 1250000000 21582246056053 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126401297/10000000000 : ℝ)^259 ≤ (12793074957307/100000000000000 : ℝ)^195 := by
    have hnat : (2126401297 : ℕ)^259*100000000000000^195 ≤ 12793074957307^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126401297 10000000000 12793074957307 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393519031/10000000000 : ℝ)^259 ≤ (5505304115441/12500000000000 : ℝ)^195 := by
    have hnat : (5393519031 : ℕ)^259*12500000000000^195 ≤ 5505304115441^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393519031 10000000000 5505304115441 12500000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664046369/1250000000 : ℝ), (-2126401297/10000000000 : ℝ), (5393519031/10000000000 : ℝ)] ![(21582246056053/50000000000000 : ℝ), (12793074957307/100000000000000 : ℝ), (5505304115441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664046369/1250000000 : ℝ)|^259 ≤ (21582246056053/50000000000000 : ℝ)^195
        have hw : |(664046369/1250000000 : ℝ)|=(664046369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126401297/10000000000 : ℝ)|^259 ≤ (12793074957307/100000000000000 : ℝ)^195
        have hw : |(-2126401297/10000000000 : ℝ)|=(2126401297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393519031/10000000000 : ℝ)|^259 ≤ (5505304115441/12500000000000 : ℝ)^195
        have hw : |(5393519031/10000000000 : ℝ)|=(5393519031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_6 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5312370637/10000000000 : ℝ)*x 0 + (5393519051/10000000000 : ℝ)*x 1 + (-425280339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312370637/10000000000 : ℝ)^259 ≤ (21582244356307/50000000000000 : ℝ)^195 := by
    have hnat : (5312370637 : ℕ)^259*50000000000000^195 ≤ 21582244356307^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312370637 10000000000 21582244356307 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393519051/10000000000 : ℝ)^259 ≤ (8808486628089/20000000000000 : ℝ)^195 := by
    have hnat : (5393519051 : ℕ)^259*20000000000000^195 ≤ 8808486628089^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393519051 10000000000 8808486628089 20000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425280339/2000000000 : ℝ)^259 ≤ (12793078137679/100000000000000 : ℝ)^195 := by
    have hnat : (425280339 : ℕ)^259*100000000000000^195 ≤ 12793078137679^195*2000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425280339 2000000000 12793078137679 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312370637/10000000000 : ℝ), (5393519051/10000000000 : ℝ), (-425280339/2000000000 : ℝ)] ![(21582244356307/50000000000000 : ℝ), (8808486628089/20000000000000 : ℝ), (12793078137679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312370637/10000000000 : ℝ)|^259 ≤ (21582244356307/50000000000000 : ℝ)^195
        have hw : |(5312370637/10000000000 : ℝ)|=(5312370637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393519051/10000000000 : ℝ)|^259 ≤ (8808486628089/20000000000000 : ℝ)^195
        have hw : |(5393519051/10000000000 : ℝ)|=(5393519051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425280339/2000000000 : ℝ)|^259 ≤ (12793078137679/100000000000000 : ℝ)^195
        have hw : |(-425280339/2000000000 : ℝ)|=(425280339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1095_s8_7 (p : ℝ) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4371347857/10000000000 : ℝ)*x 0 + (4499564517/10000000000 : ℝ)*x 1 + (424682721/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371347857/10000000000 : ℝ)^259 ≤ (16658407916761/50000000000000 : ℝ)^195 := by
    have hnat : (4371347857 : ℕ)^259*50000000000000^195 ≤ 16658407916761^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371347857 10000000000 16658407916761 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499564517/10000000000 : ℝ)^259 ≤ (34620972048713/100000000000000 : ℝ)^195 := by
    have hnat : (4499564517 : ℕ)^259*100000000000000^195 ≤ 34620972048713^195*10000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499564517 10000000000 34620972048713 100000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424682721/1000000000 : ℝ)^259 ≤ (16031106050461/50000000000000 : ℝ)^195 := by
    have hnat : (424682721 : ℕ)^259*50000000000000^195 ≤ 16031106050461^195*1000000000^259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424682721 1000000000 16031106050461 50000000000000 259 195 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (259/64 : ℝ)) 259 195 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371347857/10000000000 : ℝ), (4499564517/10000000000 : ℝ), (424682721/1000000000 : ℝ)] ![(16658407916761/50000000000000 : ℝ), (34620972048713/100000000000000 : ℝ), (16031106050461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371347857/10000000000 : ℝ)|^259 ≤ (16658407916761/50000000000000 : ℝ)^195
        have hw : |(4371347857/10000000000 : ℝ)|=(4371347857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499564517/10000000000 : ℝ)|^259 ≤ (34620972048713/100000000000000 : ℝ)^195
        have hw : |(4499564517/10000000000 : ℝ)|=(4499564517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424682721/1000000000 : ℝ)|^259 ≤ (16031106050461/50000000000000 : ℝ)^195
        have hw : |(424682721/1000000000 : ℝ)|=(424682721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1095_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11291/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11289/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (14678365173455667/100000000000000000000 : ℝ) := by
    have hpowers : (11289/100000 : ℝ)^8287 ≤ (14678365173455667/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11289 : ℕ)^8287*100000000000000000000^2048 ≤ 14678365173455667^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11289 100000 14678365173455667 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11289/100000 : ℝ)) (X := (14678365173455667/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14023/100000 : ℝ) ^ (8287/2048 : ℝ) ≤ (35301120163714007/100000000000000000000 : ℝ) := by
    have hpowers : (14023/100000 : ℝ)^8287 ≤ (35301120163714007/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14023 : ℕ)^8287*100000000000000000000^2048 ≤ 35301120163714007^2048*100000^8287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14023 100000 35301120163714007 100000000000000000000 8287 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14023/100000 : ℝ)) (X := (35301120163714007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014678365173455667/50000000000000000000 : ℝ) ≤ (80005803397209/80000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50014678365173455667/50000000000000000000 : ℝ)^2048 ≤ (80005803397209/80000000000000 : ℝ)^8287 := by
      have hnat : (50014678365173455667 : ℕ)^2048*80000000000000^8287 ≤ 80005803397209^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014678365173455667 50000000000000000000 80005803397209 80000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80005803397209/80000000000000 : ℝ)) (X := (50014678365173455667/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024989742668584837/50000000000000000000 : ℝ) ≤ (5000617465512469/5000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50024989742668584837/50000000000000000000 : ℝ)^2048 ≤ (5000617465512469/5000000000000000 : ℝ)^8287 := by
      have hnat : (50024989742668584837 : ℕ)^2048*5000000000000000^8287 ≤ 5000617465512469^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024989742668584837 50000000000000000000 5000617465512469 5000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000617465512469/5000000000000000 : ℝ)) (X := (50024989742668584837/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035301120163714007/50000000000000000000 : ℝ) ≤ (10001744437398751/10000000000000000 : ℝ) ^ (8287/2048 : ℝ) := by
    have hpowers : (50035301120163714007/50000000000000000000 : ℝ)^2048 ≤ (10001744437398751/10000000000000000 : ℝ)^8287 := by
      have hnat : (50035301120163714007 : ℕ)^2048*10000000000000000^8287 ≤ 10001744437398751^8287*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035301120163714007 50000000000000000000 10001744437398751 10000000000000000 2048 8287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001744437398751/10000000000000000 : ℝ)) (X := (50035301120163714007/50000000000000000000 : ℝ)) (by norm_num) 8287 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14678365173455667/100000000000000000000 : ℝ) ≤ ((6832619919022056459/6835000000000000000 : ℝ)+2*(509506373813/273400000000000 : ℝ)*(11289/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (6832619919022056459/6835000000000000000 : ℝ)+2*(509506373813/273400000000000 : ℝ)*(11289/100000 : ℝ)=(80005803397209/80000000000000 : ℝ) by norm_num, show 1+2*(14678365173455667/100000000000000000000 : ℝ)=(50014678365173455667/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35301120163714007/100000000000000000000 : ℝ)+(14678365173455667/100000000000000000000 : ℝ) ≤ ((6832619919022056459/6835000000000000000 : ℝ)+(509506373813/273400000000000 : ℝ)*((14023/100000 : ℝ)+(11289/100000 : ℝ)))^(8287/2048 : ℝ) := by
    rw [show (6832619919022056459/6835000000000000000 : ℝ)+(509506373813/273400000000000 : ℝ)*((14023/100000 : ℝ)+(11289/100000 : ℝ))=(5000617465512469/5000000000000000 : ℝ) by norm_num, show 1+(35301120163714007/100000000000000000000 : ℝ)+(14678365173455667/100000000000000000000 : ℝ)=(50024989742668584837/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35301120163714007/100000000000000000000 : ℝ) ≤ ((6832619919022056459/6835000000000000000 : ℝ)+2*(509506373813/273400000000000 : ℝ)*(14023/100000 : ℝ))^(8287/2048 : ℝ) := by
    rw [show (6832619919022056459/6835000000000000000 : ℝ)+2*(509506373813/273400000000000 : ℝ)*(14023/100000 : ℝ)=(10001744437398751/10000000000000000 : ℝ) by norm_num, show 1+2*(35301120163714007/100000000000000000000 : ℝ)=(50035301120163714007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6832619919022056459/6835000000000000000 : ℝ)*(X 1 0+X 2 0)+(509506373813/273400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (6832619919022056459/6835000000000000000 : ℝ)) (alpha := (509506373813/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6832619919022056459/6835000000000000000 : ℝ)*(X 0 1+X 2 1)+(509506373813/273400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (6832619919022056459/6835000000000000000 : ℝ)) (alpha := (509506373813/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6832619919022056459/6835000000000000000 : ℝ)*(X 0 2+X 1 2)+(509506373813/273400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8287/2048 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (6832619919022056459/6835000000000000000 : ℝ)) (alpha := (509506373813/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1094784141/5000000000 : ℝ)*X 0 0+(1078768641/2000000000 : ℝ)*X 0 1+(5264977593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068980711/2000000000 : ℝ)*X 1 0+(-1127471443/5000000000 : ℝ)*X 1 1+(2632488797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068980711/2000000000 : ℝ)*X 2 0+(2632488797/5000000000 : ℝ)*X 2 1+(-450988577/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185669099/5000000000 : ℝ)*X 0 0+(849237577/2000000000 : ℝ)*X 0 1+(1125050341/2500000000 : ℝ)*X 0 2+(2185669099/5000000000 : ℝ)*X 1 0+(849237577/2000000000 : ℝ)*X 1 1+(1125050341/2500000000 : ℝ)*X 1 2+(2185669099/5000000000 : ℝ)*X 2 0+(849237577/2000000000 : ℝ)*X 2 1+(1125050341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1094786653/5000000000 : ℝ)*X 0 0+(2632650319/5000000000 : ℝ)*X 0 1+(539351897/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664046369/1250000000 : ℝ)*X 1 0+(-2126401297/10000000000 : ℝ)*X 1 1+(5393519031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312370637/10000000000 : ℝ)*X 2 0+(5393519051/10000000000 : ℝ)*X 2 1+(-425280339/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371347857/10000000000 : ℝ)*X 0 0+(4499564517/10000000000 : ℝ)*X 0 1+(424682721/1000000000 : ℝ)*X 0 2+(4371347857/10000000000 : ℝ)*X 1 0+(4499564517/10000000000 : ℝ)*X 1 1+(424682721/1000000000 : ℝ)*X 1 2+(4371347857/10000000000 : ℝ)*X 2 0+(4499564517/10000000000 : ℝ)*X 2 1+(424682721/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1095_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1394803774162150235468664927/170875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (203753943/12500000000000 : ℝ)*(base19) + (303658283/20000000000000 : ℝ)*(base23) + (59724023/100000000000000 : ℝ)*(lower2) + (41269313/20000000000000 : ℝ)*(upper3) + (124245879/100000000000000 : ℝ)*(upper5) + (2924239332167849/50000000000000 : ℝ)*(major0) + (2924239332167849/50000000000000 : ℝ)*(major1) + (2924239332167849/50000000000000 : ℝ)*(major2) + (3880034109543353/50000000000000 : ℝ)*(sp0) + (7760110641254569/100000000000000 : ℝ)*(sp1) + (7760110752994697/100000000000000 : ℝ)*(sp2) + (984205169201771/25000000000000 : ℝ)*(sp3) + (44052199407/100000000000000 : ℝ)*(sp4) + (24108487717/100000000000000 : ℝ)*(sp7) + (3936844785294801/100000000000000 : ℝ)*(f.failure) + (7760112271286113/100000000000000 : ℝ)*(f.sum) + (17756688545927/1708750000000000000000000000 : ℝ)*base66 + (1781519181004761691/341750000000000000000000000000000 : ℝ)*base67 + (2812216710250988309/341750000000000000000000000000000 : ℝ)*base70 + (363676487459488309/341750000000000000000000000000000 : ℝ)*base72 + (2927650516193/427187500000000000000000000 : ℝ)*base74 + (6092524656137511691/341750000000000000000000000000000 : ℝ)*base75 + (7365561927620511691/341750000000000000000000000000000 : ℝ)*base77 + (7023429471436261691/341750000000000000000000000000000 : ℝ)*base79 + (39210711677049/3417500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2886889/1250000000000000000000 : ℝ)*base89 + (2886889/1250000000000000000000 : ℝ)*base91 + (2886889/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (609806460692299349451430569/68350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1749453983/100000000000000 : ℝ)*(base19) + (1159376193/100000000000000 : ℝ)*(base23) + (31301911/100000000000000 : ℝ)*(upper2) + (10663159/10000000000000 : ℝ)*(upper3) + (207385191/100000000000000 : ℝ)*(upper5) + (1175586606037699/20000000000000 : ℝ)*(major0) + (1175586606037699/20000000000000 : ℝ)*(major1) + (1175586606037699/20000000000000 : ℝ)*(major2) + (29050015297/50000000000000 : ℝ)*(sp1) + (27638460353/100000000000000 : ℝ)*(sp2) + (31196776266309/400000000000 : ℝ)*(sp4) + (3899567108546337/50000000000000 : ℝ)*(sp5) + (1559833053748141/20000000000000 : ℝ)*(sp6) + (61822995256339/1562500000000 : ℝ)*(sp7) + (61822995256339/1562500000000 : ℝ)*(f.failure) + (31196776266309/400000000000 : ℝ)*(f.sum) + (1713319417161/2734000000000000000000000000 : ℝ)*base66 + (478374391116777159/136700000000000000000000000000000 : ℝ)*base68 + (3194691744154377159/136700000000000000000000000000000 : ℝ)*base70 + (1562936669925377159/136700000000000000000000000000000 : ℝ)*base72 + (1296470259293/2734000000000000000000000000 : ℝ)*base74 + (3193154857495377159/136700000000000000000000000000000 : ℝ)*base76 + (189917315354777159/136700000000000000000000000000000 : ℝ)*base78 + (4510712187044677159/136700000000000000000000000000000 : ℝ)*base80 + (22401633592233/2734000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (157767/39062500000000000000 : ℝ)*base89 + (157767/39062500000000000000 : ℝ)*base91 + (157767/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1095_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1095_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1095_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1095_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1095_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1095_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8287/2048 : ℝ) ≤ p) (hpb : p ≤ (259/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18569689/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1095_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

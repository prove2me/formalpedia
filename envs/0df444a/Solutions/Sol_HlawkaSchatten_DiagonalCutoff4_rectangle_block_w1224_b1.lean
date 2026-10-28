-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:21.08789+00:00
-- url     : https://prove2.me/submissions/6f5be320-c001-4641-bb4d-d8238b96e347

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
theorem support_rectangle_w1224_s3_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125280237/10000000000 : ℝ)*x 0 + (5421266581/10000000000 : ℝ)*x 1 + (2619600119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125280237/10000000000 : ℝ)^8417 ≤ (6458204816271/50000000000000 : ℝ)^6369 := by
    have hnat : (2125280237 : ℕ)^8417*50000000000000^6369 ≤ 6458204816271^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125280237 10000000000 6458204816271 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421266581/10000000000 : ℝ)^8417 ≤ (4452448018963/10000000000000 : ℝ)^6369 := by
    have hnat : (5421266581 : ℕ)^8417*10000000000000^6369 ≤ 4452448018963^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421266581 10000000000 4452448018963 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619600119/5000000000 : ℝ)^8417 ≤ (42559110160913/100000000000000 : ℝ)^6369 := by
    have hnat : (2619600119 : ℕ)^8417*100000000000000^6369 ≤ 42559110160913^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619600119 5000000000 42559110160913 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125280237/10000000000 : ℝ), (5421266581/10000000000 : ℝ), (2619600119/5000000000 : ℝ)] ![(6458204816271/50000000000000 : ℝ), (4452448018963/10000000000000 : ℝ), (42559110160913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125280237/10000000000 : ℝ)|^8417 ≤ (6458204816271/50000000000000 : ℝ)^6369
        have hw : |(-2125280237/10000000000 : ℝ)|=(2125280237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421266581/10000000000 : ℝ)|^8417 ≤ (4452448018963/10000000000000 : ℝ)^6369
        have hw : |(5421266581/10000000000 : ℝ)|=(5421266581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619600119/5000000000 : ℝ)|^8417 ≤ (42559110160913/100000000000000 : ℝ)^6369
        have hw : |(2619600119/5000000000 : ℝ)|=(2619600119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337972953/2500000000 : ℝ)*x 0 + (-2218190647/10000000000 : ℝ)*x 1 + (1047840053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337972953/2500000000 : ℝ)^8417 ≤ (10943262492169/25000000000000 : ℝ)^6369 := by
    have hnat : (1337972953 : ℕ)^8417*25000000000000^6369 ≤ 10943262492169^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337972953 2500000000 10943262492169 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218190647/10000000000 : ℝ)^8417 ≤ (427119986371/3125000000000 : ℝ)^6369 := by
    have hnat : (2218190647 : ℕ)^8417*3125000000000^6369 ≤ 427119986371^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218190647 10000000000 427119986371 3125000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047840053/2000000000 : ℝ)^8417 ≤ (8511822090153/20000000000000 : ℝ)^6369 := by
    have hnat : (1047840053 : ℕ)^8417*20000000000000^6369 ≤ 8511822090153^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047840053 2000000000 8511822090153 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337972953/2500000000 : ℝ), (-2218190647/10000000000 : ℝ), (1047840053/2000000000 : ℝ)] ![(10943262492169/25000000000000 : ℝ), (427119986371/3125000000000 : ℝ), (8511822090153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337972953/2500000000 : ℝ)|^8417 ≤ (10943262492169/25000000000000 : ℝ)^6369
        have hw : |(1337972953/2500000000 : ℝ)|=(1337972953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2218190647/10000000000 : ℝ)|^8417 ≤ (427119986371/3125000000000 : ℝ)^6369
        have hw : |(-2218190647/10000000000 : ℝ)|=(2218190647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047840053/2000000000 : ℝ)|^8417 ≤ (8511822090153/20000000000000 : ℝ)^6369
        have hw : |(1047840053/2000000000 : ℝ)|=(1047840053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267594589/500000000 : ℝ)*x 0 + (5239200437/10000000000 : ℝ)*x 1 + (-17329613/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267594589/500000000 : ℝ)^8417 ≤ (10943262405697/25000000000000 : ℝ)^6369 := by
    have hnat : (267594589 : ℕ)^8417*25000000000000^6369 ≤ 10943262405697^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267594589 500000000 10943262405697 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239200437/10000000000 : ℝ)^8417 ≤ (8511822459447/20000000000000 : ℝ)^6369 := by
    have hnat : (5239200437 : ℕ)^8417*20000000000000^6369 ≤ 8511822459447^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239200437 10000000000 8511822459447 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17329613/78125000 : ℝ)^8417 ≤ (6833919036847/50000000000000 : ℝ)^6369 := by
    have hnat : (17329613 : ℕ)^8417*50000000000000^6369 ≤ 6833919036847^6369*78125000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17329613 78125000 6833919036847 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267594589/500000000 : ℝ), (5239200437/10000000000 : ℝ), (-17329613/78125000 : ℝ)] ![(10943262405697/25000000000000 : ℝ), (8511822459447/20000000000000 : ℝ), (6833919036847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267594589/500000000 : ℝ)|^8417 ≤ (10943262405697/25000000000000 : ℝ)^6369
        have hw : |(267594589/500000000 : ℝ)|=(267594589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239200437/10000000000 : ℝ)|^8417 ≤ (8511822459447/20000000000000 : ℝ)^6369
        have hw : |(5239200437/10000000000 : ℝ)|=(5239200437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17329613/78125000 : ℝ)|^8417 ≤ (6833919036847/50000000000000 : ℝ)^6369
        have hw : |(-17329613/78125000 : ℝ)|=(17329613/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351459291/10000000000 : ℝ)*x 0 + (417122879/1000000000 : ℝ)*x 1 + (2269639751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351459291/10000000000 : ℝ)^8417 ≤ (16649655930569/50000000000000 : ℝ)^6369 := by
    have hnat : (4351459291 : ℕ)^8417*50000000000000^6369 ≤ 16649655930569^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351459291 10000000000 16649655930569 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417122879/1000000000 : ℝ)^8417 ≤ (7872216836293/25000000000000 : ℝ)^6369 := by
    have hnat : (417122879 : ℕ)^8417*25000000000000^6369 ≤ 7872216836293^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417122879 1000000000 7872216836293 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269639751/5000000000 : ℝ)^8417 ≤ (35211820779639/100000000000000 : ℝ)^6369 := by
    have hnat : (2269639751 : ℕ)^8417*100000000000000^6369 ≤ 35211820779639^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269639751 5000000000 35211820779639 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351459291/10000000000 : ℝ), (417122879/1000000000 : ℝ), (2269639751/5000000000 : ℝ)] ![(16649655930569/50000000000000 : ℝ), (7872216836293/25000000000000 : ℝ), (35211820779639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351459291/10000000000 : ℝ)|^8417 ≤ (16649655930569/50000000000000 : ℝ)^6369
        have hw : |(4351459291/10000000000 : ℝ)|=(4351459291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417122879/1000000000 : ℝ)|^8417 ≤ (7872216836293/25000000000000 : ℝ)^6369
        have hw : |(417122879/1000000000 : ℝ)|=(417122879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269639751/5000000000 : ℝ)|^8417 ≤ (35211820779639/100000000000000 : ℝ)^6369
        have hw : |(2269639751/5000000000 : ℝ)|=(2269639751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42505899/200000000 : ℝ)*x 0 + (5239869237/10000000000 : ℝ)*x 1 + (677574247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42505899/200000000 : ℝ)^8417 ≤ (12916527804221/100000000000000 : ℝ)^6369 := by
    have hnat : (42505899 : ℕ)^8417*100000000000000^6369 ≤ 12916527804221^6369*200000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42505899 200000000 12916527804221 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239869237/10000000000 : ℝ)^8417 ≤ (4256629220397/10000000000000 : ℝ)^6369 := by
    have hnat : (5239869237 : ℕ)^8417*10000000000000^6369 ≤ 4256629220397^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239869237 10000000000 4256629220397 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677574247/1250000000 : ℝ)^8417 ≤ (44517179975471/100000000000000 : ℝ)^6369 := by
    have hnat : (677574247 : ℕ)^8417*100000000000000^6369 ≤ 44517179975471^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677574247 1250000000 44517179975471 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42505899/200000000 : ℝ), (5239869237/10000000000 : ℝ), (677574247/1250000000 : ℝ)] ![(12916527804221/100000000000000 : ℝ), (4256629220397/10000000000000 : ℝ), (44517179975471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42505899/200000000 : ℝ)|^8417 ≤ (12916527804221/100000000000000 : ℝ)^6369
        have hw : |(-42505899/200000000 : ℝ)|=(42505899/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239869237/10000000000 : ℝ)|^8417 ≤ (4256629220397/10000000000000 : ℝ)^6369
        have hw : |(5239869237/10000000000 : ℝ)|=(5239869237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677574247/1250000000 : ℝ)|^8417 ≤ (44517179975471/100000000000000 : ℝ)^6369
        have hw : |(677574247/1250000000 : ℝ)|=(677574247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305498941/10000000000 : ℝ)*x 0 + (-2036796887/10000000000 : ℝ)*x 1 + (2710296831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305498941/10000000000 : ℝ)^8417 ≤ (43272289641577/100000000000000 : ℝ)^6369 := by
    have hnat : (5305498941 : ℕ)^8417*100000000000000^6369 ≤ 43272289641577^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305498941 10000000000 43272289641577 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036796887/10000000000 : ℝ)^8417 ≤ (244210675467/2000000000000 : ℝ)^6369 := by
    have hnat : (2036796887 : ℕ)^8417*2000000000000^6369 ≤ 244210675467^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036796887 10000000000 244210675467 2000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710296831/5000000000 : ℝ)^8417 ≤ (5564647070937/12500000000000 : ℝ)^6369 := by
    have hnat : (2710296831 : ℕ)^8417*12500000000000^6369 ≤ 5564647070937^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710296831 5000000000 5564647070937 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305498941/10000000000 : ℝ), (-2036796887/10000000000 : ℝ), (2710296831/5000000000 : ℝ)] ![(43272289641577/100000000000000 : ℝ), (244210675467/2000000000000 : ℝ), (5564647070937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305498941/10000000000 : ℝ)|^8417 ≤ (43272289641577/100000000000000 : ℝ)^6369
        have hw : |(5305498941/10000000000 : ℝ)|=(5305498941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036796887/10000000000 : ℝ)|^8417 ≤ (244210675467/2000000000000 : ℝ)^6369
        have hw : |(-2036796887/10000000000 : ℝ)|=(2036796887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710296831/5000000000 : ℝ)|^8417 ≤ (5564647070937/12500000000000 : ℝ)^6369
        have hw : |(2710296831/5000000000 : ℝ)|=(2710296831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061099737/2000000000 : ℝ)*x 0 + (2710296829/5000000000 : ℝ)*x 1 + (-2036797241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061099737/2000000000 : ℝ)^8417 ≤ (1352258965069/3125000000000 : ℝ)^6369 := by
    have hnat : (1061099737 : ℕ)^8417*3125000000000^6369 ≤ 1352258965069^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061099737 2000000000 1352258965069 3125000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710296829/5000000000 : ℝ)^8417 ≤ (22258588262041/50000000000000 : ℝ)^6369 := by
    have hnat : (2710296829 : ℕ)^8417*50000000000000^6369 ≤ 22258588262041^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710296829 5000000000 22258588262041 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2036797241/10000000000 : ℝ)^8417 ≤ (2442107315597/20000000000000 : ℝ)^6369 := by
    have hnat : (2036797241 : ℕ)^8417*20000000000000^6369 ≤ 2442107315597^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036797241 10000000000 2442107315597 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061099737/2000000000 : ℝ), (2710296829/5000000000 : ℝ), (-2036797241/10000000000 : ℝ)] ![(1352258965069/3125000000000 : ℝ), (22258588262041/50000000000000 : ℝ), (2442107315597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061099737/2000000000 : ℝ)|^8417 ≤ (1352258965069/3125000000000 : ℝ)^6369
        have hw : |(1061099737/2000000000 : ℝ)|=(1061099737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710296829/5000000000 : ℝ)|^8417 ≤ (22258588262041/50000000000000 : ℝ)^6369
        have hw : |(2710296829/5000000000 : ℝ)|=(2710296829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2036797241/10000000000 : ℝ)|^8417 ≤ (2442107315597/20000000000000 : ℝ)^6369
        have hw : |(-2036797241/10000000000 : ℝ)|=(2036797241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s3_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217574453/500000000 : ℝ)*x 0 + (1134481653/2500000000 : ℝ)*x 1 + (834517731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217574453/500000000 : ℝ)^8417 ≤ (16649806459903/50000000000000 : ℝ)^6369 := by
    have hnat : (217574453 : ℕ)^8417*50000000000000^6369 ≤ 16649806459903^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217574453 500000000 16649806459903 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134481653/2500000000 : ℝ)^8417 ≤ (3519795228541/10000000000000 : ℝ)^6369 := by
    have hnat : (1134481653 : ℕ)^8417*10000000000000^6369 ≤ 3519795228541^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134481653 2500000000 3519795228541 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834517731/2000000000 : ℝ)^8417 ≤ (6300486955499/20000000000000 : ℝ)^6369 := by
    have hnat : (834517731 : ℕ)^8417*20000000000000^6369 ≤ 6300486955499^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834517731 2000000000 6300486955499 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217574453/500000000 : ℝ), (1134481653/2500000000 : ℝ), (834517731/2000000000 : ℝ)] ![(16649806459903/50000000000000 : ℝ), (3519795228541/10000000000000 : ℝ), (6300486955499/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217574453/500000000 : ℝ)|^8417 ≤ (16649806459903/50000000000000 : ℝ)^6369
        have hw : |(217574453/500000000 : ℝ)|=(217574453/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134481653/2500000000 : ℝ)|^8417 ≤ (3519795228541/10000000000000 : ℝ)^6369
        have hw : |(1134481653/2500000000 : ℝ)|=(1134481653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834517731/2000000000 : ℝ)|^8417 ≤ (6300486955499/20000000000000 : ℝ)^6369
        have hw : |(834517731/2000000000 : ℝ)|=(834517731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (679/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7359/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (377/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (377/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (377/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (377/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (377/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (377/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (377/4000 : ℝ) ^ (263/64 : ℝ) ≤ (3047245633998931/50000000000000000000 : ℝ) := by
    have hpowers : (377/4000 : ℝ)^263 ≤ (3047245633998931/50000000000000000000 : ℝ)^64 := by
      have hnat : (377 : ℕ)^263*50000000000000000000^64 ≤ 3047245633998931^64*4000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        377 4000 3047245633998931 50000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (377/4000 : ℝ)) (X := (3047245633998931/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (16271/100000 : ℝ) ^ (263/64 : ℝ) ≤ (28732632472412137/50000000000000000000 : ℝ) := by
    have hpowers : (16271/100000 : ℝ)^263 ≤ (28732632472412137/50000000000000000000 : ℝ)^64 := by
      have hnat : (16271 : ℕ)^263*50000000000000000000^64 ≤ 28732632472412137^64*100000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16271 100000 28732632472412137 50000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16271/100000 : ℝ)) (X := (28732632472412137/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25003047245633998931/25000000000000000000 : ℝ) ≤ (625018537521659/625000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (25003047245633998931/25000000000000000000 : ℝ)^64 ≤ (625018537521659/625000000000000 : ℝ)^263 := by
      have hnat : (25003047245633998931 : ℕ)^64*625000000000000^263 ≤ 625018537521659^263*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003047245633998931 25000000000000000000 625018537521659 625000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625018537521659/625000000000000 : ℝ)) (X := (25003047245633998931/25000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (12507944969526602767/12500000000000000000 : ℝ) ≤ (10001546329504691/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (12507944969526602767/12500000000000000000 : ℝ)^64 ≤ (10001546329504691/10000000000000000 : ℝ)^263 := by
      have hnat : (12507944969526602767 : ℕ)^64*10000000000000000^263 ≤ 10001546329504691^263*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507944969526602767 12500000000000000000 10001546329504691 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001546329504691/10000000000000000 : ℝ)) (X := (12507944969526602767/12500000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028732632472412137/25000000000000000000 : ℝ) ≤ (5001398029331419/5000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (25028732632472412137/25000000000000000000 : ℝ)^64 ≤ (5001398029331419/5000000000000000 : ℝ)^263 := by
      have hnat : (25028732632472412137 : ℕ)^64*5000000000000000^263 ≤ 5001398029331419^263*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028732632472412137 25000000000000000000 5001398029331419 5000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001398029331419/5000000000000000 : ℝ)) (X := (25028732632472412137/25000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3047245633998931/50000000000000000000 : ℝ) ≤ ((11406412188556894879/11410000000000000000 : ℝ)+2*(416576386049/228200000000000 : ℝ)*(377/4000 : ℝ))^(263/64 : ℝ) := by
    rw [show (11406412188556894879/11410000000000000000 : ℝ)+2*(416576386049/228200000000000 : ℝ)*(377/4000 : ℝ)=(625018537521659/625000000000000 : ℝ) by norm_num, show 1+2*(3047245633998931/50000000000000000000 : ℝ)=(25003047245633998931/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28732632472412137/50000000000000000000 : ℝ)+(3047245633998931/50000000000000000000 : ℝ) ≤ ((11406412188556894879/11410000000000000000 : ℝ)+(416576386049/228200000000000 : ℝ)*((16271/100000 : ℝ)+(377/4000 : ℝ)))^(263/64 : ℝ) := by
    rw [show (11406412188556894879/11410000000000000000 : ℝ)+(416576386049/228200000000000 : ℝ)*((16271/100000 : ℝ)+(377/4000 : ℝ))=(10001546329504691/10000000000000000 : ℝ) by norm_num, show 1+(28732632472412137/50000000000000000000 : ℝ)+(3047245633998931/50000000000000000000 : ℝ)=(12507944969526602767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28732632472412137/50000000000000000000 : ℝ) ≤ ((11406412188556894879/11410000000000000000 : ℝ)+2*(416576386049/228200000000000 : ℝ)*(16271/100000 : ℝ))^(263/64 : ℝ) := by
    rw [show (11406412188556894879/11410000000000000000 : ℝ)+2*(416576386049/228200000000000 : ℝ)*(16271/100000 : ℝ)=(5001398029331419/5000000000000000 : ℝ) by norm_num, show 1+2*(28732632472412137/50000000000000000000 : ℝ)=(25028732632472412137/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11406412188556894879/11410000000000000000 : ℝ)*(X 1 0+X 2 0)+(416576386049/228200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (377/4000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (11406412188556894879/11410000000000000000 : ℝ)) (alpha := (416576386049/228200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11406412188556894879/11410000000000000000 : ℝ)*(X 0 1+X 2 1)+(416576386049/228200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (377/4000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (11406412188556894879/11410000000000000000 : ℝ)) (alpha := (416576386049/228200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11406412188556894879/11410000000000000000 : ℝ)*(X 0 2+X 1 2)+(416576386049/228200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (377/4000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (11406412188556894879/11410000000000000000 : ℝ)) (alpha := (416576386049/228200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2125280237/10000000000 : ℝ)*X 0 0+(5421266581/10000000000 : ℝ)*X 0 1+(2619600119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337972953/2500000000 : ℝ)*X 1 0+(-2218190647/10000000000 : ℝ)*X 1 1+(1047840053/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267594589/500000000 : ℝ)*X 2 0+(5239200437/10000000000 : ℝ)*X 2 1+(-17329613/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351459291/10000000000 : ℝ)*X 0 0+(417122879/1000000000 : ℝ)*X 0 1+(2269639751/5000000000 : ℝ)*X 0 2+(4351459291/10000000000 : ℝ)*X 1 0+(417122879/1000000000 : ℝ)*X 1 1+(2269639751/5000000000 : ℝ)*X 1 2+(4351459291/10000000000 : ℝ)*X 2 0+(417122879/1000000000 : ℝ)*X 2 1+(2269639751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42505899/200000000 : ℝ)*X 0 0+(5239869237/10000000000 : ℝ)*X 0 1+(677574247/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305498941/10000000000 : ℝ)*X 1 0+(-2036796887/10000000000 : ℝ)*X 1 1+(2710296831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061099737/2000000000 : ℝ)*X 2 0+(2710296829/5000000000 : ℝ)*X 2 1+(-2036797241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217574453/500000000 : ℝ)*X 0 0+(1134481653/2500000000 : ℝ)*X 0 1+(834517731/2000000000 : ℝ)*X 0 2+(217574453/500000000 : ℝ)*X 1 0+(1134481653/2500000000 : ℝ)*X 1 1+(834517731/2000000000 : ℝ)*X 1 2+(217574453/500000000 : ℝ)*X 2 0+(1134481653/2500000000 : ℝ)*X 2 1+(834517731/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49561306853830071002559/5705000000000000000000000000 : ℝ) := by norm_num
    linear_combination (772750419/50000000000000 : ℝ)*(base19) + (329930321/25000000000000 : ℝ)*(base23) + (20651711/20000000000000 : ℝ)*(lower2) + (4462847/4000000000000 : ℝ)*(upper3) + (83940089/50000000000000 : ℝ)*(upper5) + (32068813973557/781250000000 : ℝ)*(major0) + (32068813973557/781250000000 : ℝ)*(major1) + (32068813973557/781250000000 : ℝ)*(major2) + (4291042592557/78125000000 : ℝ)*(sp0) + (5492568202455189/100000000000000 : ℝ)*(sp1) + (5492568428234743/100000000000000 : ℝ)*(sp2) + (2717031639319063/100000000000000 : ℝ)*(sp3) + (35229483067/100000000000000 : ℝ)*(sp4) + (3675094327/25000000000000 : ℝ)*(sp7) + (2717046339696371/100000000000000 : ℝ)*(f.failure) + (5492569747956027/100000000000000 : ℝ)*(f.sum) + (14002872279437/5705000000000000000000000000 : ℝ)*base65 + (101186249420098919/17828125000000000000000000000000 : ℝ)*base68 + (600470617754233/557128906250000000000000000000 : ℝ)*base69 + (81907331795348919/17828125000000000000000000000000 : ℝ)*base72 + (24748998235263/5705000000000000000000000000 : ℝ)*base74 + (164395610720744831/17828125000000000000000000000000 : ℝ)*base75 + (200751397141473919/17828125000000000000000000000000 : ℝ)*base78 + (161273647418463581/17828125000000000000000000000000 : ℝ)*base79 + (7881760509941/2852500000000000000000000000 : ℝ)*base81 + (2719013/250000000000000000000 : ℝ)*base89 + (2719013/250000000000000000000 : ℝ)*base91 + (2719013/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19101917739808973465763/2282000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2099368981/100000000000000 : ℝ)*(base19) + (474812659/25000000000000 : ℝ)*(base23) + (4611799/10000000000000 : ℝ)*(upper3) + (108543031/100000000000000 : ℝ)*(lower4) + (64314061/20000000000000 : ℝ)*(upper5) + (827046711420913/20000000000000 : ℝ)*(major0) + (827046711420913/20000000000000 : ℝ)*(major1) + (827046711420913/20000000000000 : ℝ)*(major2) + (20439645213/50000000000000 : ℝ)*(sp1) + (12565115823/50000000000000 : ℝ)*(sp2) + (5533281397074109/100000000000000 : ℝ)*(sp4) + (2766619209207351/50000000000000 : ℝ)*(sp5) + (5533254367591827/100000000000000 : ℝ)*(sp6) + (273718543811197/10000000000000 : ℝ)*(sp7) + (273718543811197/10000000000000 : ℝ)*(f.failure) + (5533281397074109/100000000000000 : ℝ)*(f.sum) + (980821923437/2282000000000000000000000000 : ℝ)*base65 + (1179203810538545473/228200000000000000000000000000000 : ℝ)*base68 + (729315566501254527/228200000000000000000000000000000 : ℝ)*base69 + (1275330828970745473/228200000000000000000000000000000 : ℝ)*base72 + (8977070036271/2282000000000000000000000000 : ℝ)*base74 + (412342519215254527/228200000000000000000000000000000 : ℝ)*base75 + (1925539920814945473/228200000000000000000000000000000 : ℝ)*base78 + (2416092293154454527/228200000000000000000000000000000 : ℝ)*base79 + (9083910346419/2282000000000000000000000000 : ℝ)*base81 + (132891/25000000000000000000 : ℝ)*base89 + (132891/25000000000000000000 : ℝ)*base91 + (132891/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1224_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1224_s4_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127686857/10000000000 : ℝ)*x 0 + (674779603/1250000000 : ℝ)*x 1 + (1052130691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127686857/10000000000 : ℝ)^8417 ≤ (6467871293929/50000000000000 : ℝ)^6369 := by
    have hnat : (2127686857 : ℕ)^8417*50000000000000^6369 ≤ 6467871293929^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127686857 10000000000 6467871293929 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674779603/1250000000 : ℝ)^8417 ≤ (44274689342743/100000000000000 : ℝ)^6369 := by
    have hnat : (674779603 : ℕ)^8417*100000000000000^6369 ≤ 44274689342743^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674779603 1250000000 44274689342743 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052130691/2000000000 : ℝ)^8417 ≤ (1337174001983/3125000000000 : ℝ)^6369 := by
    have hnat : (1052130691 : ℕ)^8417*3125000000000^6369 ≤ 1337174001983^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052130691 2000000000 1337174001983 3125000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127686857/10000000000 : ℝ), (674779603/1250000000 : ℝ), (1052130691/2000000000 : ℝ)] ![(6467871293929/50000000000000 : ℝ), (44274689342743/100000000000000 : ℝ), (1337174001983/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127686857/10000000000 : ℝ)|^8417 ≤ (6467871293929/50000000000000 : ℝ)^6369
        have hw : |(-2127686857/10000000000 : ℝ)|=(2127686857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674779603/1250000000 : ℝ)|^8417 ≤ (44274689342743/100000000000000 : ℝ)^6369
        have hw : |(674779603/1250000000 : ℝ)|=(674779603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052130691/2000000000 : ℝ)|^8417 ≤ (1337174001983/3125000000000 : ℝ)^6369
        have hw : |(1052130691/2000000000 : ℝ)|=(1052130691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673047949/5000000000 : ℝ)*x 0 + (-2197550759/10000000000 : ℝ)*x 1 + (5260653379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673047949/5000000000 : ℝ)^8417 ≤ (1365950401211/3125000000000 : ℝ)^6369 := by
    have hnat : (2673047949 : ℕ)^8417*3125000000000^6369 ≤ 1365950401211^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673047949 5000000000 1365950401211 3125000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197550759/10000000000 : ℝ)^8417 ≤ (13500019901433/100000000000000 : ℝ)^6369 := by
    have hnat : (2197550759 : ℕ)^8417*100000000000000^6369 ≤ 13500019901433^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197550759 10000000000 13500019901433 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260653379/10000000000 : ℝ)^8417 ≤ (21394783623251/50000000000000 : ℝ)^6369 := by
    have hnat : (5260653379 : ℕ)^8417*50000000000000^6369 ≤ 21394783623251^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260653379 10000000000 21394783623251 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673047949/5000000000 : ℝ), (-2197550759/10000000000 : ℝ), (5260653379/10000000000 : ℝ)] ![(1365950401211/3125000000000 : ℝ), (13500019901433/100000000000000 : ℝ), (21394783623251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673047949/5000000000 : ℝ)|^8417 ≤ (1365950401211/3125000000000 : ℝ)^6369
        have hw : |(2673047949/5000000000 : ℝ)|=(2673047949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197550759/10000000000 : ℝ)|^8417 ≤ (13500019901433/100000000000000 : ℝ)^6369
        have hw : |(-2197550759/10000000000 : ℝ)|=(2197550759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260653379/10000000000 : ℝ)|^8417 ≤ (21394783623251/50000000000000 : ℝ)^6369
        have hw : |(5260653379/10000000000 : ℝ)|=(5260653379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8553753/16000000 : ℝ)*x 0 + (2630326709/5000000000 : ℝ)*x 1 + (-219755107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8553753/16000000 : ℝ)^8417 ≤ (43710409888923/100000000000000 : ℝ)^6369 := by
    have hnat : (8553753 : ℕ)^8417*100000000000000^6369 ≤ 43710409888923^6369*16000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8553753 16000000 43710409888923 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630326709/5000000000 : ℝ)^8417 ≤ (42789567665729/100000000000000 : ℝ)^6369 := by
    have hnat : (2630326709 : ℕ)^8417*100000000000000^6369 ≤ 42789567665729^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630326709 5000000000 42789567665729 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219755107/1000000000 : ℝ)^8417 ≤ (168750280329/1250000000000 : ℝ)^6369 := by
    have hnat : (219755107 : ℕ)^8417*1250000000000^6369 ≤ 168750280329^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219755107 1000000000 168750280329 1250000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8553753/16000000 : ℝ), (2630326709/5000000000 : ℝ), (-219755107/1000000000 : ℝ)] ![(43710409888923/100000000000000 : ℝ), (42789567665729/100000000000000 : ℝ), (168750280329/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8553753/16000000 : ℝ)|^8417 ≤ (43710409888923/100000000000000 : ℝ)^6369
        have hw : |(8553753/16000000 : ℝ)|=(8553753/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630326709/5000000000 : ℝ)|^8417 ≤ (42789567665729/100000000000000 : ℝ)^6369
        have hw : |(2630326709/5000000000 : ℝ)|=(2630326709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219755107/1000000000 : ℝ)|^8417 ≤ (168750280329/1250000000000 : ℝ)^6369
        have hw : |(-219755107/1000000000 : ℝ)|=(219755107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088225287/2500000000 : ℝ)*x 0 + (2108002941/5000000000 : ℝ)*x 1 + (89882673/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088225287/2500000000 : ℝ)^8417 ≤ (6662778870559/20000000000000 : ℝ)^6369 := by
    have hnat : (1088225287 : ℕ)^8417*20000000000000^6369 ≤ 6662778870559^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088225287 2500000000 6662778870559 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108002941/5000000000 : ℝ)^8417 ≤ (1596817803371/5000000000000 : ℝ)^6369 := by
    have hnat : (2108002941 : ℕ)^8417*5000000000000^6369 ≤ 1596817803371^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108002941 5000000000 1596817803371 5000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89882673/200000000 : ℝ)^8417 ≤ (2171859348231/6250000000000 : ℝ)^6369 := by
    have hnat : (89882673 : ℕ)^8417*6250000000000^6369 ≤ 2171859348231^6369*200000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89882673 200000000 2171859348231 6250000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088225287/2500000000 : ℝ), (2108002941/5000000000 : ℝ), (89882673/200000000 : ℝ)] ![(6662778870559/20000000000000 : ℝ), (1596817803371/5000000000000 : ℝ), (2171859348231/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088225287/2500000000 : ℝ)|^8417 ≤ (6662778870559/20000000000000 : ℝ)^6369
        have hw : |(1088225287/2500000000 : ℝ)|=(1088225287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2108002941/5000000000 : ℝ)|^8417 ≤ (1596817803371/5000000000000 : ℝ)^6369
        have hw : |(2108002941/5000000000 : ℝ)|=(2108002941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89882673/200000000 : ℝ)|^8417 ≤ (2171859348231/6250000000000 : ℝ)^6369
        have hw : |(89882673/200000000 : ℝ)|=(89882673/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-531923113/2500000000 : ℝ)*x 0 + (1315259093/2500000000 : ℝ)*x 1 + (1079570583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531923113/2500000000 : ℝ)^8417 ≤ (1293578754203/10000000000000 : ℝ)^6369 := by
    have hnat : (531923113 : ℕ)^8417*10000000000000^6369 ≤ 1293578754203^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531923113 2500000000 1293578754203 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315259093/2500000000 : ℝ)^8417 ≤ (21396842120113/50000000000000 : ℝ)^6369 := by
    have hnat : (1315259093 : ℕ)^8417*50000000000000^6369 ≤ 21396842120113^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315259093 2500000000 21396842120113 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079570583/2000000000 : ℝ)^8417 ≤ (44270528196349/100000000000000 : ℝ)^6369 := by
    have hnat : (1079570583 : ℕ)^8417*100000000000000^6369 ≤ 44270528196349^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079570583 2000000000 44270528196349 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531923113/2500000000 : ℝ), (1315259093/2500000000 : ℝ), (1079570583/2000000000 : ℝ)] ![(1293578754203/10000000000000 : ℝ), (21396842120113/50000000000000 : ℝ), (44270528196349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531923113/2500000000 : ℝ)|^8417 ≤ (1293578754203/10000000000000 : ℝ)^6369
        have hw : |(-531923113/2500000000 : ℝ)|=(531923113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315259093/2500000000 : ℝ)|^8417 ≤ (21396842120113/50000000000000 : ℝ)^6369
        have hw : |(1315259093/2500000000 : ℝ)|=(1315259093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079570583/2000000000 : ℝ)|^8417 ≤ (44270528196349/100000000000000 : ℝ)^6369
        have hw : |(1079570583/2000000000 : ℝ)|=(1079570583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531103573/1000000000 : ℝ)*x 0 + (-1030175893/5000000000 : ℝ)*x 1 + (1349463093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531103573/1000000000 : ℝ)^8417 ≤ (21665989749459/50000000000000 : ℝ)^6369 := by
    have hnat : (531103573 : ℕ)^8417*50000000000000^6369 ≤ 21665989749459^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531103573 1000000000 21665989749459 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030175893/5000000000 : ℝ)^8417 ≤ (774843635593/6250000000000 : ℝ)^6369 := by
    have hnat : (1030175893 : ℕ)^8417*6250000000000^6369 ≤ 774843635593^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030175893 5000000000 774843635593 6250000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349463093/2500000000 : ℝ)^8417 ≤ (44270522310901/100000000000000 : ℝ)^6369 := by
    have hnat : (1349463093 : ℕ)^8417*100000000000000^6369 ≤ 44270522310901^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349463093 2500000000 44270522310901 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531103573/1000000000 : ℝ), (-1030175893/5000000000 : ℝ), (1349463093/2500000000 : ℝ)] ![(21665989749459/50000000000000 : ℝ), (774843635593/6250000000000 : ℝ), (44270522310901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531103573/1000000000 : ℝ)|^8417 ≤ (21665989749459/50000000000000 : ℝ)^6369
        have hw : |(531103573/1000000000 : ℝ)|=(531103573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030175893/5000000000 : ℝ)|^8417 ≤ (774843635593/6250000000000 : ℝ)^6369
        have hw : |(-1030175893/5000000000 : ℝ)|=(1030175893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349463093/2500000000 : ℝ)|^8417 ≤ (44270522310901/100000000000000 : ℝ)^6369
        have hw : |(1349463093/2500000000 : ℝ)|=(1349463093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655517853/5000000000 : ℝ)*x 0 + (5397852497/10000000000 : ℝ)*x 1 + (-2060351649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655517853/5000000000 : ℝ)^8417 ≤ (2166598962007/5000000000000 : ℝ)^6369 := by
    have hnat : (2655517853 : ℕ)^8417*5000000000000^6369 ≤ 2166598962007^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655517853 5000000000 2166598962007 5000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397852497/10000000000 : ℝ)^8417 ≤ (22135261832873/50000000000000 : ℝ)^6369 := by
    have hnat : (5397852497 : ℕ)^8417*50000000000000^6369 ≤ 22135261832873^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397852497 10000000000 22135261832873 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060351649/10000000000 : ℝ)^8417 ≤ (6198748540029/50000000000000 : ℝ)^6369 := by
    have hnat : (2060351649 : ℕ)^8417*50000000000000^6369 ≤ 6198748540029^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060351649 10000000000 6198748540029 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655517853/5000000000 : ℝ), (5397852497/10000000000 : ℝ), (-2060351649/10000000000 : ℝ)] ![(2166598962007/5000000000000 : ℝ), (22135261832873/50000000000000 : ℝ), (6198748540029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655517853/5000000000 : ℝ)|^8417 ≤ (2166598962007/5000000000000 : ℝ)^6369
        have hw : |(2655517853/5000000000 : ℝ)|=(2655517853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397852497/10000000000 : ℝ)|^8417 ≤ (22135261832873/50000000000000 : ℝ)^6369
        have hw : |(5397852497/10000000000 : ℝ)|=(5397852497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060351649/10000000000 : ℝ)|^8417 ≤ (6198748540029/50000000000000 : ℝ)^6369
        have hw : |(-2060351649/10000000000 : ℝ)|=(2060351649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s4_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435291449/1000000000 : ℝ)*x 0 + (561669953/1250000000 : ℝ)*x 1 + (263548903/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435291449/1000000000 : ℝ)^8417 ≤ (33314029296873/100000000000000 : ℝ)^6369 := by
    have hnat : (435291449 : ℕ)^8417*100000000000000^6369 ≤ 33314029296873^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435291449 1000000000 33314029296873 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561669953/1250000000 : ℝ)^8417 ≤ (34741840321823/100000000000000 : ℝ)^6369 := by
    have hnat : (561669953 : ℕ)^8417*100000000000000^6369 ≤ 34741840321823^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561669953 1250000000 34741840321823 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263548903/625000000 : ℝ)^8417 ≤ (638882607409/2000000000000 : ℝ)^6369 := by
    have hnat : (263548903 : ℕ)^8417*2000000000000^6369 ≤ 638882607409^6369*625000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263548903 625000000 638882607409 2000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435291449/1000000000 : ℝ), (561669953/1250000000 : ℝ), (263548903/625000000 : ℝ)] ![(33314029296873/100000000000000 : ℝ), (34741840321823/100000000000000 : ℝ), (638882607409/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435291449/1000000000 : ℝ)|^8417 ≤ (33314029296873/100000000000000 : ℝ)^6369
        have hw : |(435291449/1000000000 : ℝ)|=(435291449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561669953/1250000000 : ℝ)|^8417 ≤ (34741840321823/100000000000000 : ℝ)^6369
        have hw : |(561669953/1250000000 : ℝ)|=(561669953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263548903/625000000 : ℝ)|^8417 ≤ (638882607409/2000000000000 : ℝ)^6369
        have hw : |(263548903/625000000 : ℝ)|=(263548903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (679/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (679/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (679/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (679/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (679/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (679/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (679/6250 : ℝ) ^ (263/64 : ℝ) ≤ (5463744870188511/50000000000000000000 : ℝ) := by
    have hpowers : (679/6250 : ℝ)^263 ≤ (5463744870188511/50000000000000000000 : ℝ)^64 := by
      have hnat : (679 : ℕ)^263*50000000000000000000^64 ≤ 5463744870188511^64*6250^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        679 6250 5463744870188511 50000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (679/6250 : ℝ)) (X := (5463744870188511/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (7359/50000 : ℝ) ^ (263/64 : ℝ) ≤ (38052102393227777/100000000000000000000 : ℝ) := by
    have hpowers : (7359/50000 : ℝ)^263 ≤ (38052102393227777/100000000000000000000 : ℝ)^64 := by
      have hnat : (7359 : ℕ)^263*100000000000000000000^64 ≤ 38052102393227777^64*50000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7359 50000 38052102393227777 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7359/50000 : ℝ)) (X := (38052102393227777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005463744870188511/25000000000000000000 : ℝ) ≤ (2000106357646457/2000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (25005463744870188511/25000000000000000000 : ℝ)^64 ≤ (2000106357646457/2000000000000000 : ℝ)^263 := by
      have hnat : (25005463744870188511 : ℕ)^64*2000000000000000^263 ≤ 2000106357646457^263*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005463744870188511 25000000000000000000 2000106357646457 2000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000106357646457/2000000000000000 : ℝ)) (X := (25005463744870188511/25000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048979592133604799/100000000000000000000 : ℝ) ≤ (10001191678020853/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (100048979592133604799/100000000000000000000 : ℝ)^64 ≤ (10001191678020853/10000000000000000 : ℝ)^263 := by
      have hnat : (100048979592133604799 : ℕ)^64*10000000000000000^263 ≤ 10001191678020853^263*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048979592133604799 100000000000000000000 10001191678020853 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001191678020853/10000000000000000 : ℝ)) (X := (100048979592133604799/100000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038052102393227777/50000000000000000000 : ℝ) ≤ (10001851567809421/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50038052102393227777/50000000000000000000 : ℝ)^64 ≤ (10001851567809421/10000000000000000 : ℝ)^263 := by
      have hnat : (50038052102393227777 : ℕ)^64*10000000000000000^263 ≤ 10001851567809421^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038052102393227777 50000000000000000000 10001851567809421 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001851567809421/10000000000000000 : ℝ)) (X := (50038052102393227777/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5463744870188511/50000000000000000000 : ℝ) ≤ ((19263855713260610443/19270000000000000000 : ℝ)+2*(82486223571/48175000000000 : ℝ)*(679/6250 : ℝ))^(263/64 : ℝ) := by
    rw [show (19263855713260610443/19270000000000000000 : ℝ)+2*(82486223571/48175000000000 : ℝ)*(679/6250 : ℝ)=(2000106357646457/2000000000000000 : ℝ) by norm_num, show 1+2*(5463744870188511/50000000000000000000 : ℝ)=(25005463744870188511/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38052102393227777/100000000000000000000 : ℝ)+(5463744870188511/50000000000000000000 : ℝ) ≤ ((19263855713260610443/19270000000000000000 : ℝ)+(82486223571/48175000000000 : ℝ)*((7359/50000 : ℝ)+(679/6250 : ℝ)))^(263/64 : ℝ) := by
    rw [show (19263855713260610443/19270000000000000000 : ℝ)+(82486223571/48175000000000 : ℝ)*((7359/50000 : ℝ)+(679/6250 : ℝ))=(10001191678020853/10000000000000000 : ℝ) by norm_num, show 1+(38052102393227777/100000000000000000000 : ℝ)+(5463744870188511/50000000000000000000 : ℝ)=(100048979592133604799/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38052102393227777/100000000000000000000 : ℝ) ≤ ((19263855713260610443/19270000000000000000 : ℝ)+2*(82486223571/48175000000000 : ℝ)*(7359/50000 : ℝ))^(263/64 : ℝ) := by
    rw [show (19263855713260610443/19270000000000000000 : ℝ)+2*(82486223571/48175000000000 : ℝ)*(7359/50000 : ℝ)=(10001851567809421/10000000000000000 : ℝ) by norm_num, show 1+2*(38052102393227777/100000000000000000000 : ℝ)=(50038052102393227777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19263855713260610443/19270000000000000000 : ℝ)*(X 1 0+X 2 0)+(82486223571/48175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (679/6250 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (19263855713260610443/19270000000000000000 : ℝ)) (alpha := (82486223571/48175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19263855713260610443/19270000000000000000 : ℝ)*(X 0 1+X 2 1)+(82486223571/48175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (679/6250 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (19263855713260610443/19270000000000000000 : ℝ)) (alpha := (82486223571/48175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19263855713260610443/19270000000000000000 : ℝ)*(X 0 2+X 1 2)+(82486223571/48175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (679/6250 : ℝ)) (hi := (7359/50000 : ℝ)) (c := (19263855713260610443/19270000000000000000 : ℝ)) (alpha := (82486223571/48175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2127686857/10000000000 : ℝ)*X 0 0+(674779603/1250000000 : ℝ)*X 0 1+(1052130691/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673047949/5000000000 : ℝ)*X 1 0+(-2197550759/10000000000 : ℝ)*X 1 1+(5260653379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8553753/16000000 : ℝ)*X 2 0+(2630326709/5000000000 : ℝ)*X 2 1+(-219755107/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088225287/2500000000 : ℝ)*X 0 0+(2108002941/5000000000 : ℝ)*X 0 1+(89882673/200000000 : ℝ)*X 0 2+(1088225287/2500000000 : ℝ)*X 1 0+(2108002941/5000000000 : ℝ)*X 1 1+(89882673/200000000 : ℝ)*X 1 2+(1088225287/2500000000 : ℝ)*X 2 0+(2108002941/5000000000 : ℝ)*X 2 1+(89882673/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-531923113/2500000000 : ℝ)*X 0 0+(1315259093/2500000000 : ℝ)*X 0 1+(1079570583/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531103573/1000000000 : ℝ)*X 1 0+(-1030175893/5000000000 : ℝ)*X 1 1+(1349463093/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655517853/5000000000 : ℝ)*X 2 0+(5397852497/10000000000 : ℝ)*X 2 1+(-2060351649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435291449/1000000000 : ℝ)*X 0 0+(561669953/1250000000 : ℝ)*X 0 1+(263548903/625000000 : ℝ)*X 0 2+(435291449/1000000000 : ℝ)*X 1 0+(561669953/1250000000 : ℝ)*X 1 1+(263548903/625000000 : ℝ)*X 1 2+(435291449/1000000000 : ℝ)*X 2 0+(561669953/1250000000 : ℝ)*X 2 1+(263548903/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3670851601082026113772598787/963500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (590387939/50000000000000 : ℝ)*(base19) + (575503119/50000000000000 : ℝ)*(base23) + (48988807/25000000000000 : ℝ)*(upper2) + (16647799/10000000000000 : ℝ)*(upper3) + (5431943957030401/100000000000000 : ℝ)*(major0) + (5431943957030401/100000000000000 : ℝ)*(major1) + (5431943957030401/100000000000000 : ℝ)*(major2) + (7268361794045241/100000000000000 : ℝ)*(sp0) + (1817096310282009/25000000000000 : ℝ)*(sp1) + (1817095359119461/25000000000000 : ℝ)*(sp2) + (898871449804521/25000000000000 : ℝ)*(sp3) + (24627858673/100000000000000 : ℝ)*(sp4) + (3834419831/100000000000000 : ℝ)*(sp6) + (15565941679/100000000000000 : ℝ)*(sp7) + (3595501365159763/100000000000000 : ℝ)*(f.failure) + (3634193210951957/50000000000000 : ℝ)*(f.sum) + (19008074737831/9635000000000000000000000000 : ℝ)*base66 + (37813661772590522357/1927000000000000000000000000000000 : ℝ)*base68 + (32956212206776522357/1927000000000000000000000000000000 : ℝ)*base70 + (27496191109132522357/1927000000000000000000000000000000 : ℝ)*base72 + (364046647837/301093750000000000000000000 : ℝ)*base73 + (10990328018614522357/1927000000000000000000000000000000 : ℝ)*base76 + (22295067529498522357/1927000000000000000000000000000000 : ℝ)*base78 + (22807592210883522357/1927000000000000000000000000000000 : ℝ)*base80 + (19887678521329/9635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1853989/250000000000000000000 : ℝ)*base89 + (1853989/250000000000000000000 : ℝ)*base91 + (1853989/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2049829542831658021098415131/240875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (966395727/100000000000000 : ℝ)*(base19) + (2236687543/100000000000000 : ℝ)*(base23) + (7133397/1250000000000 : ℝ)*(lower4) + (28956079/100000000000000 : ℝ)*(upper5) + (2731170855272739/50000000000000 : ℝ)*(major0) + (2731170855272739/50000000000000 : ℝ)*(major1) + (2731170855272739/50000000000000 : ℝ)*(major2) + (7895735637/100000000000000 : ℝ)*(sp0) + (5692339117/50000000000000 : ℝ)*(sp1) + (46047275569/100000000000000 : ℝ)*(sp2) + (913631632120437/12500000000000 : ℝ)*(sp4) + (1827262150406293/25000000000000 : ℝ)*(sp5) + (7309012668736021/100000000000000 : ℝ)*(sp6) + (180781109236373/5000000000000 : ℝ)*(sp7) + (180781109236373/5000000000000 : ℝ)*(f.failure) + (7309060952699133/100000000000000 : ℝ)*(f.sum) + (78503088533113/9635000000000000000000000000 : ℝ)*base66 + (3742861035155786623/963500000000000000000000000000000 : ℝ)*base68 + (3457125778658286623/963500000000000000000000000000000 : ℝ)*base70 + (15274729164357786623/963500000000000000000000000000000 : ℝ)*base72 + (14641356393041/4817500000000000000000000000 : ℝ)*base73 + (14105461657159213377/963500000000000000000000000000000 : ℝ)*base75 + (4312962454154286623/963500000000000000000000000000000 : ℝ)*base78 + (11336846109572286623/963500000000000000000000000000000 : ℝ)*base80 + (63790677875583/9635000000000000000000000000 : ℝ)*base82 + (142819/12500000000000000000 : ℝ)*base89 + (142819/12500000000000000000 : ℝ)*base91 + (142819/12500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1224_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1224_s5_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-133010279/625000000 : ℝ)*x 0 + (5392846769/10000000000 : ℝ)*x 1 + (5265729779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133010279/625000000 : ℝ)^8417 ≤ (1617447519487/12500000000000 : ℝ)^6369 := by
    have hnat : (133010279 : ℕ)^8417*12500000000000^6369 ≤ 1617447519487^6369*625000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133010279 625000000 1617447519487 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392846769/10000000000 : ℝ)^8417 ≤ (44216275856939/100000000000000 : ℝ)^6369 := by
    have hnat : (5392846769 : ℕ)^8417*100000000000000^6369 ≤ 44216275856939^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392846769 10000000000 44216275856939 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265729779/10000000000 : ℝ)^8417 ≤ (5355517996581/12500000000000 : ℝ)^6369 := by
    have hnat : (5265729779 : ℕ)^8417*12500000000000^6369 ≤ 5355517996581^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265729779 10000000000 5355517996581 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133010279/625000000 : ℝ), (5392846769/10000000000 : ℝ), (5265729779/10000000000 : ℝ)] ![(1617447519487/12500000000000 : ℝ), (44216275856939/100000000000000 : ℝ), (5355517996581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133010279/625000000 : ℝ)|^8417 ≤ (1617447519487/12500000000000 : ℝ)^6369
        have hw : |(-133010279/625000000 : ℝ)|=(133010279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392846769/10000000000 : ℝ)|^8417 ≤ (44216275856939/100000000000000 : ℝ)^6369
        have hw : |(5392846769/10000000000 : ℝ)|=(5392846769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265729779/10000000000 : ℝ)|^8417 ≤ (5355517996581/12500000000000 : ℝ)^6369
        have hw : |(5265729779/10000000000 : ℝ)|=(5265729779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672367171/5000000000 : ℝ)*x 0 + (-1096319301/5000000000 : ℝ)*x 1 + (20569257/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672367171/5000000000 : ℝ)^8417 ≤ (21847850753903/50000000000000 : ℝ)^6369 := by
    have hnat : (2672367171 : ℕ)^8417*50000000000000^6369 ≤ 21847850753903^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672367171 5000000000 21847850753903 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096319301/5000000000 : ℝ)^8417 ≤ (3365038590979/25000000000000 : ℝ)^6369 := by
    have hnat : (1096319301 : ℕ)^8417*25000000000000^6369 ≤ 3365038590979^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096319301 5000000000 3365038590979 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20569257/39062500 : ℝ)^8417 ≤ (21422072056217/50000000000000 : ℝ)^6369 := by
    have hnat : (20569257 : ℕ)^8417*50000000000000^6369 ≤ 21422072056217^6369*39062500^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20569257 39062500 21422072056217 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672367171/5000000000 : ℝ), (-1096319301/5000000000 : ℝ), (20569257/39062500 : ℝ)] ![(21847850753903/50000000000000 : ℝ), (3365038590979/25000000000000 : ℝ), (21422072056217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672367171/5000000000 : ℝ)|^8417 ≤ (21847850753903/50000000000000 : ℝ)^6369
        have hw : |(2672367171/5000000000 : ℝ)|=(2672367171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096319301/5000000000 : ℝ)|^8417 ≤ (3365038590979/25000000000000 : ℝ)^6369
        have hw : |(-1096319301/5000000000 : ℝ)|=(1096319301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20569257/39062500 : ℝ)|^8417 ≤ (21422072056217/50000000000000 : ℝ)^6369
        have hw : |(20569257/39062500 : ℝ)|=(20569257/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267236719/500000000 : ℝ)*x 0 + (1053145971/2000000000 : ℝ)*x 1 + (-548159617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267236719/500000000 : ℝ)^8417 ≤ (10923925479593/25000000000000 : ℝ)^6369 := by
    have hnat : (267236719 : ℕ)^8417*25000000000000^6369 ≤ 10923925479593^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267236719 500000000 10923925479593 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053145971/2000000000 : ℝ)^8417 ≤ (1338879524683/3125000000000 : ℝ)^6369 := by
    have hnat : (1053145971 : ℕ)^8417*3125000000000^6369 ≤ 1338879524683^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053145971 2000000000 1338879524683 3125000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548159617/2500000000 : ℝ)^8417 ≤ (2692030655361/20000000000000 : ℝ)^6369 := by
    have hnat : (548159617 : ℕ)^8417*20000000000000^6369 ≤ 2692030655361^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548159617 2500000000 2692030655361 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267236719/500000000 : ℝ), (1053145971/2000000000 : ℝ), (-548159617/2500000000 : ℝ)] ![(10923925479593/25000000000000 : ℝ), (1338879524683/3125000000000 : ℝ), (2692030655361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267236719/500000000 : ℝ)|^8417 ≤ (10923925479593/25000000000000 : ℝ)^6369
        have hw : |(267236719/500000000 : ℝ)|=(267236719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053145971/2000000000 : ℝ)|^8417 ≤ (1338879524683/3125000000000 : ℝ)^6369
        have hw : |(1053145971/2000000000 : ℝ)|=(1053145971/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548159617/2500000000 : ℝ)|^8417 ≤ (2692030655361/20000000000000 : ℝ)^6369
        have hw : |(-548159617/2500000000 : ℝ)|=(548159617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176591209/5000000000 : ℝ)*x 0 + (4226549023/10000000000 : ℝ)*x 1 + (4483518299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176591209/5000000000 : ℝ)^8417 ≤ (6663347842171/20000000000000 : ℝ)^6369 := by
    have hnat : (2176591209 : ℕ)^8417*20000000000000^6369 ≤ 6663347842171^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176591209 5000000000 6663347842171 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226549023/10000000000 : ℝ)^8417 ≤ (32041944107339/100000000000000 : ℝ)^6369 := by
    have hnat : (4226549023 : ℕ)^8417*100000000000000^6369 ≤ 32041944107339^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226549023 10000000000 32041944107339 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483518299/10000000000 : ℝ)^8417 ≤ (34641316669347/100000000000000 : ℝ)^6369 := by
    have hnat : (4483518299 : ℕ)^8417*100000000000000^6369 ≤ 34641316669347^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483518299 10000000000 34641316669347 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176591209/5000000000 : ℝ), (4226549023/10000000000 : ℝ), (4483518299/10000000000 : ℝ)] ![(6663347842171/20000000000000 : ℝ), (32041944107339/100000000000000 : ℝ), (34641316669347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176591209/5000000000 : ℝ)|^8417 ≤ (6663347842171/20000000000000 : ℝ)^6369
        have hw : |(2176591209/5000000000 : ℝ)|=(2176591209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226549023/10000000000 : ℝ)|^8417 ≤ (32041944107339/100000000000000 : ℝ)^6369
        have hw : |(4226549023/10000000000 : ℝ)|=(4226549023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483518299/10000000000 : ℝ)|^8417 ≤ (34641316669347/100000000000000 : ℝ)^6369
        have hw : |(4483518299/10000000000 : ℝ)|=(4483518299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-532042329/2500000000 : ℝ)*x 0 + (5266056831/10000000000 : ℝ)*x 1 + (1348129653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532042329/2500000000 : ℝ)^8417 ≤ (2587923828619/20000000000000 : ℝ)^6369 := by
    have hnat : (532042329 : ℕ)^8417*20000000000000^6369 ≤ 2587923828619^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532042329 2500000000 2587923828619 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266056831/10000000000 : ℝ)^8417 ≤ (42847660711551/100000000000000 : ℝ)^6369 := by
    have hnat : (5266056831 : ℕ)^8417*100000000000000^6369 ≤ 42847660711551^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266056831 10000000000 42847660711551 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348129653/2500000000 : ℝ)^8417 ≤ (44212720136709/100000000000000 : ℝ)^6369 := by
    have hnat : (1348129653 : ℕ)^8417*100000000000000^6369 ≤ 44212720136709^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348129653 2500000000 44212720136709 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532042329/2500000000 : ℝ), (5266056831/10000000000 : ℝ), (1348129653/2500000000 : ℝ)] ![(2587923828619/20000000000000 : ℝ), (42847660711551/100000000000000 : ℝ), (44212720136709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532042329/2500000000 : ℝ)|^8417 ≤ (2587923828619/20000000000000 : ℝ)^6369
        have hw : |(-532042329/2500000000 : ℝ)|=(532042329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266056831/10000000000 : ℝ)|^8417 ≤ (42847660711551/100000000000000 : ℝ)^6369
        have hw : |(5266056831/10000000000 : ℝ)|=(5266056831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348129653/2500000000 : ℝ)|^8417 ≤ (44212720136709/100000000000000 : ℝ)^6369
        have hw : |(1348129653/2500000000 : ℝ)|=(1348129653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328084951/2500000000 : ℝ)*x 0 + (-516462461/2500000000 : ℝ)*x 1 + (5392518707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328084951/2500000000 : ℝ)^8417 ≤ (21673020549853/50000000000000 : ℝ)^6369 := by
    have hnat : (1328084951 : ℕ)^8417*50000000000000^6369 ≤ 21673020549853^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328084951 2500000000 21673020549853 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516462461/2500000000 : ℝ)^8417 ≤ (6220618856521/50000000000000 : ℝ)^6369 := by
    have hnat : (516462461 : ℕ)^8417*50000000000000^6369 ≤ 6220618856521^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516462461 2500000000 6220618856521 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392518707/10000000000 : ℝ)^8417 ≤ (8842544233213/20000000000000 : ℝ)^6369 := by
    have hnat : (5392518707 : ℕ)^8417*20000000000000^6369 ≤ 8842544233213^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392518707 10000000000 8842544233213 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328084951/2500000000 : ℝ), (-516462461/2500000000 : ℝ), (5392518707/10000000000 : ℝ)] ![(21673020549853/50000000000000 : ℝ), (6220618856521/50000000000000 : ℝ), (8842544233213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328084951/2500000000 : ℝ)|^8417 ≤ (21673020549853/50000000000000 : ℝ)^6369
        have hw : |(1328084951/2500000000 : ℝ)|=(1328084951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516462461/2500000000 : ℝ)|^8417 ≤ (6220618856521/50000000000000 : ℝ)^6369
        have hw : |(-516462461/2500000000 : ℝ)|=(516462461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392518707/10000000000 : ℝ)|^8417 ≤ (8842544233213/20000000000000 : ℝ)^6369
        have hw : |(5392518707/10000000000 : ℝ)|=(5392518707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328085011/2500000000 : ℝ)*x 0 + (5392518581/10000000000 : ℝ)*x 1 + (-516462423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328085011/2500000000 : ℝ)^8417 ≤ (21673021843843/50000000000000 : ℝ)^6369 := by
    have hnat : (1328085011 : ℕ)^8417*50000000000000^6369 ≤ 21673021843843^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328085011 2500000000 21673021843843 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392518581/10000000000 : ℝ)^8417 ≤ (8842543960163/20000000000000 : ℝ)^6369 := by
    have hnat : (5392518581 : ℕ)^8417*20000000000000^6369 ≤ 8842543960163^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392518581 10000000000 8842543960163 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516462423/2500000000 : ℝ)^8417 ≤ (48598580091/390625000000 : ℝ)^6369 := by
    have hnat : (516462423 : ℕ)^8417*390625000000^6369 ≤ 48598580091^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516462423 2500000000 48598580091 390625000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328085011/2500000000 : ℝ), (5392518581/10000000000 : ℝ), (-516462423/2500000000 : ℝ)] ![(21673021843843/50000000000000 : ℝ), (8842543960163/20000000000000 : ℝ), (48598580091/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328085011/2500000000 : ℝ)|^8417 ≤ (21673021843843/50000000000000 : ℝ)^6369
        have hw : |(1328085011/2500000000 : ℝ)|=(1328085011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392518581/10000000000 : ℝ)|^8417 ≤ (8842543960163/20000000000000 : ℝ)^6369
        have hw : |(5392518581/10000000000 : ℝ)|=(5392518581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516462423/2500000000 : ℝ)|^8417 ≤ (48598580091/390625000000 : ℝ)^6369
        have hw : |(-516462423/2500000000 : ℝ)|=(516462423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s5_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353192479/10000000000 : ℝ)*x 0 + (4482857623/10000000000 : ℝ)*x 1 + (528401521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353192479/10000000000 : ℝ)^8417 ≤ (33316840972241/100000000000000 : ℝ)^6369 := by
    have hnat : (4353192479 : ℕ)^8417*100000000000000^6369 ≤ 33316840972241^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353192479 10000000000 33316840972241 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482857623/10000000000 : ℝ)^8417 ≤ (6926914154291/20000000000000 : ℝ)^6369 := by
    have hnat : (4482857623 : ℕ)^8417*20000000000000^6369 ≤ 6926914154291^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482857623 10000000000 6926914154291 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528401521/1250000000 : ℝ)^8417 ≤ (32048588242837/100000000000000 : ℝ)^6369 := by
    have hnat : (528401521 : ℕ)^8417*100000000000000^6369 ≤ 32048588242837^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528401521 1250000000 32048588242837 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353192479/10000000000 : ℝ), (4482857623/10000000000 : ℝ), (528401521/1250000000 : ℝ)] ![(33316840972241/100000000000000 : ℝ), (6926914154291/20000000000000 : ℝ), (32048588242837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353192479/10000000000 : ℝ)|^8417 ≤ (33316840972241/100000000000000 : ℝ)^6369
        have hw : |(4353192479/10000000000 : ℝ)|=(4353192479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482857623/10000000000 : ℝ)|^8417 ≤ (6926914154291/20000000000000 : ℝ)^6369
        have hw : |(4482857623/10000000000 : ℝ)|=(4482857623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528401521/1250000000 : ℝ)|^8417 ≤ (32048588242837/100000000000000 : ℝ)^6369
        have hw : |(528401521/1250000000 : ℝ)|=(528401521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1143/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14123/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5661/50000 : ℝ) ^ (263/64 : ℝ) ≤ (2589676062594783/20000000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^263 ≤ (2589676062594783/20000000000000000000 : ℝ)^64 := by
      have hnat : (5661 : ℕ)^263*20000000000000000000^64 ≤ 2589676062594783^64*50000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 2589676062594783 20000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (2589676062594783/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (263/64 : ℝ) ≤ (16592954866903901/50000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^263 ≤ (16592954866903901/50000000000000000000 : ℝ)^64 := by
      have hnat : (3559 : ℕ)^263*50000000000000000000^64 ≤ 16592954866903901^64*25000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 16592954866903901 50000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (16592954866903901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002589676062594783/10000000000000000000 : ℝ) ≤ (5000315062798967/5000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (10002589676062594783/10000000000000000000 : ℝ)^64 ≤ (5000315062798967/5000000000000000 : ℝ)^263 := by
      have hnat : (10002589676062594783 : ℕ)^64*5000000000000000^263 ≤ 5000315062798967^263*10000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002589676062594783 10000000000000000000 5000315062798967 5000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000315062798967/5000000000000000 : ℝ)) (X := (10002589676062594783/10000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046134290046781717/100000000000000000000 : ℝ) ≤ (2500280615908823/2500000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (100046134290046781717/100000000000000000000 : ℝ)^64 ≤ (2500280615908823/2500000000000000 : ℝ)^263 := by
      have hnat : (100046134290046781717 : ℕ)^64*2500000000000000^263 ≤ 2500280615908823^263*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046134290046781717 100000000000000000000 2500280615908823 2500000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500280615908823/2500000000000000 : ℝ)) (X := (100046134290046781717/100000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016592954866903901/25000000000000000000 : ℝ) ≤ (200032296033453/200000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (25016592954866903901/25000000000000000000 : ℝ)^64 ≤ (200032296033453/200000000000000 : ℝ)^263 := by
      have hnat : (25016592954866903901 : ℕ)^64*200000000000000^263 ≤ 200032296033453^263*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016592954866903901 25000000000000000000 200032296033453 200000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200032296033453/200000000000000 : ℝ)) (X := (25016592954866903901/25000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2589676062594783/20000000000000000000 : ℝ) ≤ ((7282671920868611281/7285000000000000000 : ℝ)+2*(246169018679/145700000000000 : ℝ)*(5661/50000 : ℝ))^(263/64 : ℝ) := by
    rw [show (7282671920868611281/7285000000000000000 : ℝ)+2*(246169018679/145700000000000 : ℝ)*(5661/50000 : ℝ)=(5000315062798967/5000000000000000 : ℝ) by norm_num, show 1+2*(2589676062594783/20000000000000000000 : ℝ)=(10002589676062594783/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16592954866903901/50000000000000000000 : ℝ)+(2589676062594783/20000000000000000000 : ℝ) ≤ ((7282671920868611281/7285000000000000000 : ℝ)+(246169018679/145700000000000 : ℝ)*((3559/25000 : ℝ)+(5661/50000 : ℝ)))^(263/64 : ℝ) := by
    rw [show (7282671920868611281/7285000000000000000 : ℝ)+(246169018679/145700000000000 : ℝ)*((3559/25000 : ℝ)+(5661/50000 : ℝ))=(2500280615908823/2500000000000000 : ℝ) by norm_num, show 1+(16592954866903901/50000000000000000000 : ℝ)+(2589676062594783/20000000000000000000 : ℝ)=(100046134290046781717/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16592954866903901/50000000000000000000 : ℝ) ≤ ((7282671920868611281/7285000000000000000 : ℝ)+2*(246169018679/145700000000000 : ℝ)*(3559/25000 : ℝ))^(263/64 : ℝ) := by
    rw [show (7282671920868611281/7285000000000000000 : ℝ)+2*(246169018679/145700000000000 : ℝ)*(3559/25000 : ℝ)=(200032296033453/200000000000000 : ℝ) by norm_num, show 1+2*(16592954866903901/50000000000000000000 : ℝ)=(25016592954866903901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7282671920868611281/7285000000000000000 : ℝ)*(X 1 0+X 2 0)+(246169018679/145700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7282671920868611281/7285000000000000000 : ℝ)) (alpha := (246169018679/145700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7282671920868611281/7285000000000000000 : ℝ)*(X 0 1+X 2 1)+(246169018679/145700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7282671920868611281/7285000000000000000 : ℝ)) (alpha := (246169018679/145700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7282671920868611281/7285000000000000000 : ℝ)*(X 0 2+X 1 2)+(246169018679/145700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7282671920868611281/7285000000000000000 : ℝ)) (alpha := (246169018679/145700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-133010279/625000000 : ℝ)*X 0 0+(5392846769/10000000000 : ℝ)*X 0 1+(5265729779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672367171/5000000000 : ℝ)*X 1 0+(-1096319301/5000000000 : ℝ)*X 1 1+(20569257/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267236719/500000000 : ℝ)*X 2 0+(1053145971/2000000000 : ℝ)*X 2 1+(-548159617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176591209/5000000000 : ℝ)*X 0 0+(4226549023/10000000000 : ℝ)*X 0 1+(4483518299/10000000000 : ℝ)*X 0 2+(2176591209/5000000000 : ℝ)*X 1 0+(4226549023/10000000000 : ℝ)*X 1 1+(4483518299/10000000000 : ℝ)*X 1 2+(2176591209/5000000000 : ℝ)*X 2 0+(4226549023/10000000000 : ℝ)*X 2 1+(4483518299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532042329/2500000000 : ℝ)*X 0 0+(5266056831/10000000000 : ℝ)*X 0 1+(1348129653/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328084951/2500000000 : ℝ)*X 1 0+(-516462461/2500000000 : ℝ)*X 1 1+(5392518707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328085011/2500000000 : ℝ)*X 2 0+(5392518581/10000000000 : ℝ)*X 2 1+(-516462423/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353192479/10000000000 : ℝ)*X 0 0+(4482857623/10000000000 : ℝ)*X 0 1+(528401521/1250000000 : ℝ)*X 0 2+(4353192479/10000000000 : ℝ)*X 1 0+(4482857623/10000000000 : ℝ)*X 1 1+(528401521/1250000000 : ℝ)*X 1 2+(4353192479/10000000000 : ℝ)*X 2 0+(4482857623/10000000000 : ℝ)*X 2 1+(528401521/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (279055864978057368020075127/45531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8153909/625000000000 : ℝ)*(base19) + (656509603/50000000000000 : ℝ)*(base23) + (3205271/12500000000000 : ℝ)*(upper3) + (25407791/100000000000000 : ℝ)*(upper4) + (217340683/100000000000000 : ℝ)*(upper5) + (734900121250711/12500000000000 : ℝ)*(major0) + (734900121250711/12500000000000 : ℝ)*(major1) + (734900121250711/12500000000000 : ℝ)*(major2) + (1966701353467963/25000000000000 : ℝ)*(sp0) + (7866851607883441/100000000000000 : ℝ)*(sp1) + (314674063979587/4000000000000 : ℝ)*(sp2) + (486441740099401/12500000000000 : ℝ)*(sp3) + (47498637029/100000000000000 : ℝ)*(sp4) + (14902411061/100000000000000 : ℝ)*(sp7) + (972887205801567/25000000000000 : ℝ)*(f.failure) + (7866852912508881/100000000000000 : ℝ)*(f.sum) + (57695759647083/7285000000000000000000000000 : ℝ)*base66 + (664278386483804209/91062500000000000000000000000000 : ℝ)*base68 + (963557156287820791/91062500000000000000000000000000 : ℝ)*base69 + (889757548433258291/91062500000000000000000000000000 : ℝ)*base71 + (76966527075773/7285000000000000000000000000 : ℝ)*base74 + (685269262418320791/91062500000000000000000000000000 : ℝ)*base75 + (763936885755383291/91062500000000000000000000000000 : ℝ)*base77 + (647751074356679209/91062500000000000000000000000000 : ℝ)*base80 + (178314664313/1821250000000000000000000000 : ℝ)*base81 + (807001/62500000000000000000 : ℝ)*base89 + (807001/62500000000000000000 : ℝ)*base91 + (807001/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3416842879108319989198230129/364250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (564728551/50000000000000 : ℝ)*(base19) + (178287243/10000000000000 : ℝ)*(base23) + (146269853/100000000000000 : ℝ)*(upper3) + (6006819/6250000000000 : ℝ)*(lower4) + (10714649/10000000000000 : ℝ)*(upper5) + (5909598611279797/100000000000000 : ℝ)*(major0) + (5909598611279797/100000000000000 : ℝ)*(major1) + (5909598611279797/100000000000000 : ℝ)*(major2) + (7086532817/20000000000000 : ℝ)*(sp1) + (13583330347/25000000000000 : ℝ)*(sp2) + (1581505468279399/20000000000000 : ℝ)*(sp4) + (247109086852369/3125000000000 : ℝ)*(sp5) + (7907471225203177/100000000000000 : ℝ)*(sp6) + (3911669568479649/100000000000000 : ℝ)*(sp7) + (3911669568479649/100000000000000 : ℝ)*(f.failure) + (1581505468279399/20000000000000 : ℝ)*(f.sum) + (8227863211843/1821250000000000000000000000 : ℝ)*base66 + (2740255842127739957/728500000000000000000000000000000 : ℝ)*base67 + (842875552327739957/728500000000000000000000000000000 : ℝ)*base69 + (7576263656499239957/728500000000000000000000000000000 : ℝ)*base71 + (23822598000131/3642500000000000000000000000 : ℝ)*base74 + (65629247498260043/728500000000000000000000000000000 : ℝ)*base76 + (4324333978308239957/728500000000000000000000000000000 : ℝ)*base77 + (2338662380634260043/728500000000000000000000000000000 : ℝ)*base80 + (10969092550423/7285000000000000000000000000 : ℝ)*base81 + (752953/250000000000000000000 : ℝ)*base90 + (752953/250000000000000000000 : ℝ)*base92 + (752953/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1224_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1224_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1224_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1224_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1224_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (377/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

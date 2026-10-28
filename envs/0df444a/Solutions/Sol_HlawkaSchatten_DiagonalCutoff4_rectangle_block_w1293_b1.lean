-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1293_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:57.511383+00:00
-- url     : https://prove2.me/submissions/6dc38cd1-5d2b-414d-9080-1fca08d7c6ce

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
theorem support_rectangle_w1293_s3_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-521182699/2500000000 : ℝ)*x 0 + (1358482899/2500000000 : ℝ)*x 1 + (5225811773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521182699/2500000000 : ℝ)^4253 ≤ (3169881333007/25000000000000 : ℝ)^3229 := by
    have hnat : (521182699 : ℕ)^4253*25000000000000^3229 ≤ 3169881333007^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521182699 2500000000 3169881333007 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358482899/2500000000 : ℝ)^4253 ≤ (22391437458827/50000000000000 : ℝ)^3229 := by
    have hnat : (1358482899 : ℕ)^4253*50000000000000^3229 ≤ 22391437458827^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358482899 2500000000 22391437458827 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225811773/10000000000 : ℝ)^4253 ≤ (21268799870661/50000000000000 : ℝ)^3229 := by
    have hnat : (5225811773 : ℕ)^4253*50000000000000^3229 ≤ 21268799870661^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225811773 10000000000 21268799870661 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-521182699/2500000000 : ℝ), (1358482899/2500000000 : ℝ), (5225811773/10000000000 : ℝ)] ![(3169881333007/25000000000000 : ℝ), (22391437458827/50000000000000 : ℝ), (21268799870661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-521182699/2500000000 : ℝ)|^4253 ≤ (3169881333007/25000000000000 : ℝ)^3229
        have hw : |(-521182699/2500000000 : ℝ)|=(521182699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358482899/2500000000 : ℝ)|^4253 ≤ (22391437458827/50000000000000 : ℝ)^3229
        have hw : |(1358482899/2500000000 : ℝ)|=(1358482899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225811773/10000000000 : ℝ)|^4253 ≤ (21268799870661/50000000000000 : ℝ)^3229
        have hw : |(5225811773/10000000000 : ℝ)|=(5225811773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669314161/1250000000 : ℝ)*x 0 + (-2191240781/10000000000 : ℝ)*x 1 + (5225811729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669314161/1250000000 : ℝ)^4253 ≤ (21961401492433/50000000000000 : ℝ)^3229 := by
    have hnat : (669314161 : ℕ)^4253*50000000000000^3229 ≤ 21961401492433^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669314161 1250000000 21961401492433 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191240781/10000000000 : ℝ)^4253 ≤ (13539597730593/100000000000000 : ℝ)^3229 := by
    have hnat : (2191240781 : ℕ)^4253*100000000000000^3229 ≤ 13539597730593^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191240781 10000000000 13539597730593 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225811729/10000000000 : ℝ)^4253 ≤ (8507519853917/20000000000000 : ℝ)^3229 := by
    have hnat : (5225811729 : ℕ)^4253*20000000000000^3229 ≤ 8507519853917^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225811729 10000000000 8507519853917 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669314161/1250000000 : ℝ), (-2191240781/10000000000 : ℝ), (5225811729/10000000000 : ℝ)] ![(21961401492433/50000000000000 : ℝ), (13539597730593/100000000000000 : ℝ), (8507519853917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669314161/1250000000 : ℝ)|^4253 ≤ (21961401492433/50000000000000 : ℝ)^3229
        have hw : |(669314161/1250000000 : ℝ)|=(669314161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191240781/10000000000 : ℝ)|^4253 ≤ (13539597730593/100000000000000 : ℝ)^3229
        have hw : |(-2191240781/10000000000 : ℝ)|=(2191240781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225811729/10000000000 : ℝ)|^4253 ≤ (8507519853917/20000000000000 : ℝ)^3229
        have hw : |(5225811729/10000000000 : ℝ)|=(5225811729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669314151/1250000000 : ℝ)*x 0 + (5225812007/10000000000 : ℝ)*x 1 + (-2191240521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669314151/1250000000 : ℝ)^4253 ≤ (1098070053013/2500000000000 : ℝ)^3229 := by
    have hnat : (669314151 : ℕ)^4253*2500000000000^3229 ≤ 1098070053013^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669314151 1250000000 1098070053013 2500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225812007/10000000000 : ℝ)^4253 ≤ (42537602250101/100000000000000 : ℝ)^3229 := by
    have hnat : (5225812007 : ℕ)^4253*100000000000000^3229 ≤ 42537602250101^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225812007 10000000000 42537602250101 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191240521/10000000000 : ℝ)^4253 ≤ (1353959561459/10000000000000 : ℝ)^3229 := by
    have hnat : (2191240521 : ℕ)^4253*10000000000000^3229 ≤ 1353959561459^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191240521 10000000000 1353959561459 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669314151/1250000000 : ℝ), (5225812007/10000000000 : ℝ), (-2191240521/10000000000 : ℝ)] ![(1098070053013/2500000000000 : ℝ), (42537602250101/100000000000000 : ℝ), (1353959561459/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669314151/1250000000 : ℝ)|^4253 ≤ (1098070053013/2500000000000 : ℝ)^3229
        have hw : |(669314151/1250000000 : ℝ)|=(669314151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225812007/10000000000 : ℝ)|^4253 ≤ (42537602250101/100000000000000 : ℝ)^3229
        have hw : |(5225812007/10000000000 : ℝ)|=(5225812007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191240521/10000000000 : ℝ)|^4253 ≤ (1353959561459/10000000000000 : ℝ)^3229
        have hw : |(-2191240521/10000000000 : ℝ)|=(2191240521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169093413/5000000000 : ℝ)*x 0 + (4129275067/10000000000 : ℝ)*x 1 + (2278586837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169093413/5000000000 : ℝ)^4253 ≤ (33288118686381/100000000000000 : ℝ)^3229 := by
    have hnat : (2169093413 : ℕ)^4253*100000000000000^3229 ≤ 33288118686381^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169093413 5000000000 33288118686381 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129275067/10000000000 : ℝ)^4253 ≤ (7798254495933/25000000000000 : ℝ)^3229 := by
    have hnat : (4129275067 : ℕ)^4253*25000000000000^3229 ≤ 7798254495933^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129275067 10000000000 7798254495933 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278586837/5000000000 : ℝ)^4253 ≤ (7103772662847/20000000000000 : ℝ)^3229 := by
    have hnat : (2278586837 : ℕ)^4253*20000000000000^3229 ≤ 7103772662847^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278586837 5000000000 7103772662847 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169093413/5000000000 : ℝ), (4129275067/10000000000 : ℝ), (2278586837/5000000000 : ℝ)] ![(33288118686381/100000000000000 : ℝ), (7798254495933/25000000000000 : ℝ), (7103772662847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169093413/5000000000 : ℝ)|^4253 ≤ (33288118686381/100000000000000 : ℝ)^3229
        have hw : |(2169093413/5000000000 : ℝ)|=(2169093413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129275067/10000000000 : ℝ)|^4253 ≤ (7798254495933/25000000000000 : ℝ)^3229
        have hw : |(4129275067/10000000000 : ℝ)|=(4129275067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2278586837/5000000000 : ℝ)|^4253 ≤ (7103772662847/20000000000000 : ℝ)^3229
        have hw : |(2278586837/5000000000 : ℝ)|=(2278586837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084753301/10000000000 : ℝ)*x 0 + (1306676867/2500000000 : ℝ)*x 1 + (1358257567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084753301/10000000000 : ℝ)^4253 ≤ (12679705617243/100000000000000 : ℝ)^3229 := by
    have hnat : (2084753301 : ℕ)^4253*100000000000000^3229 ≤ 12679705617243^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084753301 10000000000 12679705617243 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306676867/2500000000 : ℝ)^4253 ≤ (42547202997347/100000000000000 : ℝ)^3229 := by
    have hnat : (1306676867 : ℕ)^4253*100000000000000^3229 ≤ 42547202997347^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306676867 2500000000 42547202997347 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358257567/2500000000 : ℝ)^4253 ≤ (4477309136513/10000000000000 : ℝ)^3229 := by
    have hnat : (1358257567 : ℕ)^4253*10000000000000^3229 ≤ 4477309136513^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358257567 2500000000 4477309136513 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084753301/10000000000 : ℝ), (1306676867/2500000000 : ℝ), (1358257567/2500000000 : ℝ)] ![(12679705617243/100000000000000 : ℝ), (42547202997347/100000000000000 : ℝ), (4477309136513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084753301/10000000000 : ℝ)|^4253 ≤ (12679705617243/100000000000000 : ℝ)^3229
        have hw : |(-2084753301/10000000000 : ℝ)|=(2084753301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306676867/2500000000 : ℝ)|^4253 ≤ (42547202997347/100000000000000 : ℝ)^3229
        have hw : |(1306676867/2500000000 : ℝ)|=(1306676867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358257567/2500000000 : ℝ)|^4253 ≤ (4477309136513/10000000000000 : ℝ)^3229
        have hw : |(1358257567/2500000000 : ℝ)|=(1358257567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301218539/10000000000 : ℝ)*x 0 + (-496005521/2500000000 : ℝ)*x 1 + (5433030223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301218539/10000000000 : ℝ)^4253 ≤ (270924377247/625000000000 : ℝ)^3229 := by
    have hnat : (5301218539 : ℕ)^4253*625000000000^3229 ≤ 270924377247^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301218539 10000000000 270924377247 625000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496005521/2500000000 : ℝ)^4253 ≤ (11879008748019/100000000000000 : ℝ)^3229 := by
    have hnat : (496005521 : ℕ)^4253*100000000000000^3229 ≤ 11879008748019^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496005521 2500000000 11879008748019 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433030223/10000000000 : ℝ)^4253 ≤ (22386545438343/50000000000000 : ℝ)^3229 := by
    have hnat : (5433030223 : ℕ)^4253*50000000000000^3229 ≤ 22386545438343^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433030223 10000000000 22386545438343 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301218539/10000000000 : ℝ), (-496005521/2500000000 : ℝ), (5433030223/10000000000 : ℝ)] ![(270924377247/625000000000 : ℝ), (11879008748019/100000000000000 : ℝ), (22386545438343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301218539/10000000000 : ℝ)|^4253 ≤ (270924377247/625000000000 : ℝ)^3229
        have hw : |(5301218539/10000000000 : ℝ)|=(5301218539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496005521/2500000000 : ℝ)|^4253 ≤ (11879008748019/100000000000000 : ℝ)^3229
        have hw : |(-496005521/2500000000 : ℝ)|=(496005521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433030223/10000000000 : ℝ)|^4253 ≤ (22386545438343/50000000000000 : ℝ)^3229
        have hw : |(5433030223/10000000000 : ℝ)|=(5433030223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301218581/10000000000 : ℝ)*x 0 + (5433030159/10000000000 : ℝ)*x 1 + (-992011057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301218581/10000000000 : ℝ)^4253 ≤ (5418487601483/12500000000000 : ℝ)^3229 := by
    have hnat : (5301218581 : ℕ)^4253*12500000000000^3229 ≤ 5418487601483^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301218581 10000000000 5418487601483 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433030159/10000000000 : ℝ)^4253 ≤ (4477309018201/10000000000000 : ℝ)^3229 := by
    have hnat : (5433030159 : ℕ)^4253*10000000000000^3229 ≤ 4477309018201^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433030159 10000000000 4477309018201 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992011057/5000000000 : ℝ)^4253 ≤ (5939504492301/50000000000000 : ℝ)^3229 := by
    have hnat : (992011057 : ℕ)^4253*50000000000000^3229 ≤ 5939504492301^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992011057 5000000000 5939504492301 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301218581/10000000000 : ℝ), (5433030159/10000000000 : ℝ), (-992011057/5000000000 : ℝ)] ![(5418487601483/12500000000000 : ℝ), (4477309018201/10000000000000 : ℝ), (5939504492301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301218581/10000000000 : ℝ)|^4253 ≤ (5418487601483/12500000000000 : ℝ)^3229
        have hw : |(5301218581/10000000000 : ℝ)|=(5301218581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433030159/10000000000 : ℝ)|^4253 ≤ (4477309018201/10000000000000 : ℝ)^3229
        have hw : |(5433030159/10000000000 : ℝ)|=(5433030159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992011057/5000000000 : ℝ)|^4253 ≤ (5939504492301/50000000000000 : ℝ)^3229
        have hw : |(-992011057/5000000000 : ℝ)|=(992011057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s3_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338233243/10000000000 : ℝ)*x 0 + (1138833009/2500000000 : ℝ)*x 1 + (2065563899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338233243/10000000000 : ℝ)^4253 ≤ (33288587808751/100000000000000 : ℝ)^3229 := by
    have hnat : (4338233243 : ℕ)^4253*100000000000000^3229 ≤ 33288587808751^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338233243 10000000000 33288587808751 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138833009/2500000000 : ℝ)^4253 ≤ (3549995872471/10000000000000 : ℝ)^3229 := by
    have hnat : (1138833009 : ℕ)^4253*10000000000000^3229 ≤ 3549995872471^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138833009 2500000000 3549995872471 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065563899/5000000000 : ℝ)^4253 ≤ (15605726726163/50000000000000 : ℝ)^3229 := by
    have hnat : (2065563899 : ℕ)^4253*50000000000000^3229 ≤ 15605726726163^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065563899 5000000000 15605726726163 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338233243/10000000000 : ℝ), (1138833009/2500000000 : ℝ), (2065563899/5000000000 : ℝ)] ![(33288587808751/100000000000000 : ℝ), (3549995872471/10000000000000 : ℝ), (15605726726163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338233243/10000000000 : ℝ)|^4253 ≤ (33288587808751/100000000000000 : ℝ)^3229
        have hw : |(4338233243/10000000000 : ℝ)|=(4338233243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1138833009/2500000000 : ℝ)|^4253 ≤ (3549995872471/10000000000000 : ℝ)^3229
        have hw : |(1138833009/2500000000 : ℝ)|=(1138833009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065563899/5000000000 : ℝ)|^4253 ≤ (15605726726163/50000000000000 : ℝ)^3229
        have hw : |(2065563899/5000000000 : ℝ)|=(2065563899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5331/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3013/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1189/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1189/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1189/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1189/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1189/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1189/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1189/12500 : ℝ) ^ (1063/256 : ℝ) ≤ (1430123279003827/25000000000000000000 : ℝ) := by
    have hpowers : (1189/12500 : ℝ)^1063 ≤ (1430123279003827/25000000000000000000 : ℝ)^256 := by
      have hnat : (1189 : ℕ)^1063*25000000000000000000^256 ≤ 1430123279003827^256*12500^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1189 12500 1430123279003827 25000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1189/12500 : ℝ)) (X := (1430123279003827/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16313/100000 : ℝ) ^ (1063/256 : ℝ) ≤ (26862090051892387/50000000000000000000 : ℝ) := by
    have hpowers : (16313/100000 : ℝ)^1063 ≤ (26862090051892387/50000000000000000000 : ℝ)^256 := by
      have hnat : (16313 : ℕ)^1063*50000000000000000000^256 ≤ 26862090051892387^256*100000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16313 100000 26862090051892387 50000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16313/100000 : ℝ)) (X := (26862090051892387/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501430123279003827/12500000000000000000 : ℝ) ≤ (500013775942083/500000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (12501430123279003827/12500000000000000000 : ℝ)^256 ≤ (500013775942083/500000000000000 : ℝ)^1063 := by
      have hnat : (12501430123279003827 : ℕ)^256*500000000000000^1063 ≤ 500013775942083^1063*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501430123279003827 12500000000000000000 500013775942083 500000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500013775942083/500000000000000 : ℝ)) (X := (12501430123279003827/12500000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029722336609900041/50000000000000000000 : ℝ) ≤ (2000286254068331/2000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50029722336609900041/50000000000000000000 : ℝ)^256 ≤ (2000286254068331/2000000000000000 : ℝ)^1063 := by
      have hnat : (50029722336609900041 : ℕ)^256*2000000000000000^1063 ≤ 2000286254068331^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029722336609900041 50000000000000000000 2000286254068331 2000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000286254068331/2000000000000000 : ℝ)) (X := (50029722336609900041/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25026862090051892387/25000000000000000000 : ℝ) ≤ (200051740436833/200000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (25026862090051892387/25000000000000000000 : ℝ)^256 ≤ (200051740436833/200000000000000 : ℝ)^1063 := by
      have hnat : (25026862090051892387 : ℕ)^256*200000000000000^1063 ≤ 200051740436833^1063*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026862090051892387 25000000000000000000 200051740436833 200000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200051740436833/200000000000000 : ℝ)) (X := (25026862090051892387/25000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1430123279003827/25000000000000000000 : ℝ) ≤ ((3399494339355311239/3400500000000000000 : ℝ)+2*(231150299999/136020000000000 : ℝ)*(1189/12500 : ℝ))^(1063/256 : ℝ) := by
    rw [show (3399494339355311239/3400500000000000000 : ℝ)+2*(231150299999/136020000000000 : ℝ)*(1189/12500 : ℝ)=(500013775942083/500000000000000 : ℝ) by norm_num, show 1+2*(1430123279003827/25000000000000000000 : ℝ)=(12501430123279003827/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26862090051892387/50000000000000000000 : ℝ)+(1430123279003827/25000000000000000000 : ℝ) ≤ ((3399494339355311239/3400500000000000000 : ℝ)+(231150299999/136020000000000 : ℝ)*((16313/100000 : ℝ)+(1189/12500 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (3399494339355311239/3400500000000000000 : ℝ)+(231150299999/136020000000000 : ℝ)*((16313/100000 : ℝ)+(1189/12500 : ℝ))=(2000286254068331/2000000000000000 : ℝ) by norm_num, show 1+(26862090051892387/50000000000000000000 : ℝ)+(1430123279003827/25000000000000000000 : ℝ)=(50029722336609900041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26862090051892387/50000000000000000000 : ℝ) ≤ ((3399494339355311239/3400500000000000000 : ℝ)+2*(231150299999/136020000000000 : ℝ)*(16313/100000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (3399494339355311239/3400500000000000000 : ℝ)+2*(231150299999/136020000000000 : ℝ)*(16313/100000 : ℝ)=(200051740436833/200000000000000 : ℝ) by norm_num, show 1+2*(26862090051892387/50000000000000000000 : ℝ)=(25026862090051892387/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3399494339355311239/3400500000000000000 : ℝ)*(X 1 0+X 2 0)+(231150299999/136020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (1189/12500 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (3399494339355311239/3400500000000000000 : ℝ)) (alpha := (231150299999/136020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3399494339355311239/3400500000000000000 : ℝ)*(X 0 1+X 2 1)+(231150299999/136020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (1189/12500 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (3399494339355311239/3400500000000000000 : ℝ)) (alpha := (231150299999/136020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3399494339355311239/3400500000000000000 : ℝ)*(X 0 2+X 1 2)+(231150299999/136020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (1189/12500 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (3399494339355311239/3400500000000000000 : ℝ)) (alpha := (231150299999/136020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-521182699/2500000000 : ℝ)*X 0 0+(1358482899/2500000000 : ℝ)*X 0 1+(5225811773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669314161/1250000000 : ℝ)*X 1 0+(-2191240781/10000000000 : ℝ)*X 1 1+(5225811729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669314151/1250000000 : ℝ)*X 2 0+(5225812007/10000000000 : ℝ)*X 2 1+(-2191240521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169093413/5000000000 : ℝ)*X 0 0+(4129275067/10000000000 : ℝ)*X 0 1+(2278586837/5000000000 : ℝ)*X 0 2+(2169093413/5000000000 : ℝ)*X 1 0+(4129275067/10000000000 : ℝ)*X 1 1+(2278586837/5000000000 : ℝ)*X 1 2+(2169093413/5000000000 : ℝ)*X 2 0+(4129275067/10000000000 : ℝ)*X 2 1+(2278586837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2084753301/10000000000 : ℝ)*X 0 0+(1306676867/2500000000 : ℝ)*X 0 1+(1358257567/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301218539/10000000000 : ℝ)*X 1 0+(-496005521/2500000000 : ℝ)*X 1 1+(5433030223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301218581/10000000000 : ℝ)*X 2 0+(5433030159/10000000000 : ℝ)*X 2 1+(-992011057/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338233243/10000000000 : ℝ)*X 0 0+(1138833009/2500000000 : ℝ)*X 0 1+(2065563899/5000000000 : ℝ)*X 0 2+(4338233243/10000000000 : ℝ)*X 1 0+(1138833009/2500000000 : ℝ)*X 1 1+(2065563899/5000000000 : ℝ)*X 1 2+(4338233243/10000000000 : ℝ)*X 2 0+(1138833009/2500000000 : ℝ)*X 2 1+(2065563899/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260153749644513313304674581/28337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191791399/12500000000000 : ℝ)*(base19) + (359459513/25000000000000 : ℝ)*(base23) + (661377/5000000000000 : ℝ)*(lower2) + (22830609/50000000000000 : ℝ)*(upper3) + (275750141/100000000000000 : ℝ)*(upper5) + (1785502384950707/50000000000000 : ℝ)*(major0) + (1785502384950707/50000000000000 : ℝ)*(major1) + (1785502384950707/50000000000000 : ℝ)*(major2) + (4804949322862367/100000000000000 : ℝ)*(sp0) + (4804979914788107/100000000000000 : ℝ)*(sp1) + (4804980011281247/100000000000000 : ℝ)*(sp2) + (584254108907739/25000000000000 : ℝ)*(sp3) + (32126256933/100000000000000 : ℝ)*(sp4) + (11349034331/100000000000000 : ℝ)*(sp7) + (2337027784665287/100000000000000 : ℝ)*(f.failure) + (4804981449119299/100000000000000 : ℝ)*(f.sum) + (1560654722131/3400500000000000000000000000 : ℝ)*base65 + (601605399425606991/56675000000000000000000000000000 : ℝ)*base67 + (434671744498331991/56675000000000000000000000000000 : ℝ)*base69 + (1053311295205931991/56675000000000000000000000000000 : ℝ)*base71 + (827068692277/1360200000000000000000000000 : ℝ)*base73 + (431882639209431991/56675000000000000000000000000000 : ℝ)*base75 + (1085709867267931991/56675000000000000000000000000000 : ℝ)*base77 + (928732969344331991/56675000000000000000000000000000 : ℝ)*base79 + (2100719616791/6801000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6643419/5000000000000000000000 : ℝ)*base90 + (6643419/5000000000000000000000 : ℝ)*base92 + (6643419/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96674356888175044880096257/14168750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171597111/10000000000000 : ℝ)*(base19) + (181312111/10000000000000 : ℝ)*(base23) + (10643339/6250000000000 : ℝ)*(upper3) + (15446641/50000000000000 : ℝ)*(lower4) + (5814097/3125000000000 : ℝ)*(upper5) + (1801032309119887/50000000000000 : ℝ)*(major0) + (1801032309119887/50000000000000 : ℝ)*(major1) + (1801032309119887/50000000000000 : ℝ)*(major2) + (28548364607/100000000000000 : ℝ)*(sp1) + (28595641543/100000000000000 : ℝ)*(sp2) + (4846774248294459/100000000000000 : ℝ)*(sp4) + (4846743983958743/100000000000000 : ℝ)*(sp5) + (2423371919765903/50000000000000 : ℝ)*(sp6) + (147334672546841/6250000000000 : ℝ)*(sp7) + (147334672546841/6250000000000 : ℝ)*(f.failure) + (4846774248294459/100000000000000 : ℝ)*(f.sum) + (33180304359623/6801000000000000000000000000 : ℝ)*base66 + (179110089828878331/56675000000000000000000000000000 : ℝ)*base67 + (226242681993278331/56675000000000000000000000000000 : ℝ)*base69 + (29884368626603331/56675000000000000000000000000000 : ℝ)*base71 + (20405133134689/6801000000000000000000000000 : ℝ)*base73 + (123690392791778331/56675000000000000000000000000000 : ℝ)*base75 + (47932355922128331/56675000000000000000000000000000 : ℝ)*base77 + (194764918475646669/56675000000000000000000000000000 : ℝ)*base80 + (1022241583307/272040000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2521483/312500000000000000000 : ℝ)*base89 + (2521483/312500000000000000000 : ℝ)*base91 + (2521483/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1293_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3013/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1293_s4_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-16693141/80000000 : ℝ)*x 0 + (5418856259/10000000000 : ℝ)*x 1 + (1047926749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16693141/80000000 : ℝ)^4253 ≤ (3173710748933/25000000000000 : ℝ)^3229 := by
    have hnat : (16693141 : ℕ)^4253*25000000000000^3229 ≤ 3173710748933^3229*80000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16693141 80000000 3173710748933 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418856259/10000000000 : ℝ)^4253 ≤ (44619305931803/100000000000000 : ℝ)^3229 := by
    have hnat : (5418856259 : ℕ)^4253*100000000000000^3229 ≤ 44619305931803^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418856259 10000000000 44619305931803 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047926749/2000000000 : ℝ)^4253 ≤ (341486808453/800000000000 : ℝ)^3229 := by
    have hnat : (1047926749 : ℕ)^4253*800000000000^3229 ≤ 341486808453^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047926749 2000000000 341486808453 800000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16693141/80000000 : ℝ), (5418856259/10000000000 : ℝ), (1047926749/2000000000 : ℝ)] ![(3173710748933/25000000000000 : ℝ), (44619305931803/100000000000000 : ℝ), (341486808453/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16693141/80000000 : ℝ)|^4253 ≤ (3173710748933/25000000000000 : ℝ)^3229
        have hw : |(-16693141/80000000 : ℝ)|=(16693141/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418856259/10000000000 : ℝ)|^4253 ≤ (44619305931803/100000000000000 : ℝ)^3229
        have hw : |(5418856259/10000000000 : ℝ)|=(5418856259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047926749/2000000000 : ℝ)|^4253 ≤ (341486808453/800000000000 : ℝ)^3229
        have hw : |(1047926749/2000000000 : ℝ)|=(1047926749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675351001/5000000000 : ℝ)*x 0 + (-1089035489/5000000000 : ℝ)*x 1 + (5239633907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675351001/5000000000 : ℝ)^4253 ≤ (43881629284733/100000000000000 : ℝ)^3229 := by
    have hnat : (2675351001 : ℕ)^4253*100000000000000^3229 ≤ 43881629284733^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675351001 5000000000 43881629284733 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089035489/5000000000 : ℝ)^4253 ≤ (13432517911367/100000000000000 : ℝ)^3229 := by
    have hnat : (1089035489 : ℕ)^4253*100000000000000^3229 ≤ 13432517911367^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089035489 5000000000 13432517911367 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239633907/10000000000 : ℝ)^4253 ≤ (2667865799683/6250000000000 : ℝ)^3229 := by
    have hnat : (5239633907 : ℕ)^4253*6250000000000^3229 ≤ 2667865799683^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239633907 10000000000 2667865799683 6250000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675351001/5000000000 : ℝ), (-1089035489/5000000000 : ℝ), (5239633907/10000000000 : ℝ)] ![(43881629284733/100000000000000 : ℝ), (13432517911367/100000000000000 : ℝ), (2667865799683/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675351001/5000000000 : ℝ)|^4253 ≤ (43881629284733/100000000000000 : ℝ)^3229
        have hw : |(2675351001/5000000000 : ℝ)|=(2675351001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089035489/5000000000 : ℝ)|^4253 ≤ (13432517911367/100000000000000 : ℝ)^3229
        have hw : |(-1089035489/5000000000 : ℝ)|=(1089035489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239633907/10000000000 : ℝ)|^4253 ≤ (2667865799683/6250000000000 : ℝ)^3229
        have hw : |(5239633907/10000000000 : ℝ)|=(5239633907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535070203/1000000000 : ℝ)*x 0 + (5239633621/10000000000 : ℝ)*x 1 + (-1089035659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535070203/1000000000 : ℝ)^4253 ≤ (8776325917437/20000000000000 : ℝ)^3229 := by
    have hnat : (535070203 : ℕ)^4253*20000000000000^3229 ≤ 8776325917437^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535070203 1000000000 8776325917437 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239633621/10000000000 : ℝ)^4253 ≤ (42685849726073/100000000000000 : ℝ)^3229 := by
    have hnat : (5239633621 : ℕ)^4253*100000000000000^3229 ≤ 42685849726073^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239633621 10000000000 42685849726073 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089035659/5000000000 : ℝ)^4253 ≤ (3358130168291/25000000000000 : ℝ)^3229 := by
    have hnat : (1089035659 : ℕ)^4253*25000000000000^3229 ≤ 3358130168291^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089035659 5000000000 3358130168291 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535070203/1000000000 : ℝ), (5239633621/10000000000 : ℝ), (-1089035659/5000000000 : ℝ)] ![(8776325917437/20000000000000 : ℝ), (42685849726073/100000000000000 : ℝ), (3358130168291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535070203/1000000000 : ℝ)|^4253 ≤ (8776325917437/20000000000000 : ℝ)^3229
        have hw : |(535070203/1000000000 : ℝ)|=(535070203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239633621/10000000000 : ℝ)|^4253 ≤ (42685849726073/100000000000000 : ℝ)^3229
        have hw : |(5239633621/10000000000 : ℝ)|=(5239633621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1089035659/5000000000 : ℝ)|^4253 ≤ (3358130168291/25000000000000 : ℝ)^3229
        have hw : |(-1089035659/5000000000 : ℝ)|=(1089035659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339342291/10000000000 : ℝ)*x 0 + (831767211/2000000000 : ℝ)*x 1 + (565915199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339342291/10000000000 : ℝ)^4253 ≤ (16649898544889/50000000000000 : ℝ)^3229 := by
    have hnat : (4339342291 : ℕ)^4253*50000000000000^3229 ≤ 16649898544889^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339342291 10000000000 16649898544889 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831767211/2000000000 : ℝ)^4253 ≤ (7871868726309/25000000000000 : ℝ)^3229 := by
    have hnat : (831767211 : ℕ)^4253*25000000000000^3229 ≤ 7871868726309^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831767211 2000000000 7871868726309 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565915199/1250000000 : ℝ)^4253 ≤ (275099437443/781250000000 : ℝ)^3229 := by
    have hnat : (565915199 : ℕ)^4253*781250000000^3229 ≤ 275099437443^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565915199 1250000000 275099437443 781250000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339342291/10000000000 : ℝ), (831767211/2000000000 : ℝ), (565915199/1250000000 : ℝ)] ![(16649898544889/50000000000000 : ℝ), (7871868726309/25000000000000 : ℝ), (275099437443/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339342291/10000000000 : ℝ)|^4253 ≤ (16649898544889/50000000000000 : ℝ)^3229
        have hw : |(4339342291/10000000000 : ℝ)|=(4339342291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831767211/2000000000 : ℝ)|^4253 ≤ (7871868726309/25000000000000 : ℝ)^3229
        have hw : |(831767211/2000000000 : ℝ)|=(831767211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565915199/1250000000 : ℝ)|^4253 ≤ (275099437443/781250000000 : ℝ)^3229
        have hw : |(565915199/1250000000 : ℝ)|=(565915199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086656811/10000000000 : ℝ)*x 0 + (1048059709/2000000000 : ℝ)*x 1 + (1354547001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086656811/10000000000 : ℝ)^4253 ≤ (12694956671271/100000000000000 : ℝ)^3229 := by
    have hnat : (2086656811 : ℕ)^4253*100000000000000^3229 ≤ 12694956671271^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086656811 10000000000 12694956671271 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048059709/2000000000 : ℝ)^4253 ≤ (21346492339367/50000000000000 : ℝ)^3229 := by
    have hnat : (1048059709 : ℕ)^4253*50000000000000^3229 ≤ 21346492339367^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048059709 2000000000 21346492339367 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354547001/2500000000 : ℝ)^4253 ≤ (22306029315883/50000000000000 : ℝ)^3229 := by
    have hnat : (1354547001 : ℕ)^4253*50000000000000^3229 ≤ 22306029315883^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354547001 2500000000 22306029315883 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086656811/10000000000 : ℝ), (1048059709/2000000000 : ℝ), (1354547001/2500000000 : ℝ)] ![(12694956671271/100000000000000 : ℝ), (21346492339367/50000000000000 : ℝ), (22306029315883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086656811/10000000000 : ℝ)|^4253 ≤ (12694956671271/100000000000000 : ℝ)^3229
        have hw : |(-2086656811/10000000000 : ℝ)|=(2086656811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048059709/2000000000 : ℝ)|^4253 ≤ (21346492339367/50000000000000 : ℝ)^3229
        have hw : |(1048059709/2000000000 : ℝ)|=(1048059709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354547001/2500000000 : ℝ)|^4253 ≤ (22306029315883/50000000000000 : ℝ)^3229
        have hw : |(1354547001/2500000000 : ℝ)|=(1354547001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304810261/10000000000 : ℝ)*x 0 + (-1999517051/10000000000 : ℝ)*x 1 + (2709093971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304810261/10000000000 : ℝ)^4253 ≤ (1735463508649/4000000000000 : ℝ)^3229 := by
    have hnat : (5304810261 : ℕ)^4253*4000000000000^3229 ≤ 1735463508649^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304810261 10000000000 1735463508649 4000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999517051/10000000000 : ℝ)^4253 ≤ (3000338577553/25000000000000 : ℝ)^3229 := by
    have hnat : (1999517051 : ℕ)^4253*25000000000000^3229 ≤ 3000338577553^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999517051 10000000000 3000338577553 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709093971/5000000000 : ℝ)^4253 ≤ (22306028979691/50000000000000 : ℝ)^3229 := by
    have hnat : (2709093971 : ℕ)^4253*50000000000000^3229 ≤ 22306028979691^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709093971 5000000000 22306028979691 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304810261/10000000000 : ℝ), (-1999517051/10000000000 : ℝ), (2709093971/5000000000 : ℝ)] ![(1735463508649/4000000000000 : ℝ), (3000338577553/25000000000000 : ℝ), (22306028979691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304810261/10000000000 : ℝ)|^4253 ≤ (1735463508649/4000000000000 : ℝ)^3229
        have hw : |(5304810261/10000000000 : ℝ)|=(5304810261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999517051/10000000000 : ℝ)|^4253 ≤ (3000338577553/25000000000000 : ℝ)^3229
        have hw : |(-1999517051/10000000000 : ℝ)|=(1999517051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709093971/5000000000 : ℝ)|^4253 ≤ (22306028979691/50000000000000 : ℝ)^3229
        have hw : |(2709093971/5000000000 : ℝ)|=(2709093971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652405163/5000000000 : ℝ)*x 0 + (541818789/1000000000 : ℝ)*x 1 + (-1999517033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652405163/5000000000 : ℝ)^4253 ≤ (2711661776027/6250000000000 : ℝ)^3229 := by
    have hnat : (2652405163 : ℕ)^4253*6250000000000^3229 ≤ 2711661776027^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652405163 5000000000 2711661776027 6250000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541818789/1000000000 : ℝ)^4253 ≤ (44612057395447/100000000000000 : ℝ)^3229 := by
    have hnat : (541818789 : ℕ)^4253*100000000000000^3229 ≤ 44612057395447^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541818789 1000000000 44612057395447 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999517033/10000000000 : ℝ)^4253 ≤ (1500169270989/12500000000000 : ℝ)^3229 := by
    have hnat : (1999517033 : ℕ)^4253*12500000000000^3229 ≤ 1500169270989^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999517033 10000000000 1500169270989 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652405163/5000000000 : ℝ), (541818789/1000000000 : ℝ), (-1999517033/10000000000 : ℝ)] ![(2711661776027/6250000000000 : ℝ), (44612057395447/100000000000000 : ℝ), (1500169270989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652405163/5000000000 : ℝ)|^4253 ≤ (2711661776027/6250000000000 : ℝ)^3229
        have hw : |(2652405163/5000000000 : ℝ)|=(2652405163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541818789/1000000000 : ℝ)|^4253 ≤ (44612057395447/100000000000000 : ℝ)^3229
        have hw : |(541818789/1000000000 : ℝ)|=(541818789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999517033/10000000000 : ℝ)|^4253 ≤ (1500169270989/12500000000000 : ℝ)^3229
        have hw : |(-1999517033/10000000000 : ℝ)|=(1999517033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s4_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542421461/1250000000 : ℝ)*x 0 + (2262977349/5000000000 : ℝ)*x 1 + (2080105157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542421461/1250000000 : ℝ)^4253 ≤ (1665004711057/5000000000000 : ℝ)^3229 := by
    have hnat : (542421461 : ℕ)^4253*5000000000000^3229 ≤ 1665004711057^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542421461 1250000000 1665004711057 5000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262977349/5000000000 : ℝ)^4253 ≤ (8799681420513/25000000000000 : ℝ)^3229 := by
    have hnat : (2262977349 : ℕ)^4253*25000000000000^3229 ≤ 8799681420513^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262977349 5000000000 8799681420513 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080105157/5000000000 : ℝ)^4253 ≤ (31501180084311/100000000000000 : ℝ)^3229 := by
    have hnat : (2080105157 : ℕ)^4253*100000000000000^3229 ≤ 31501180084311^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080105157 5000000000 31501180084311 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542421461/1250000000 : ℝ), (2262977349/5000000000 : ℝ), (2080105157/5000000000 : ℝ)] ![(1665004711057/5000000000000 : ℝ), (8799681420513/25000000000000 : ℝ), (31501180084311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542421461/1250000000 : ℝ)|^4253 ≤ (1665004711057/5000000000000 : ℝ)^3229
        have hw : |(542421461/1250000000 : ℝ)|=(542421461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262977349/5000000000 : ℝ)|^4253 ≤ (8799681420513/25000000000000 : ℝ)^3229
        have hw : |(2262977349/5000000000 : ℝ)|=(2262977349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2080105157/5000000000 : ℝ)|^4253 ≤ (31501180084311/100000000000000 : ℝ)^3229
        have hw : |(2080105157/5000000000 : ℝ)|=(2080105157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3013/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10957/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3013/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3013/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3013/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3013/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3013/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3013/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5331/50000 : ℝ) ^ (1063/256 : ℝ) ≤ (9188656390160337/100000000000000000000 : ℝ) := by
    have hpowers : (5331/50000 : ℝ)^1063 ≤ (9188656390160337/100000000000000000000 : ℝ)^256 := by
      have hnat : (5331 : ℕ)^1063*100000000000000000000^256 ≤ 9188656390160337^256*50000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5331 50000 9188656390160337 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5331/50000 : ℝ)) (X := (9188656390160337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3013/20000 : ℝ) ^ (1063/256 : ℝ) ≤ (38605153143205887/100000000000000000000 : ℝ) := by
    have hpowers : (3013/20000 : ℝ)^1063 ≤ (38605153143205887/100000000000000000000 : ℝ)^256 := by
      have hnat : (3013 : ℕ)^1063*100000000000000000000^256 ≤ 38605153143205887^256*20000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3013 20000 38605153143205887 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3013/20000 : ℝ)) (X := (38605153143205887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009188656390160337/50000000000000000000 : ℝ) ≤ (5000221272997437/5000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50009188656390160337/50000000000000000000 : ℝ)^256 ≤ (5000221272997437/5000000000000000 : ℝ)^1063 := by
      have hnat : (50009188656390160337 : ℕ)^256*5000000000000000^1063 ≤ 5000221272997437^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009188656390160337 50000000000000000000 5000221272997437 5000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000221272997437/5000000000000000 : ℝ)) (X := (50009188656390160337/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252987113095835389/6250000000000000000 : ℝ) ≤ (2500287699815763/2500000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (6252987113095835389/6250000000000000000 : ℝ)^256 ≤ (2500287699815763/2500000000000000 : ℝ)^1063 := by
      have hnat : (6252987113095835389 : ℕ)^256*2500000000000000^1063 ≤ 2500287699815763^1063*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252987113095835389 6250000000000000000 2500287699815763 2500000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500287699815763/2500000000000000 : ℝ)) (X := (6252987113095835389/6250000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038605153143205887/50000000000000000000 : ℝ) ≤ (1000185905253123/1000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50038605153143205887/50000000000000000000 : ℝ)^256 ≤ (1000185905253123/1000000000000000 : ℝ)^1063 := by
      have hnat : (50038605153143205887 : ℕ)^256*1000000000000000^1063 ≤ 1000185905253123^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038605153143205887 50000000000000000000 1000185905253123 1000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000185905253123/1000000000000000 : ℝ)) (X := (50038605153143205887/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9188656390160337/100000000000000000000 : ℝ) ≤ ((880336914746496051/880600000000000000 : ℝ)+2*(354126634089/220150000000000 : ℝ)*(5331/50000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (880336914746496051/880600000000000000 : ℝ)+2*(354126634089/220150000000000 : ℝ)*(5331/50000 : ℝ)=(5000221272997437/5000000000000000 : ℝ) by norm_num, show 1+2*(9188656390160337/100000000000000000000 : ℝ)=(50009188656390160337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38605153143205887/100000000000000000000 : ℝ)+(9188656390160337/100000000000000000000 : ℝ) ≤ ((880336914746496051/880600000000000000 : ℝ)+(354126634089/220150000000000 : ℝ)*((3013/20000 : ℝ)+(5331/50000 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (880336914746496051/880600000000000000 : ℝ)+(354126634089/220150000000000 : ℝ)*((3013/20000 : ℝ)+(5331/50000 : ℝ))=(2500287699815763/2500000000000000 : ℝ) by norm_num, show 1+(38605153143205887/100000000000000000000 : ℝ)+(9188656390160337/100000000000000000000 : ℝ)=(6252987113095835389/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38605153143205887/100000000000000000000 : ℝ) ≤ ((880336914746496051/880600000000000000 : ℝ)+2*(354126634089/220150000000000 : ℝ)*(3013/20000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (880336914746496051/880600000000000000 : ℝ)+2*(354126634089/220150000000000 : ℝ)*(3013/20000 : ℝ)=(1000185905253123/1000000000000000 : ℝ) by norm_num, show 1+2*(38605153143205887/100000000000000000000 : ℝ)=(50038605153143205887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (880336914746496051/880600000000000000 : ℝ)*(X 1 0+X 2 0)+(354126634089/220150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (3013/20000 : ℝ)) (c := (880336914746496051/880600000000000000 : ℝ)) (alpha := (354126634089/220150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (880336914746496051/880600000000000000 : ℝ)*(X 0 1+X 2 1)+(354126634089/220150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (3013/20000 : ℝ)) (c := (880336914746496051/880600000000000000 : ℝ)) (alpha := (354126634089/220150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (880336914746496051/880600000000000000 : ℝ)*(X 0 2+X 1 2)+(354126634089/220150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (3013/20000 : ℝ)) (c := (880336914746496051/880600000000000000 : ℝ)) (alpha := (354126634089/220150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16693141/80000000 : ℝ)*X 0 0+(5418856259/10000000000 : ℝ)*X 0 1+(1047926749/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675351001/5000000000 : ℝ)*X 1 0+(-1089035489/5000000000 : ℝ)*X 1 1+(5239633907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535070203/1000000000 : ℝ)*X 2 0+(5239633621/10000000000 : ℝ)*X 2 1+(-1089035659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339342291/10000000000 : ℝ)*X 0 0+(831767211/2000000000 : ℝ)*X 0 1+(565915199/1250000000 : ℝ)*X 0 2+(4339342291/10000000000 : ℝ)*X 1 0+(831767211/2000000000 : ℝ)*X 1 1+(565915199/1250000000 : ℝ)*X 1 2+(4339342291/10000000000 : ℝ)*X 2 0+(831767211/2000000000 : ℝ)*X 2 1+(565915199/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2086656811/10000000000 : ℝ)*X 0 0+(1048059709/2000000000 : ℝ)*X 0 1+(1354547001/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304810261/10000000000 : ℝ)*X 1 0+(-1999517051/10000000000 : ℝ)*X 1 1+(2709093971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652405163/5000000000 : ℝ)*X 2 0+(541818789/1000000000 : ℝ)*X 2 1+(-1999517033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((542421461/1250000000 : ℝ)*X 0 0+(2262977349/5000000000 : ℝ)*X 0 1+(2080105157/5000000000 : ℝ)*X 0 2+(542421461/1250000000 : ℝ)*X 1 0+(2262977349/5000000000 : ℝ)*X 1 1+(2080105157/5000000000 : ℝ)*X 1 2+(542421461/1250000000 : ℝ)*X 2 0+(2262977349/5000000000 : ℝ)*X 2 1+(2080105157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115294743377779544766073491/11007500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2248621541/100000000000000 : ℝ)*(base19) + (34980587/1562500000000 : ℝ)*(base23) + (4180241/20000000000000 : ℝ)*(lower2) + (233357793/50000000000000 : ℝ)*(upper3) + (50035027/100000000000000 : ℝ)*(upper5) + (1036700440967549/25000000000000 : ℝ)*(major0) + (1036700440967549/25000000000000 : ℝ)*(major1) + (1036700440967549/25000000000000 : ℝ)*(major2) + (5579708803907261/100000000000000 : ℝ)*(sp0) + (1115949085752681/20000000000000 : ℝ)*(sp1) + (5579745438627377/100000000000000 : ℝ)*(sp2) + (2713829964373457/100000000000000 : ℝ)*(sp3) + (9718369421/25000000000000 : ℝ)*(sp4) + (25536842023/100000000000000 : ℝ)*(sp7) + (67846387530387/2500000000000 : ℝ)*(f.failure) + (1115949535476989/20000000000000 : ℝ)*(f.sum) + (17233525312229/11007500000000000000000000000 : ℝ)*base65 + (9113418195613353/1295000000000000000000000000000 : ℝ)*base68 + (7614198481418353/1295000000000000000000000000000 : ℝ)*base70 + (8920228869248353/1295000000000000000000000000000 : ℝ)*base72 + (61100860653403/22015000000000000000000000000 : ℝ)*base73 + (15542380340848353/1295000000000000000000000000000 : ℝ)*base76 + (5047710726748353/1295000000000000000000000000000 : ℝ)*base78 + (2819298276323353/1295000000000000000000000000000 : ℝ)*base80 + (5346879001543/1375937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1407881/125000000000000000000 : ℝ)*base89 + (1407881/125000000000000000000 : ℝ)*base91 + (1407881/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101079208102515670977108141/22015000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (380583697/50000000000000 : ℝ)*(base19) + (91095187/10000000000000 : ℝ)*(base23) + (9972193/20000000000000 : ℝ)*(upper3) + (4253281/10000000000000 : ℝ)*(lower4) + (134548667/100000000000000 : ℝ)*(upper5) + (2088905014168803/50000000000000 : ℝ)*(major0) + (2088905014168803/50000000000000 : ℝ)*(major1) + (2088905014168803/50000000000000 : ℝ)*(major2) + (1478759677/10000000000000 : ℝ)*(sp1) + (3717900309/25000000000000 : ℝ)*(sp2) + (2810735592579333/50000000000000 : ℝ)*(sp4) + (2810727818197251/50000000000000 : ℝ)*(sp5) + (5621455402605559/100000000000000 : ℝ)*(sp6) + (2734148718470573/100000000000000 : ℝ)*(sp7) + (2734148718470573/100000000000000 : ℝ)*(f.failure) + (2810735592579333/50000000000000 : ℝ)*(f.sum) + (57770930449699/11007500000000000000000000000 : ℝ)*base65 + (10133656585585591/2590000000000000000000000000000 : ℝ)*base68 + (6082619189834409/2590000000000000000000000000000 : ℝ)*base69 + (16043181101834409/2590000000000000000000000000000 : ℝ)*base71 + (7243430808561/2751875000000000000000000000 : ℝ)*base73 + (17924952270065591/2590000000000000000000000000000 : ℝ)*base76 + (20594865874154409/2590000000000000000000000000000 : ℝ)*base77 + (1683749115774409/2590000000000000000000000000000 : ℝ)*base79 + (53428930791463/22015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (23867401/5000000000000000000000 : ℝ)*base90 + (23867401/5000000000000000000000 : ℝ)*base92 + (23867401/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1293_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3013/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1293_s5_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-417400001/2000000000 : ℝ)*x 0 + (2707916941/5000000000 : ℝ)*x 1 + (1310605283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417400001/2000000000 : ℝ)^4253 ≤ (1269770683497/10000000000000 : ℝ)^3229 := by
    have hnat : (417400001 : ℕ)^4253*10000000000000^3229 ≤ 1269770683497^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417400001 2000000000 1269770683497 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707916941/5000000000 : ℝ)^4253 ≤ (11146632543577/25000000000000 : ℝ)^3229 := by
    have hnat : (2707916941 : ℕ)^4253*25000000000000^3229 ≤ 11146632543577^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707916941 5000000000 11146632543577 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310605283/2500000000 : ℝ)^4253 ≤ (21357881486913/50000000000000 : ℝ)^3229 := by
    have hnat : (1310605283 : ℕ)^4253*50000000000000^3229 ≤ 21357881486913^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310605283 2500000000 21357881486913 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417400001/2000000000 : ℝ), (2707916941/5000000000 : ℝ), (1310605283/2500000000 : ℝ)] ![(1269770683497/10000000000000 : ℝ), (11146632543577/25000000000000 : ℝ), (21357881486913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417400001/2000000000 : ℝ)|^4253 ≤ (1269770683497/10000000000000 : ℝ)^3229
        have hw : |(-417400001/2000000000 : ℝ)|=(417400001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707916941/5000000000 : ℝ)|^4253 ≤ (11146632543577/25000000000000 : ℝ)^3229
        have hw : |(2707916941/5000000000 : ℝ)|=(2707916941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310605283/2500000000 : ℝ)|^4253 ≤ (21357881486913/50000000000000 : ℝ)^3229
        have hw : |(1310605283/2500000000 : ℝ)|=(1310605283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349935057/10000000000 : ℝ)*x 0 + (-135963003/625000000 : ℝ)*x 1 + (1048484239/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349935057/10000000000 : ℝ)^4253 ≤ (43873345025757/100000000000000 : ℝ)^3229 := by
    have hnat : (5349935057 : ℕ)^4253*100000000000000^3229 ≤ 43873345025757^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349935057 10000000000 43873345025757 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135963003/625000000 : ℝ)^4253 ≤ (13410891310559/100000000000000 : ℝ)^3229 := by
    have hnat : (135963003 : ℕ)^4253*100000000000000^3229 ≤ 13410891310559^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135963003 625000000 13410891310559 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048484239/2000000000 : ℝ)^4253 ≤ (21357881824973/50000000000000 : ℝ)^3229 := by
    have hnat : (1048484239 : ℕ)^4253*50000000000000^3229 ≤ 21357881824973^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048484239 2000000000 21357881824973 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349935057/10000000000 : ℝ), (-135963003/625000000 : ℝ), (1048484239/2000000000 : ℝ)] ![(43873345025757/100000000000000 : ℝ), (13410891310559/100000000000000 : ℝ), (21357881824973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349935057/10000000000 : ℝ)|^4253 ≤ (43873345025757/100000000000000 : ℝ)^3229
        have hw : |(5349935057/10000000000 : ℝ)|=(5349935057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135963003/625000000 : ℝ)|^4253 ≤ (13410891310559/100000000000000 : ℝ)^3229
        have hw : |(-135963003/625000000 : ℝ)|=(135963003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048484239/2000000000 : ℝ)|^4253 ≤ (21357881824973/50000000000000 : ℝ)^3229
        have hw : |(1048484239/2000000000 : ℝ)|=(1048484239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534993491/1000000000 : ℝ)*x 0 + (5242421513/10000000000 : ℝ)*x 1 + (-2175407823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534993491/1000000000 : ℝ)^4253 ≤ (43873343437953/100000000000000 : ℝ)^3229 := by
    have hnat : (534993491 : ℕ)^4253*100000000000000^3229 ≤ 43873343437953^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534993491 1000000000 43873343437953 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242421513/10000000000 : ℝ)^4253 ≤ (21357883531373/50000000000000 : ℝ)^3229 := by
    have hnat : (5242421513 : ℕ)^4253*50000000000000^3229 ≤ 21357883531373^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242421513 10000000000 21357883531373 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175407823/10000000000 : ℝ)^4253 ≤ (13410889483609/100000000000000 : ℝ)^3229 := by
    have hnat : (2175407823 : ℕ)^4253*100000000000000^3229 ≤ 13410889483609^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175407823 10000000000 13410889483609 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534993491/1000000000 : ℝ), (5242421513/10000000000 : ℝ), (-2175407823/10000000000 : ℝ)] ![(43873343437953/100000000000000 : ℝ), (21357883531373/50000000000000 : ℝ), (13410889483609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534993491/1000000000 : ℝ)|^4253 ≤ (43873343437953/100000000000000 : ℝ)^3229
        have hw : |(534993491/1000000000 : ℝ)|=(534993491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242421513/10000000000 : ℝ)|^4253 ≤ (21357883531373/50000000000000 : ℝ)^3229
        have hw : |(5242421513/10000000000 : ℝ)|=(5242421513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175407823/10000000000 : ℝ)|^4253 ≤ (13410889483609/100000000000000 : ℝ)^3229
        have hw : |(-2175407823/10000000000 : ℝ)|=(2175407823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4339553083/10000000000 : ℝ)*x 0 + (4164782647/10000000000 : ℝ)*x 1 + (452132241/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339553083/10000000000 : ℝ)^4253 ≤ (33301927692539/100000000000000 : ℝ)^3229 := by
    have hnat : (4339553083 : ℕ)^4253*100000000000000^3229 ≤ 33301927692539^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339553083 10000000000 33301927692539 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4164782647/10000000000 : ℝ)^4253 ≤ (15773394638569/50000000000000 : ℝ)^3229 := by
    have hnat : (4164782647 : ℕ)^4253*50000000000000^3229 ≤ 15773394638569^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164782647 10000000000 15773394638569 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452132241/1000000000 : ℝ)^4253 ≤ (35151283011729/100000000000000 : ℝ)^3229 := by
    have hnat : (452132241 : ℕ)^4253*100000000000000^3229 ≤ 35151283011729^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452132241 1000000000 35151283011729 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339553083/10000000000 : ℝ), (4164782647/10000000000 : ℝ), (452132241/1000000000 : ℝ)] ![(33301927692539/100000000000000 : ℝ), (15773394638569/50000000000000 : ℝ), (35151283011729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339553083/10000000000 : ℝ)|^4253 ≤ (33301927692539/100000000000000 : ℝ)^3229
        have hw : |(4339553083/10000000000 : ℝ)|=(4339553083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4164782647/10000000000 : ℝ)|^4253 ≤ (15773394638569/50000000000000 : ℝ)^3229
        have hw : |(4164782647/10000000000 : ℝ)|=(4164782647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452132241/1000000000 : ℝ)|^4253 ≤ (35151283011729/100000000000000 : ℝ)^3229
        have hw : |(452132241/1000000000 : ℝ)|=(452132241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087013293/10000000000 : ℝ)*x 0 + (1048608769/2000000000 : ℝ)*x 1 + (5415207719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087013293/10000000000 : ℝ)^4253 ≤ (12697813320413/100000000000000 : ℝ)^3229 := by
    have hnat : (2087013293 : ℕ)^4253*100000000000000^3229 ≤ 12697813320413^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087013293 10000000000 12697813320413 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048608769/2000000000 : ℝ)^4253 ≤ (5340305762599/12500000000000 : ℝ)^3229 := by
    have hnat : (1048608769 : ℕ)^4253*12500000000000^3229 ≤ 5340305762599^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048608769 2000000000 5340305762599 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415207719/10000000000 : ℝ)^4253 ≤ (5572467569973/12500000000000 : ℝ)^3229 := by
    have hnat : (5415207719 : ℕ)^4253*12500000000000^3229 ≤ 5572467569973^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415207719 10000000000 5572467569973 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087013293/10000000000 : ℝ), (1048608769/2000000000 : ℝ), (5415207719/10000000000 : ℝ)] ![(12697813320413/100000000000000 : ℝ), (5340305762599/12500000000000 : ℝ), (5572467569973/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087013293/10000000000 : ℝ)|^4253 ≤ (12697813320413/100000000000000 : ℝ)^3229
        have hw : |(-2087013293/10000000000 : ℝ)|=(2087013293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048608769/2000000000 : ℝ)|^4253 ≤ (5340305762599/12500000000000 : ℝ)^3229
        have hw : |(1048608769/2000000000 : ℝ)|=(1048608769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415207719/10000000000 : ℝ)|^4253 ≤ (5572467569973/12500000000000 : ℝ)^3229
        have hw : |(5415207719/10000000000 : ℝ)|=(5415207719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305531371/10000000000 : ℝ)*x 0 + (-2002621579/10000000000 : ℝ)*x 1 + (2707603863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305531371/10000000000 : ℝ)^4253 ≤ (21697177989039/50000000000000 : ℝ)^3229 := by
    have hnat : (5305531371 : ℕ)^4253*50000000000000^3229 ≤ 21697177989039^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305531371 10000000000 21697177989039 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002621579/10000000000 : ℝ)^4253 ≤ (1503237921739/12500000000000 : ℝ)^3229 := by
    have hnat : (2002621579 : ℕ)^4253*12500000000000^3229 ≤ 1503237921739^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002621579 10000000000 1503237921739 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707603863/5000000000 : ℝ)^4253 ≤ (8915948127137/20000000000000 : ℝ)^3229 := by
    have hnat : (2707603863 : ℕ)^4253*20000000000000^3229 ≤ 8915948127137^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707603863 5000000000 8915948127137 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305531371/10000000000 : ℝ), (-2002621579/10000000000 : ℝ), (2707603863/5000000000 : ℝ)] ![(21697177989039/50000000000000 : ℝ), (1503237921739/12500000000000 : ℝ), (8915948127137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305531371/10000000000 : ℝ)|^4253 ≤ (21697177989039/50000000000000 : ℝ)^3229
        have hw : |(5305531371/10000000000 : ℝ)|=(5305531371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002621579/10000000000 : ℝ)|^4253 ≤ (1503237921739/12500000000000 : ℝ)^3229
        have hw : |(-2002621579/10000000000 : ℝ)|=(2002621579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707603863/5000000000 : ℝ)|^4253 ≤ (8915948127137/20000000000000 : ℝ)^3229
        have hw : |(2707603863/5000000000 : ℝ)|=(2707603863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305531389/10000000000 : ℝ)*x 0 + (541520771/1000000000 : ℝ)*x 1 + (-250327697/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305531389/10000000000 : ℝ)^4253 ≤ (4339435617199/10000000000000 : ℝ)^3229 := by
    have hnat : (5305531389 : ℕ)^4253*10000000000000^3229 ≤ 4339435617199^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305531389 10000000000 4339435617199 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541520771/1000000000 : ℝ)^4253 ≤ (44579740462197/100000000000000 : ℝ)^3229 := by
    have hnat : (541520771 : ℕ)^4253*100000000000000^3229 ≤ 44579740462197^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541520771 1000000000 44579740462197 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250327697/1250000000 : ℝ)^4253 ≤ (1503237918773/12500000000000 : ℝ)^3229 := by
    have hnat : (250327697 : ℕ)^4253*12500000000000^3229 ≤ 1503237918773^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250327697 1250000000 1503237918773 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305531389/10000000000 : ℝ), (541520771/1000000000 : ℝ), (-250327697/1250000000 : ℝ)] ![(4339435617199/10000000000000 : ℝ), (44579740462197/100000000000000 : ℝ), (1503237918773/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305531389/10000000000 : ℝ)|^4253 ≤ (4339435617199/10000000000000 : ℝ)^3229
        have hw : |(5305531389/10000000000 : ℝ)|=(5305531389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541520771/1000000000 : ℝ)|^4253 ≤ (44579740462197/100000000000000 : ℝ)^3229
        have hw : |(541520771/1000000000 : ℝ)|=(541520771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250327697/1250000000 : ℝ)|^4253 ≤ (1503237918773/12500000000000 : ℝ)^3229
        have hw : |(-250327697/1250000000 : ℝ)|=(250327697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s5_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (433958039/1000000000 : ℝ)*x 0 + (565005241/1250000000 : ℝ)*x 1 + (833213827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433958039/1000000000 : ℝ)^4253 ≤ (33302203703373/100000000000000 : ℝ)^3229 := by
    have hnat : (433958039 : ℕ)^4253*100000000000000^3229 ≤ 33302203703373^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433958039 1000000000 33302203703373 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565005241/1250000000 : ℝ)^4253 ≤ (7027634274353/20000000000000 : ℝ)^3229 := by
    have hnat : (565005241 : ℕ)^4253*20000000000000^3229 ≤ 7027634274353^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565005241 1250000000 7027634274353 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833213827/2000000000 : ℝ)^4253 ≤ (31559624906571/100000000000000 : ℝ)^3229 := by
    have hnat : (833213827 : ℕ)^4253*100000000000000^3229 ≤ 31559624906571^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833213827 2000000000 31559624906571 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433958039/1000000000 : ℝ), (565005241/1250000000 : ℝ), (833213827/2000000000 : ℝ)] ![(33302203703373/100000000000000 : ℝ), (7027634274353/20000000000000 : ℝ), (31559624906571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433958039/1000000000 : ℝ)|^4253 ≤ (33302203703373/100000000000000 : ℝ)^3229
        have hw : |(433958039/1000000000 : ℝ)|=(433958039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565005241/1250000000 : ℝ)|^4253 ≤ (7027634274353/20000000000000 : ℝ)^3229
        have hw : |(565005241/1250000000 : ℝ)|=(565005241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833213827/2000000000 : ℝ)|^4253 ≤ (31559624906571/100000000000000 : ℝ)^3229
        have hw : |(833213827/2000000000 : ℝ)|=(833213827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11017/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10957/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10957/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10957/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10957/100000 : ℝ) ^ (1063/256 : ℝ) ≤ (10291286605339901/100000000000000000000 : ℝ) := by
    have hpowers : (10957/100000 : ℝ)^1063 ≤ (10291286605339901/100000000000000000000 : ℝ)^256 := by
      have hnat : (10957 : ℕ)^1063*100000000000000000000^256 ≤ 10291286605339901^256*100000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10957 100000 10291286605339901 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10957/100000 : ℝ)) (X := (10291286605339901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (1063/256 : ℝ) ≤ (4420269549822431/12500000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^1063 ≤ (4420269549822431/12500000000000000000 : ℝ)^256 := by
      have hnat : (59 : ℕ)^1063*12500000000000000000^256 ≤ 4420269549822431^256*400^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 4420269549822431 12500000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (4420269549822431/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010291286605339901/50000000000000000000 : ℝ) ≤ (1250061955869253/1250000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50010291286605339901/50000000000000000000 : ℝ)^256 ≤ (1250061955869253/1250000000000000 : ℝ)^1063 := by
      have hnat : (50010291286605339901 : ℕ)^256*1250000000000000^1063 ≤ 1250061955869253^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010291286605339901 50000000000000000000 1250061955869253 1250000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250061955869253/1250000000000000 : ℝ)) (X := (50010291286605339901/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045653443003919349/100000000000000000000 : ℝ) ≤ (400043970862141/400000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (100045653443003919349/100000000000000000000 : ℝ)^256 ≤ (400043970862141/400000000000000 : ℝ)^1063 := by
      have hnat : (100045653443003919349 : ℕ)^256*400000000000000^1063 ≤ 400043970862141^1063*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045653443003919349 100000000000000000000 400043970862141 400000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400043970862141/400000000000000 : ℝ)) (X := (100045653443003919349/100000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254420269549822431/6250000000000000000 : ℝ) ≤ (5000851448076513/5000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (6254420269549822431/6250000000000000000 : ℝ)^256 ≤ (5000851448076513/5000000000000000 : ℝ)^1063 := by
      have hnat : (6254420269549822431 : ℕ)^256*5000000000000000^1063 ≤ 5000851448076513^1063*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254420269549822431 6250000000000000000 5000851448076513 5000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000851448076513/5000000000000000 : ℝ)) (X := (6254420269549822431/6250000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10291286605339901/100000000000000000000 : ℝ) ≤ ((18959326079711574059/18965000000000000000 : ℝ)+2*(603624599501/379300000000000 : ℝ)*(10957/100000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (18959326079711574059/18965000000000000000 : ℝ)+2*(603624599501/379300000000000 : ℝ)*(10957/100000 : ℝ)=(1250061955869253/1250000000000000 : ℝ) by norm_num, show 1+2*(10291286605339901/100000000000000000000 : ℝ)=(50010291286605339901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4420269549822431/12500000000000000000 : ℝ)+(10291286605339901/100000000000000000000 : ℝ) ≤ ((18959326079711574059/18965000000000000000 : ℝ)+(603624599501/379300000000000 : ℝ)*((59/400 : ℝ)+(10957/100000 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (18959326079711574059/18965000000000000000 : ℝ)+(603624599501/379300000000000 : ℝ)*((59/400 : ℝ)+(10957/100000 : ℝ))=(400043970862141/400000000000000 : ℝ) by norm_num, show 1+(4420269549822431/12500000000000000000 : ℝ)+(10291286605339901/100000000000000000000 : ℝ)=(100045653443003919349/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4420269549822431/12500000000000000000 : ℝ) ≤ ((18959326079711574059/18965000000000000000 : ℝ)+2*(603624599501/379300000000000 : ℝ)*(59/400 : ℝ))^(1063/256 : ℝ) := by
    rw [show (18959326079711574059/18965000000000000000 : ℝ)+2*(603624599501/379300000000000 : ℝ)*(59/400 : ℝ)=(5000851448076513/5000000000000000 : ℝ) by norm_num, show 1+2*(4420269549822431/12500000000000000000 : ℝ)=(6254420269549822431/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18959326079711574059/18965000000000000000 : ℝ)*(X 1 0+X 2 0)+(603624599501/379300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (18959326079711574059/18965000000000000000 : ℝ)) (alpha := (603624599501/379300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18959326079711574059/18965000000000000000 : ℝ)*(X 0 1+X 2 1)+(603624599501/379300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (18959326079711574059/18965000000000000000 : ℝ)) (alpha := (603624599501/379300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18959326079711574059/18965000000000000000 : ℝ)*(X 0 2+X 1 2)+(603624599501/379300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (10957/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (18959326079711574059/18965000000000000000 : ℝ)) (alpha := (603624599501/379300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-417400001/2000000000 : ℝ)*X 0 0+(2707916941/5000000000 : ℝ)*X 0 1+(1310605283/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349935057/10000000000 : ℝ)*X 1 0+(-135963003/625000000 : ℝ)*X 1 1+(1048484239/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534993491/1000000000 : ℝ)*X 2 0+(5242421513/10000000000 : ℝ)*X 2 1+(-2175407823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4339553083/10000000000 : ℝ)*X 0 0+(4164782647/10000000000 : ℝ)*X 0 1+(452132241/1000000000 : ℝ)*X 0 2+(4339553083/10000000000 : ℝ)*X 1 0+(4164782647/10000000000 : ℝ)*X 1 1+(452132241/1000000000 : ℝ)*X 1 2+(4339553083/10000000000 : ℝ)*X 2 0+(4164782647/10000000000 : ℝ)*X 2 1+(452132241/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2087013293/10000000000 : ℝ)*X 0 0+(1048608769/2000000000 : ℝ)*X 0 1+(5415207719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305531371/10000000000 : ℝ)*X 1 0+(-2002621579/10000000000 : ℝ)*X 1 1+(2707603863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305531389/10000000000 : ℝ)*X 2 0+(541520771/1000000000 : ℝ)*X 2 1+(-250327697/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((433958039/1000000000 : ℝ)*X 0 0+(565005241/1250000000 : ℝ)*X 0 1+(833213827/2000000000 : ℝ)*X 0 2+(433958039/1000000000 : ℝ)*X 1 0+(565005241/1250000000 : ℝ)*X 1 1+(833213827/2000000000 : ℝ)*X 1 2+(433958039/1000000000 : ℝ)*X 2 0+(565005241/1250000000 : ℝ)*X 2 1+(833213827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1947035891089115589829143339/237062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (863480407/100000000000000 : ℝ)*(base19) + (31585109/5000000000000 : ℝ)*(base23) + (14350939/25000000000000 : ℝ)*(lower2) + (9708937/50000000000000 : ℝ)*(lower3) + (2142852507944693/50000000000000 : ℝ)*(major0) + (2142852507944693/50000000000000 : ℝ)*(major1) + (2142852507944693/50000000000000 : ℝ)*(major2) + (5766618562378979/100000000000000 : ℝ)*(sp0) + (5766644700725493/100000000000000 : ℝ)*(sp1) + (2883324512664259/50000000000000 : ℝ)*(sp2) + (2804748287540411/100000000000000 : ℝ)*(sp3) + (31094651719/100000000000000 : ℝ)*(sp4) + (2046412399/50000000000000 : ℝ)*(sp5) + (1476679393/12500000000000 : ℝ)*(sp7) + (701190025243889/25000000000000 : ℝ)*(f.failure) + (2883324828515349/50000000000000 : ℝ)*(f.sum) + (31081216157271/18965000000000000000000000000 : ℝ)*base65 + (369702214223668887/948250000000000000000000000000000 : ℝ)*base67 + (3700864109548418887/948250000000000000000000000000000 : ℝ)*base69 + (6748335457961168887/948250000000000000000000000000000 : ℝ)*base71 + (98548935643891/18965000000000000000000000000 : ℝ)*base73 + (1634379451737081113/948250000000000000000000000000000 : ℝ)*base76 + (4342893353147918887/948250000000000000000000000000000 : ℝ)*base77 + (8011438736250418887/948250000000000000000000000000000 : ℝ)*base79 + (11363396237677/9482500000000000000000000000 : ℝ)*base82 + (6909507/1250000000000000000000 : ℝ)*base89 + (6909507/1250000000000000000000 : ℝ)*base91 + (6909507/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1151777762397197949704201667/189650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53941861/5000000000000 : ℝ)*(base19) + (1185039731/100000000000000 : ℝ)*(base23) + (30971461/25000000000000 : ℝ)*(upper3) + (1549381/4000000000000 : ℝ)*(lower4) + (126781241/100000000000000 : ℝ)*(upper5) + (863349484512371/20000000000000 : ℝ)*(major0) + (863349484512371/20000000000000 : ℝ)*(major1) + (863349484512371/20000000000000 : ℝ)*(major2) + (21691766309/100000000000000 : ℝ)*(sp1) + (23303520513/100000000000000 : ℝ)*(sp2) + (5808418980243483/100000000000000 : ℝ)*(sp4) + (5808396209639953/100000000000000 : ℝ)*(sp5) + (2904197245841619/50000000000000 : ℝ)*(sp6) + (353134457805129/12500000000000 : ℝ)*(sp7) + (353134457805129/12500000000000 : ℝ)*(f.failure) + (5808418980243483/100000000000000 : ℝ)*(f.sum) + (5636889137899/1896500000000000000000000000 : ℝ)*base65 + (577989143686566111/379300000000000000000000000000000 : ℝ)*base68 + (3866213201230366111/379300000000000000000000000000000 : ℝ)*base70 + (696907592609066111/379300000000000000000000000000000 : ℝ)*base72 + (2375247584219/379300000000000000000000000 : ℝ)*base74 + (1136241419088833889/379300000000000000000000000000000 : ℝ)*base75 + (327813127923866111/379300000000000000000000000000000 : ℝ)*base78 + (507245425303233889/379300000000000000000000000000000 : ℝ)*base79 + (15555148190649/1896500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6137627/625000000000000000000 : ℝ)*base89 + (6137627/625000000000000000000 : ℝ)*base91 + (6137627/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1293_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10957/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1293_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1293_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1293_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1293_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11017/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1293_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

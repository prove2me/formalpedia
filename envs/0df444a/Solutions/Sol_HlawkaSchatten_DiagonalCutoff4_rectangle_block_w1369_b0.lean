-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1369_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:19:43.485057+00:00
-- url     : https://prove2.me/submissions/2d87a7e9-273f-4948-a9c9-3225439be580

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
theorem support_rectangle_w1369_s0_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-896645843/5000000000 : ℝ)*x 0 + (2992668459/5000000000 : ℝ)*x 1 + (4817309991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896645843/5000000000 : ℝ)^4329 ≤ (5264740050839/50000000000000 : ℝ)^3305 := by
    have hnat : (896645843 : ℕ)^4329*50000000000000^3305 ≤ 5264740050839^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896645843 5000000000 5264740050839 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2992668459/5000000000 : ℝ)^4329 ≤ (2552661150453/5000000000000 : ℝ)^3305 := by
    have hnat : (2992668459 : ℕ)^4329*5000000000000^3305 ≤ 2552661150453^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992668459 5000000000 2552661150453 5000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817309991/10000000000 : ℝ)^4329 ≤ (19208648442451/50000000000000 : ℝ)^3305 := by
    have hnat : (4817309991 : ℕ)^4329*50000000000000^3305 ≤ 19208648442451^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817309991 10000000000 19208648442451 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-896645843/5000000000 : ℝ), (2992668459/5000000000 : ℝ), (4817309991/10000000000 : ℝ)] ![(5264740050839/50000000000000 : ℝ), (2552661150453/5000000000000 : ℝ), (19208648442451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-896645843/5000000000 : ℝ)|^4329 ≤ (5264740050839/50000000000000 : ℝ)^3305
        have hw : |(-896645843/5000000000 : ℝ)|=(896645843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2992668459/5000000000 : ℝ)|^4329 ≤ (2552661150453/5000000000000 : ℝ)^3305
        have hw : |(2992668459/5000000000 : ℝ)|=(2992668459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817309991/10000000000 : ℝ)|^4329 ≤ (19208648442451/50000000000000 : ℝ)^3305
        have hw : |(4817309991/10000000000 : ℝ)|=(4817309991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1374697869/2500000000 : ℝ)*x 0 + (-1227950341/5000000000 : ℝ)*x 1 + (1204327639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374697869/2500000000 : ℝ)^4329 ≤ (45687071578689/100000000000000 : ℝ)^3305 := by
    have hnat : (1374697869 : ℕ)^4329*100000000000000^3305 ≤ 45687071578689^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374697869 2500000000 45687071578689 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1227950341/5000000000 : ℝ)^4329 ≤ (3179125122927/20000000000000 : ℝ)^3305 := by
    have hnat : (1227950341 : ℕ)^4329*20000000000000^3305 ≤ 3179125122927^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227950341 5000000000 3179125122927 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1204327639/2500000000 : ℝ)^4329 ≤ (19208651393367/50000000000000 : ℝ)^3305 := by
    have hnat : (1204327639 : ℕ)^4329*50000000000000^3305 ≤ 19208651393367^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204327639 2500000000 19208651393367 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374697869/2500000000 : ℝ), (-1227950341/5000000000 : ℝ), (1204327639/2500000000 : ℝ)] ![(45687071578689/100000000000000 : ℝ), (3179125122927/20000000000000 : ℝ), (19208651393367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374697869/2500000000 : ℝ)|^4329 ≤ (45687071578689/100000000000000 : ℝ)^3305
        have hw : |(1374697869/2500000000 : ℝ)|=(1374697869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1227950341/5000000000 : ℝ)|^4329 ≤ (3179125122927/20000000000000 : ℝ)^3305
        have hw : |(-1227950341/5000000000 : ℝ)|=(1227950341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1204327639/2500000000 : ℝ)|^4329 ≤ (19208651393367/50000000000000 : ℝ)^3305
        have hw : |(1204327639/2500000000 : ℝ)|=(1204327639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1099758273/2000000000 : ℝ)*x 0 + (4817309929/10000000000 : ℝ)*x 1 + (-1227950799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099758273/2000000000 : ℝ)^4329 ≤ (22843535185347/50000000000000 : ℝ)^3305 := by
    have hnat : (1099758273 : ℕ)^4329*50000000000000^3305 ≤ 22843535185347^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099758273 2000000000 22843535185347 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4817309929/10000000000 : ℝ)^4329 ≤ (9604324059317/25000000000000 : ℝ)^3305 := by
    have hnat : (4817309929 : ℕ)^4329*25000000000000^3305 ≤ 9604324059317^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817309929 10000000000 9604324059317 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1227950799/5000000000 : ℝ)^4329 ≤ (1986954172537/12500000000000 : ℝ)^3305 := by
    have hnat : (1227950799 : ℕ)^4329*12500000000000^3305 ≤ 1986954172537^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227950799 5000000000 1986954172537 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099758273/2000000000 : ℝ), (4817309929/10000000000 : ℝ), (-1227950799/5000000000 : ℝ)] ![(22843535185347/50000000000000 : ℝ), (9604324059317/25000000000000 : ℝ), (1986954172537/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099758273/2000000000 : ℝ)|^4329 ≤ (22843535185347/50000000000000 : ℝ)^3305
        have hw : |(1099758273/2000000000 : ℝ)|=(1099758273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4817309929/10000000000 : ℝ)|^4329 ≤ (9604324059317/25000000000000 : ℝ)^3305
        have hw : |(4817309929/10000000000 : ℝ)|=(4817309929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1227950799/5000000000 : ℝ)|^4329 ≤ (1986954172537/12500000000000 : ℝ)^3305
        have hw : |(-1227950799/5000000000 : ℝ)|=(1227950799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4174732861/10000000000 : ℝ)*x 0 + (621067053/2000000000 : ℝ)*x 1 + (2788363779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4174732861/10000000000 : ℝ)^4329 ≤ (15924166934833/50000000000000 : ℝ)^3305 := by
    have hnat : (4174732861 : ℕ)^4329*50000000000000^3305 ≤ 15924166934833^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4174732861 10000000000 15924166934833 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (621067053/2000000000 : ℝ)^4329 ≤ (21614572451281/100000000000000 : ℝ)^3305 := by
    have hnat : (621067053 : ℕ)^4329*100000000000000^3305 ≤ 21614572451281^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621067053 2000000000 21614572451281 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2788363779/5000000000 : ℝ)^4329 ≤ (46537093657169/100000000000000 : ℝ)^3305 := by
    have hnat : (2788363779 : ℕ)^4329*100000000000000^3305 ≤ 46537093657169^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788363779 5000000000 46537093657169 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4174732861/10000000000 : ℝ), (621067053/2000000000 : ℝ), (2788363779/5000000000 : ℝ)] ![(15924166934833/50000000000000 : ℝ), (21614572451281/100000000000000 : ℝ), (46537093657169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4174732861/10000000000 : ℝ)|^4329 ≤ (15924166934833/50000000000000 : ℝ)^3305
        have hw : |(4174732861/10000000000 : ℝ)|=(4174732861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(621067053/2000000000 : ℝ)|^4329 ≤ (21614572451281/100000000000000 : ℝ)^3305
        have hw : |(621067053/2000000000 : ℝ)|=(621067053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2788363779/5000000000 : ℝ)|^4329 ≤ (46537093657169/100000000000000 : ℝ)^3305
        have hw : |(2788363779/5000000000 : ℝ)|=(2788363779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-898804307/5000000000 : ℝ)*x 0 + (4847321769/10000000000 : ℝ)*x 1 + (5954252623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898804307/5000000000 : ℝ)^4329 ≤ (5281346575879/50000000000000 : ℝ)^3305 := by
    have hnat : (898804307 : ℕ)^4329*50000000000000^3305 ≤ 5281346575879^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898804307 5000000000 5281346575879 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4847321769/10000000000 : ℝ)^4329 ≤ (38731093610129/100000000000000 : ℝ)^3305 := by
    have hnat : (4847321769 : ℕ)^4329*100000000000000^3305 ≤ 38731093610129^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847321769 10000000000 38731093610129 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5954252623/10000000000 : ℝ)^4329 ≤ (12676553302869/25000000000000 : ℝ)^3305 := by
    have hnat : (5954252623 : ℕ)^4329*25000000000000^3305 ≤ 12676553302869^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954252623 10000000000 12676553302869 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898804307/5000000000 : ℝ), (4847321769/10000000000 : ℝ), (5954252623/10000000000 : ℝ)] ![(5281346575879/50000000000000 : ℝ), (38731093610129/100000000000000 : ℝ), (12676553302869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898804307/5000000000 : ℝ)|^4329 ≤ (5281346575879/50000000000000 : ℝ)^3305
        have hw : |(-898804307/5000000000 : ℝ)|=(898804307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4847321769/10000000000 : ℝ)|^4329 ≤ (38731093610129/100000000000000 : ℝ)^3305
        have hw : |(4847321769/10000000000 : ℝ)|=(4847321769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5954252623/10000000000 : ℝ)|^4329 ≤ (12676553302869/25000000000000 : ℝ)^3305
        have hw : |(5954252623/10000000000 : ℝ)|=(5954252623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5180303243/10000000000 : ℝ)*x 0 + (-1318961097/10000000000 : ℝ)*x 1 + (5954251511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180303243/10000000000 : ℝ)^4329 ≤ (5281567545283/12500000000000 : ℝ)^3305 := by
    have hnat : (5180303243 : ℕ)^4329*12500000000000^3305 ≤ 5281567545283^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180303243 10000000000 5281567545283 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318961097/10000000000 : ℝ)^4329 ≤ (3520629408131/50000000000000 : ℝ)^3305 := by
    have hnat : (1318961097 : ℕ)^4329*50000000000000^3305 ≤ 3520629408131^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318961097 10000000000 3520629408131 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5954251511/10000000000 : ℝ)^4329 ≤ (2028248032307/4000000000000 : ℝ)^3305 := by
    have hnat : (5954251511 : ℕ)^4329*4000000000000^3305 ≤ 2028248032307^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5954251511 10000000000 2028248032307 4000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180303243/10000000000 : ℝ), (-1318961097/10000000000 : ℝ), (5954251511/10000000000 : ℝ)] ![(5281567545283/12500000000000 : ℝ), (3520629408131/50000000000000 : ℝ), (2028248032307/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180303243/10000000000 : ℝ)|^4329 ≤ (5281567545283/12500000000000 : ℝ)^3305
        have hw : |(5180303243/10000000000 : ℝ)|=(5180303243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1318961097/10000000000 : ℝ)|^4329 ≤ (3520629408131/50000000000000 : ℝ)^3305
        have hw : |(-1318961097/10000000000 : ℝ)|=(1318961097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5954251511/10000000000 : ℝ)|^4329 ≤ (2028248032307/4000000000000 : ℝ)^3305
        have hw : |(5954251511/10000000000 : ℝ)|=(5954251511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1295075633/2500000000 : ℝ)*x 0 + (2977126691/5000000000 : ℝ)*x 1 + (-1318959199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295075633/2500000000 : ℝ)^4329 ≤ (10563133191573/25000000000000 : ℝ)^3305 := by
    have hnat : (1295075633 : ℕ)^4329*25000000000000^3305 ≤ 10563133191573^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295075633 2500000000 10563133191573 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2977126691/5000000000 : ℝ)^4329 ≤ (50706221677741/100000000000000 : ℝ)^3305 := by
    have hnat : (2977126691 : ℕ)^4329*100000000000000^3305 ≤ 50706221677741^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2977126691 5000000000 50706221677741 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318959199/10000000000 : ℝ)^4329 ≤ (176031138611/2500000000000 : ℝ)^3305 := by
    have hnat : (1318959199 : ℕ)^4329*2500000000000^3305 ≤ 176031138611^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318959199 10000000000 176031138611 2500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295075633/2500000000 : ℝ), (2977126691/5000000000 : ℝ), (-1318959199/10000000000 : ℝ)] ![(10563133191573/25000000000000 : ℝ), (50706221677741/100000000000000 : ℝ), (176031138611/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295075633/2500000000 : ℝ)|^4329 ≤ (10563133191573/25000000000000 : ℝ)^3305
        have hw : |(1295075633/2500000000 : ℝ)|=(1295075633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2977126691/5000000000 : ℝ)|^4329 ≤ (50706221677741/100000000000000 : ℝ)^3305
        have hw : |(2977126691/5000000000 : ℝ)|=(2977126691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1318959199/10000000000 : ℝ)|^4329 ≤ (176031138611/2500000000000 : ℝ)^3305
        have hw : |(-1318959199/10000000000 : ℝ)|=(1318959199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s0_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261491271/625000000 : ℝ)*x 0 + (1102645817/2000000000 : ℝ)*x 1 + (3171106643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261491271/625000000 : ℝ)^4329 ≤ (31939571038343/100000000000000 : ℝ)^3305 := by
    have hnat : (261491271 : ℕ)^4329*100000000000000^3305 ≤ 31939571038343^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261491271 625000000 31939571038343 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102645817/2000000000 : ℝ)^4329 ≤ (9168851523927/20000000000000 : ℝ)^3305 := by
    have hnat : (1102645817 : ℕ)^4329*20000000000000^3305 ≤ 9168851523927^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102645817 2000000000 9168851523927 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171106643/10000000000 : ℝ)^4329 ≤ (22216171322913/100000000000000 : ℝ)^3305 := by
    have hnat : (3171106643 : ℕ)^4329*100000000000000^3305 ≤ 22216171322913^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171106643 10000000000 22216171322913 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261491271/625000000 : ℝ), (1102645817/2000000000 : ℝ), (3171106643/10000000000 : ℝ)] ![(31939571038343/100000000000000 : ℝ), (9168851523927/20000000000000 : ℝ), (22216171322913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261491271/625000000 : ℝ)|^4329 ≤ (31939571038343/100000000000000 : ℝ)^3305
        have hw : |(261491271/625000000 : ℝ)|=(261491271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102645817/2000000000 : ℝ)|^4329 ≤ (9168851523927/20000000000000 : ℝ)^3305
        have hw : |(1102645817/2000000000 : ℝ)|=(1102645817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171106643/10000000000 : ℝ)|^4329 ≤ (22216171322913/100000000000000 : ℝ)^3305
        have hw : |(3171106643/10000000000 : ℝ)|=(3171106643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (323/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13339/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (541/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^541 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^541*1^128 ≤ 0^128*1^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (541/128 : ℝ) ≤ (2080087873199178389/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^541 ≤ (2080087873199178389/100000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^541*100000000000000000000^128 ≤ 2080087873199178389^128*5^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2080087873199178389 100000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2080087873199178389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^541 := by
      have hnat : (1 : ℕ)^128*1^541 ≤ 1^541*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (102080087873199178389/100000000000000000000 : ℝ) ≤ (2009765721701823/2000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (102080087873199178389/100000000000000000000 : ℝ)^128 ≤ (2009765721701823/2000000000000000 : ℝ)^541 := by
      have hnat : (102080087873199178389 : ℕ)^128*2000000000000000^541 ≤ 2009765721701823^541*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102080087873199178389 100000000000000000000 2009765721701823 2000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009765721701823/2000000000000000 : ℝ)) (X := (102080087873199178389/100000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (52080087873199178389/50000000000000000000 : ℝ) ≤ (1009765721701823/1000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (52080087873199178389/50000000000000000000 : ℝ)^128 ≤ (1009765721701823/1000000000000000 : ℝ)^541 := by
      have hnat : (52080087873199178389 : ℕ)^128*1000000000000000^541 ≤ 1009765721701823^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52080087873199178389 50000000000000000000 1009765721701823 1000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009765721701823/1000000000000000 : ℝ)) (X := (52080087873199178389/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(9765721701823/800000000000000 : ℝ)*(0 : ℝ))^(541/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(9765721701823/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2080087873199178389/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(9765721701823/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(541/128 : ℝ) := by
    rw [show (1 : ℝ)+(9765721701823/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2009765721701823/2000000000000000 : ℝ) by norm_num, show 1+(2080087873199178389/100000000000000000000 : ℝ)+(0 : ℝ)=(102080087873199178389/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2080087873199178389/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(9765721701823/800000000000000 : ℝ)*(2/5 : ℝ))^(541/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(9765721701823/800000000000000 : ℝ)*(2/5 : ℝ)=(1009765721701823/1000000000000000 : ℝ) by norm_num, show 1+2*(2080087873199178389/100000000000000000000 : ℝ)=(52080087873199178389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(9765721701823/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9765721701823/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(9765721701823/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9765721701823/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(9765721701823/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (9765721701823/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-896645843/5000000000 : ℝ)*X 0 0+(2992668459/5000000000 : ℝ)*X 0 1+(4817309991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1374697869/2500000000 : ℝ)*X 1 0+(-1227950341/5000000000 : ℝ)*X 1 1+(1204327639/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1099758273/2000000000 : ℝ)*X 2 0+(4817309929/10000000000 : ℝ)*X 2 1+(-1227950799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4174732861/10000000000 : ℝ)*X 0 0+(621067053/2000000000 : ℝ)*X 0 1+(2788363779/5000000000 : ℝ)*X 0 2+(4174732861/10000000000 : ℝ)*X 1 0+(621067053/2000000000 : ℝ)*X 1 1+(2788363779/5000000000 : ℝ)*X 1 2+(4174732861/10000000000 : ℝ)*X 2 0+(621067053/2000000000 : ℝ)*X 2 1+(2788363779/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-898804307/5000000000 : ℝ)*X 0 0+(4847321769/10000000000 : ℝ)*X 0 1+(5954252623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180303243/10000000000 : ℝ)*X 1 0+(-1318961097/10000000000 : ℝ)*X 1 1+(5954251511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1295075633/2500000000 : ℝ)*X 2 0+(2977126691/5000000000 : ℝ)*X 2 1+(-1318959199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261491271/625000000 : ℝ)*X 0 0+(1102645817/2000000000 : ℝ)*X 0 1+(3171106643/10000000000 : ℝ)*X 0 2+(261491271/625000000 : ℝ)*X 1 0+(1102645817/2000000000 : ℝ)*X 1 1+(3171106643/10000000000 : ℝ)*X 1 2+(261491271/625000000 : ℝ)*X 2 0+(1102645817/2000000000 : ℝ)*X 2 1+(3171106643/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18545595431845479478683/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1437731/781250000000 : ℝ)*(base1) + (14111323/100000000000000 : ℝ)*(base16) + (529285531/50000000000000 : ℝ)*(base19) + (42215997/4000000000000 : ℝ)*(base23) + (195137747/100000000000000 : ℝ)*(upper3) + (315196070824393/50000000000000 : ℝ)*(major0) + (315196070824393/50000000000000 : ℝ)*(major1) + (315196070824393/50000000000000 : ℝ)*(major2) + (214037113829191/25000000000000 : ℝ)*(sp0) + (6688671043969/781250000000 : ℝ)*(sp1) + (214037477727623/25000000000000 : ℝ)*(sp2) + (404631297694827/100000000000000 : ℝ)*(sp3) + (2695023221/100000000000000 : ℝ)*(sp4) + (1680716127/100000000000000 : ℝ)*(sp7) + (404633162440523/100000000000000 : ℝ)*(f.failure) + (856150966310417/100000000000000 : ℝ)*(f.sum) + (8442562548439/20000000000000000000000000000 : ℝ)*base65 + (131509770928439/40000000000000000000000000000 : ℝ)*base67 + (77885663608439/40000000000000000000000000000 : ℝ)*base69 + (44698382928439/40000000000000000000000000000 : ℝ)*base71 + (48986338448439/20000000000000000000000000000 : ℝ)*base73 + (129127344208439/40000000000000000000000000000 : ℝ)*base75 + (100151470991561/40000000000000000000000000000 : ℝ)*base78 + (112526420248439/40000000000000000000000000000 : ℝ)*base79 + (34164382748439/20000000000000000000000000000 : ℝ)*base81 + (22678681/5000000000000000000000 : ℝ)*base89 + (22678681/5000000000000000000000 : ℝ)*base91 + (22678681/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (120007976408189096138091/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (468999233/100000000000000 : ℝ)*(base19) + (911831679/100000000000000 : ℝ)*(base23) + (316313727/100000000000000 : ℝ)*(base39) + (19626973/20000000000000 : ℝ)*(upper2) + (37267807/20000000000000 : ℝ)*(upper5) + (665179969200761/100000000000000 : ℝ)*(major0) + (665179969200761/100000000000000 : ℝ)*(major1) + (133035930577407/20000000000000 : ℝ)*(major2) + (392665811/50000000000000 : ℝ)*(sp1) + (1899919579/100000000000000 : ℝ)*(sp2) + (45169840571369/5000000000000 : ℝ)*(sp4) + (36135822283861/4000000000000 : ℝ)*(sp5) + (903394315989849/100000000000000 : ℝ)*(sp6) + (213481305323559/50000000000000 : ℝ)*(sp7) + (213481305323559/50000000000000 : ℝ)*(f.failure) + (903397127741107/100000000000000 : ℝ)*(f.sum) + (31184153253027/20000000000000000000000000000 : ℝ)*base65 + (57079521487039/16000000000000000000000000000 : ℝ)*base68 + (53828257567303/80000000000000000000000000000 : ℝ)*base69 + (35249666207039/16000000000000000000000000000 : ℝ)*base72 + (22289901793027/20000000000000000000000000000 : ℝ)*base73 + (82925588207303/80000000000000000000000000000 : ℝ)*base75 + (281845505392697/80000000000000000000000000000 : ℝ)*base78 + (488213632432697/80000000000000000000000000000 : ℝ)*base80 + (60364199447303/40000000000000000000000000000 : ℝ)*base81 + (3562573/2500000000000000000000 : ℝ)*base89 + (3562573/2500000000000000000000 : ℝ)*base91 + (21437427/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1369_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (323/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13339/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1369_s1_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1974219091/10000000000 : ℝ)*x 0 + (2815113847/5000000000 : ℝ)*x 1 + (2528260701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974219091/10000000000 : ℝ)^4329 ≤ (11942222581639/100000000000000 : ℝ)^3305 := by
    have hnat : (1974219091 : ℕ)^4329*100000000000000^3305 ≤ 11942222581639^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974219091 10000000000 11942222581639 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2815113847/5000000000 : ℝ)^4329 ≤ (11780684645699/25000000000000 : ℝ)^3305 := by
    have hnat : (2815113847 : ℕ)^4329*25000000000000^3305 ≤ 11780684645699^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2815113847 5000000000 11780684645699 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2528260701/5000000000 : ℝ)^4329 ≤ (40935038815459/100000000000000 : ℝ)^3305 := by
    have hnat : (2528260701 : ℕ)^4329*100000000000000^3305 ≤ 40935038815459^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528260701 5000000000 40935038815459 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1974219091/10000000000 : ℝ), (2815113847/5000000000 : ℝ), (2528260701/5000000000 : ℝ)] ![(11942222581639/100000000000000 : ℝ), (11780684645699/25000000000000 : ℝ), (40935038815459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1974219091/10000000000 : ℝ)|^4329 ≤ (11942222581639/100000000000000 : ℝ)^3305
        have hw : |(-1974219091/10000000000 : ℝ)|=(1974219091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2815113847/5000000000 : ℝ)|^4329 ≤ (11780684645699/25000000000000 : ℝ)^3305
        have hw : |(2815113847/5000000000 : ℝ)|=(2815113847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2528260701/5000000000 : ℝ)|^4329 ≤ (40935038815459/100000000000000 : ℝ)^3305
        have hw : |(2528260701/5000000000 : ℝ)|=(2528260701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675364451/1250000000 : ℝ)*x 0 + (-455933497/2000000000 : ℝ)*x 1 + (40452181/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675364451/1250000000 : ℝ)^4329 ≤ (22323249845341/50000000000000 : ℝ)^3305 := by
    have hnat : (675364451 : ℕ)^4329*50000000000000^3305 ≤ 22323249845341^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675364451 1250000000 22323249845341 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455933497/2000000000 : ℝ)^4329 ≤ (7209224256451/50000000000000 : ℝ)^3305 := by
    have hnat : (455933497 : ℕ)^4329*50000000000000^3305 ≤ 7209224256451^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455933497 2000000000 7209224256451 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40452181/80000000 : ℝ)^4329 ≤ (20467525891923/50000000000000 : ℝ)^3305 := by
    have hnat : (40452181 : ℕ)^4329*50000000000000^3305 ≤ 20467525891923^3305*80000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40452181 80000000 20467525891923 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675364451/1250000000 : ℝ), (-455933497/2000000000 : ℝ), (40452181/80000000 : ℝ)] ![(22323249845341/50000000000000 : ℝ), (7209224256451/50000000000000 : ℝ), (20467525891923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675364451/1250000000 : ℝ)|^4329 ≤ (22323249845341/50000000000000 : ℝ)^3305
        have hw : |(675364451/1250000000 : ℝ)|=(675364451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455933497/2000000000 : ℝ)|^4329 ≤ (7209224256451/50000000000000 : ℝ)^3305
        have hw : |(-455933497/2000000000 : ℝ)|=(455933497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40452181/80000000 : ℝ)|^4329 ≤ (20467525891923/50000000000000 : ℝ)^3305
        have hw : |(40452181/80000000 : ℝ)|=(40452181/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402916007/10000000000 : ℝ)*x 0 + (5056521599/10000000000 : ℝ)*x 1 + (-569917069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402916007/10000000000 : ℝ)^4329 ≤ (8929300801867/20000000000000 : ℝ)^3305 := by
    have hnat : (5402916007 : ℕ)^4329*20000000000000^3305 ≤ 8929300801867^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402916007 10000000000 8929300801867 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5056521599/10000000000 : ℝ)^4329 ≤ (20467520452199/50000000000000 : ℝ)^3305 := by
    have hnat : (5056521599 : ℕ)^4329*50000000000000^3305 ≤ 20467520452199^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056521599 10000000000 20467520452199 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (569917069/2500000000 : ℝ)^4329 ≤ (7209227532947/50000000000000 : ℝ)^3305 := by
    have hnat : (569917069 : ℕ)^4329*50000000000000^3305 ≤ 7209227532947^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569917069 2500000000 7209227532947 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402916007/10000000000 : ℝ), (5056521599/10000000000 : ℝ), (-569917069/2500000000 : ℝ)] ![(8929300801867/20000000000000 : ℝ), (20467520452199/50000000000000 : ℝ), (7209227532947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402916007/10000000000 : ℝ)|^4329 ≤ (8929300801867/20000000000000 : ℝ)^3305
        have hw : |(5402916007/10000000000 : ℝ)|=(5402916007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5056521599/10000000000 : ℝ)|^4329 ≤ (20467520452199/50000000000000 : ℝ)^3305
        have hw : |(5056521599/10000000000 : ℝ)|=(5056521599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-569917069/2500000000 : ℝ)|^4329 ≤ (7209227532947/50000000000000 : ℝ)^3305
        have hw : |(-569917069/2500000000 : ℝ)|=(569917069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857495949/2000000000 : ℝ)*x 0 + (3719887243/10000000000 : ℝ)*x 1 + (197350809/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857495949/2000000000 : ℝ)^4329 ≤ (263837133873/800000000000 : ℝ)^3305 := by
    have hnat : (857495949 : ℕ)^4329*800000000000^3305 ≤ 263837133873^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857495949 2000000000 263837133873 800000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3719887243/10000000000 : ℝ)^4329 ≤ (8762246259/32000000000 : ℝ)^3305 := by
    have hnat : (3719887243 : ℕ)^4329*32000000000^3305 ≤ 8762246259^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3719887243 10000000000 8762246259 32000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197350809/400000000 : ℝ)^4329 ≤ (39638338701671/100000000000000 : ℝ)^3305 := by
    have hnat : (197350809 : ℕ)^4329*100000000000000^3305 ≤ 39638338701671^3305*400000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197350809 400000000 39638338701671 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857495949/2000000000 : ℝ), (3719887243/10000000000 : ℝ), (197350809/400000000 : ℝ)] ![(263837133873/800000000000 : ℝ), (8762246259/32000000000 : ℝ), (39638338701671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857495949/2000000000 : ℝ)|^4329 ≤ (263837133873/800000000000 : ℝ)^3305
        have hw : |(857495949/2000000000 : ℝ)|=(857495949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3719887243/10000000000 : ℝ)|^4329 ≤ (8762246259/32000000000 : ℝ)^3305
        have hw : |(3719887243/10000000000 : ℝ)|=(3719887243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197350809/400000000 : ℝ)|^4329 ≤ (39638338701671/100000000000000 : ℝ)^3305
        have hw : |(197350809/400000000 : ℝ)|=(197350809/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1974708303/10000000000 : ℝ)*x 0 + (1265892999/2500000000 : ℝ)*x 1 + (5623051527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974708303/10000000000 : ℝ)^4329 ≤ (1493262362801/12500000000000 : ℝ)^3305 := by
    have hnat : (1974708303 : ℕ)^4329*12500000000000^3305 ≤ 1493262362801^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974708303 10000000000 1493262362801 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265892999/2500000000 : ℝ)^4329 ≤ (20504908847819/50000000000000 : ℝ)^3305 := by
    have hnat : (1265892999 : ℕ)^4329*50000000000000^3305 ≤ 20504908847819^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265892999 2500000000 20504908847819 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5623051527/10000000000 : ℝ)^4329 ≤ (23522041691781/50000000000000 : ℝ)^3305 := by
    have hnat : (5623051527 : ℕ)^4329*50000000000000^3305 ≤ 23522041691781^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5623051527 10000000000 23522041691781 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1974708303/10000000000 : ℝ), (1265892999/2500000000 : ℝ), (5623051527/10000000000 : ℝ)] ![(1493262362801/12500000000000 : ℝ), (20504908847819/50000000000000 : ℝ), (23522041691781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1974708303/10000000000 : ℝ)|^4329 ≤ (1493262362801/12500000000000 : ℝ)^3305
        have hw : |(-1974708303/10000000000 : ℝ)|=(1974708303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1265892999/2500000000 : ℝ)|^4329 ≤ (20504908847819/50000000000000 : ℝ)^3305
        have hw : |(1265892999/2500000000 : ℝ)|=(1265892999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5623051527/10000000000 : ℝ)|^4329 ≤ (23522041691781/50000000000000 : ℝ)^3305
        have hw : |(5623051527/10000000000 : ℝ)|=(5623051527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262685819/500000000 : ℝ)*x 0 + (-1713138387/10000000000 : ℝ)*x 1 + (1405762903/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262685819/500000000 : ℝ)^4329 ≤ (43038566296933/100000000000000 : ℝ)^3305 := by
    have hnat : (262685819 : ℕ)^4329*100000000000000^3305 ≤ 43038566296933^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262685819 500000000 43038566296933 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713138387/10000000000 : ℝ)^4329 ≤ (9917349375121/100000000000000 : ℝ)^3305 := by
    have hnat : (1713138387 : ℕ)^4329*100000000000000^3305 ≤ 9917349375121^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713138387 10000000000 9917349375121 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405762903/2500000000 : ℝ)^4329 ≤ (4704408431503/10000000000000 : ℝ)^3305 := by
    have hnat : (1405762903 : ℕ)^4329*10000000000000^3305 ≤ 4704408431503^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405762903 2500000000 4704408431503 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262685819/500000000 : ℝ), (-1713138387/10000000000 : ℝ), (1405762903/2500000000 : ℝ)] ![(43038566296933/100000000000000 : ℝ), (9917349375121/100000000000000 : ℝ), (4704408431503/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262685819/500000000 : ℝ)|^4329 ≤ (43038566296933/100000000000000 : ℝ)^3305
        have hw : |(262685819/500000000 : ℝ)|=(262685819/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1713138387/10000000000 : ℝ)|^4329 ≤ (9917349375121/100000000000000 : ℝ)^3305
        have hw : |(-1713138387/10000000000 : ℝ)|=(1713138387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1405762903/2500000000 : ℝ)|^4329 ≤ (4704408431503/10000000000000 : ℝ)^3305
        have hw : |(1405762903/2500000000 : ℝ)|=(1405762903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253716273/10000000000 : ℝ)*x 0 + (5623051711/10000000000 : ℝ)*x 1 + (-428284599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253716273/10000000000 : ℝ)^4329 ≤ (43038565148803/100000000000000 : ℝ)^3305 := by
    have hnat : (5253716273 : ℕ)^4329*100000000000000^3305 ≤ 43038565148803^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253716273 10000000000 43038565148803 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5623051711/10000000000 : ℝ)^4329 ≤ (11761021349979/25000000000000 : ℝ)^3305 := by
    have hnat : (5623051711 : ℕ)^4329*25000000000000^3305 ≤ 11761021349979^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5623051711 10000000000 11761021349979 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428284599/2500000000 : ℝ)^4329 ≤ (2479337360841/25000000000000 : ℝ)^3305 := by
    have hnat : (428284599 : ℕ)^4329*25000000000000^3305 ≤ 2479337360841^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428284599 2500000000 2479337360841 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253716273/10000000000 : ℝ), (5623051711/10000000000 : ℝ), (-428284599/2500000000 : ℝ)] ![(43038565148803/100000000000000 : ℝ), (11761021349979/25000000000000 : ℝ), (2479337360841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253716273/10000000000 : ℝ)|^4329 ≤ (43038565148803/100000000000000 : ℝ)^3305
        have hw : |(5253716273/10000000000 : ℝ)|=(5253716273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5623051711/10000000000 : ℝ)|^4329 ≤ (11761021349979/25000000000000 : ℝ)^3305
        have hw : |(5623051711/10000000000 : ℝ)|=(5623051711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428284599/2500000000 : ℝ)|^4329 ≤ (2479337360841/25000000000000 : ℝ)^3305
        have hw : |(-428284599/2500000000 : ℝ)|=(428284599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s1_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8376007/19531250 : ℝ)*x 0 + (4918853911/10000000000 : ℝ)*x 1 + (74701357/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8376007/19531250 : ℝ)^4329 ≤ (32990078561153/100000000000000 : ℝ)^3305 := by
    have hnat : (8376007 : ℕ)^4329*100000000000000^3305 ≤ 32990078561153^3305*19531250^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8376007 19531250 32990078561153 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4918853911/10000000000 : ℝ)^4329 ≤ (19740721586399/50000000000000 : ℝ)^3305 := by
    have hnat : (4918853911 : ℕ)^4329*50000000000000^3305 ≤ 19740721586399^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918853911 10000000000 19740721586399 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74701357/200000000 : ℝ)^4329 ≤ (5505695652151/20000000000000 : ℝ)^3305 := by
    have hnat : (74701357 : ℕ)^4329*20000000000000^3305 ≤ 5505695652151^3305*200000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74701357 200000000 5505695652151 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8376007/19531250 : ℝ), (4918853911/10000000000 : ℝ), (74701357/200000000 : ℝ)] ![(32990078561153/100000000000000 : ℝ), (19740721586399/50000000000000 : ℝ), (5505695652151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8376007/19531250 : ℝ)|^4329 ≤ (32990078561153/100000000000000 : ℝ)^3305
        have hw : |(8376007/19531250 : ℝ)|=(8376007/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4918853911/10000000000 : ℝ)|^4329 ≤ (19740721586399/50000000000000 : ℝ)^3305
        have hw : |(4918853911/10000000000 : ℝ)|=(4918853911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74701357/200000000 : ℝ)|^4329 ≤ (5505695652151/20000000000000 : ℝ)^3305
        have hw : |(74701357/200000000 : ℝ)|=(74701357/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (323/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (223/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9631/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (323/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (323/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (323/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (323/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (323/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (323/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (323/20000 : ℝ) ^ (541/128 : ℝ) ≤ (534268033863/20000000000000000000 : ℝ) := by
    have hpowers : (323/20000 : ℝ)^541 ≤ (534268033863/20000000000000000000 : ℝ)^128 := by
      have hnat : (323 : ℕ)^541*20000000000000000000^128 ≤ 534268033863^128*20000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        323 20000 534268033863 20000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (323/20000 : ℝ)) (X := (534268033863/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (13339/50000 : ℝ) ^ (541/128 : ℝ) ≤ (75098440474569631/20000000000000000000 : ℝ) := by
    have hpowers : (13339/50000 : ℝ)^541 ≤ (75098440474569631/20000000000000000000 : ℝ)^128 := by
      have hnat : (13339 : ℕ)^541*20000000000000000000^128 ≤ 75098440474569631^128*50000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13339 50000 75098440474569631 20000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13339/50000 : ℝ)) (X := (75098440474569631/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000534268033863/10000000000000000000 : ℝ) ≤ (5000000063203611/5000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (10000000534268033863/10000000000000000000 : ℝ)^128 ≤ (5000000063203611/5000000000000000 : ℝ)^541 := by
      have hnat : (10000000534268033863 : ℕ)^128*5000000000000000^541 ≤ 5000000063203611^541*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000534268033863 10000000000000000000 5000000063203611 5000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000063203611/5000000000000000 : ℝ)) (X := (10000000534268033863/10000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (10037549487371301747/10000000000000000000 : ℝ) ≤ (2502217865431171/2500000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (10037549487371301747/10000000000000000000 : ℝ)^128 ≤ (2502217865431171/2500000000000000 : ℝ)^541 := by
      have hnat : (10037549487371301747 : ℕ)^128*2500000000000000^541 ≤ 2502217865431171^541*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10037549487371301747 10000000000000000000 2502217865431171 2500000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502217865431171/2500000000000000 : ℝ)) (X := (10037549487371301747/10000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (10075098440474569631/10000000000000000000 : ℝ) ≤ (5008871398521073/5000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (10075098440474569631/10000000000000000000 : ℝ)^128 ≤ (5008871398521073/5000000000000000 : ℝ)^541 := by
      have hnat : (10075098440474569631 : ℕ)^128*5000000000000000^541 ≤ 5008871398521073^541*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10075098440474569631 10000000000000000000 5008871398521073 5000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008871398521073/5000000000000000 : ℝ)) (X := (10075098440474569631/10000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(534268033863/20000000000000000000 : ℝ) ≤ ((125300674377534401363/125315000000000000000 : ℝ)+2*(4435667658731/1253150000000000 : ℝ)*(323/20000 : ℝ))^(541/128 : ℝ) := by
    rw [show (125300674377534401363/125315000000000000000 : ℝ)+2*(4435667658731/1253150000000000 : ℝ)*(323/20000 : ℝ)=(5000000063203611/5000000000000000 : ℝ) by norm_num, show 1+2*(534268033863/20000000000000000000 : ℝ)=(10000000534268033863/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(75098440474569631/20000000000000000000 : ℝ)+(534268033863/20000000000000000000 : ℝ) ≤ ((125300674377534401363/125315000000000000000 : ℝ)+(4435667658731/1253150000000000 : ℝ)*((13339/50000 : ℝ)+(323/20000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (125300674377534401363/125315000000000000000 : ℝ)+(4435667658731/1253150000000000 : ℝ)*((13339/50000 : ℝ)+(323/20000 : ℝ))=(2502217865431171/2500000000000000 : ℝ) by norm_num, show 1+(75098440474569631/20000000000000000000 : ℝ)+(534268033863/20000000000000000000 : ℝ)=(10037549487371301747/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(75098440474569631/20000000000000000000 : ℝ) ≤ ((125300674377534401363/125315000000000000000 : ℝ)+2*(4435667658731/1253150000000000 : ℝ)*(13339/50000 : ℝ))^(541/128 : ℝ) := by
    rw [show (125300674377534401363/125315000000000000000 : ℝ)+2*(4435667658731/1253150000000000 : ℝ)*(13339/50000 : ℝ)=(5008871398521073/5000000000000000 : ℝ) by norm_num, show 1+2*(75098440474569631/20000000000000000000 : ℝ)=(10075098440474569631/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125300674377534401363/125315000000000000000 : ℝ)*(X 1 0+X 2 0)+(4435667658731/1253150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (323/20000 : ℝ)) (hi := (13339/50000 : ℝ)) (c := (125300674377534401363/125315000000000000000 : ℝ)) (alpha := (4435667658731/1253150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125300674377534401363/125315000000000000000 : ℝ)*(X 0 1+X 2 1)+(4435667658731/1253150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (323/20000 : ℝ)) (hi := (13339/50000 : ℝ)) (c := (125300674377534401363/125315000000000000000 : ℝ)) (alpha := (4435667658731/1253150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125300674377534401363/125315000000000000000 : ℝ)*(X 0 2+X 1 2)+(4435667658731/1253150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (323/20000 : ℝ)) (hi := (13339/50000 : ℝ)) (c := (125300674377534401363/125315000000000000000 : ℝ)) (alpha := (4435667658731/1253150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1974219091/10000000000 : ℝ)*X 0 0+(2815113847/5000000000 : ℝ)*X 0 1+(2528260701/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675364451/1250000000 : ℝ)*X 1 0+(-455933497/2000000000 : ℝ)*X 1 1+(40452181/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5402916007/10000000000 : ℝ)*X 2 0+(5056521599/10000000000 : ℝ)*X 2 1+(-569917069/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((857495949/2000000000 : ℝ)*X 0 0+(3719887243/10000000000 : ℝ)*X 0 1+(197350809/400000000 : ℝ)*X 0 2+(857495949/2000000000 : ℝ)*X 1 0+(3719887243/10000000000 : ℝ)*X 1 1+(197350809/400000000 : ℝ)*X 1 2+(857495949/2000000000 : ℝ)*X 2 0+(3719887243/10000000000 : ℝ)*X 2 1+(197350809/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1974708303/10000000000 : ℝ)*X 0 0+(1265892999/2500000000 : ℝ)*X 0 1+(5623051527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262685819/500000000 : ℝ)*X 1 0+(-1713138387/10000000000 : ℝ)*X 1 1+(1405762903/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253716273/10000000000 : ℝ)*X 2 0+(5623051711/10000000000 : ℝ)*X 2 1+(-428284599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8376007/19531250 : ℝ)*X 0 0+(4918853911/10000000000 : ℝ)*X 0 1+(74701357/200000000 : ℝ)*X 0 2+(8376007/19531250 : ℝ)*X 1 0+(4918853911/10000000000 : ℝ)*X 1 1+(74701357/200000000 : ℝ)*X 1 2+(8376007/19531250 : ℝ)*X 2 0+(4918853911/10000000000 : ℝ)*X 2 1+(74701357/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54398954357625453264897529269/6265750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1161489/10000000000000 : ℝ)*(base16) + (1383490203/100000000000000 : ℝ)*(base19) + (61250097/4000000000000 : ℝ)*(base23) + (4010549/100000000000000 : ℝ)*(upper2) + (267608287/100000000000000 : ℝ)*(upper3) + (1283444123429793/100000000000000 : ℝ)*(major0) + (1283444123429793/100000000000000 : ℝ)*(major1) + (1283444123429793/100000000000000 : ℝ)*(major2) + (43576645813057/2500000000000 : ℝ)*(sp0) + (217884430645827/12500000000000 : ℝ)*(sp1) + (348615061803857/20000000000000 : ℝ)*(sp2) + (32952244170019/4000000000000 : ℝ)*(sp3) + (1100774943/10000000000000 : ℝ)*(sp4) + (5012938919/100000000000000 : ℝ)*(sp7) + (164762223437879/20000000000000 : ℝ)*(f.failure) + (174307684027171/10000000000000 : ℝ)*(f.sum) + (98611724813051/125315000000000000000000000000 : ℝ)*base65 + (79250935882011307859/12531500000000000000000000000000000 : ℝ)*base67 + (187174219410739807859/12531500000000000000000000000000000 : ℝ)*base69 + (112446279561763807859/12531500000000000000000000000000000 : ℝ)*base71 + (27025093847191/7832187500000000000000000000 : ℝ)*base73 + (149053761954594807859/12531500000000000000000000000000000 : ℝ)*base75 + (129348109271553307859/12531500000000000000000000000000000 : ℝ)*base77 + (20991339302888807859/12531500000000000000000000000000000 : ℝ)*base79 + (842521594935391/125315000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (679613/1000000000000000000000 : ℝ)*base89 + (679613/1000000000000000000000 : ℝ)*base91 + (679613/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7963412727159939377966352141/3132875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25107333/100000000000000 : ℝ)*(base1) + (52106801/10000000000000 : ℝ)*(base19) + (948103/195312500000 : ℝ)*(base23) + (65193657/100000000000000 : ℝ)*(upper3) + (53378181/100000000000000 : ℝ)*(upper5) + (1316061303480069/100000000000000 : ℝ)*(major0) + (1316061303480069/100000000000000 : ℝ)*(major1) + (1316061303480069/100000000000000 : ℝ)*(major2) + (1446967689/50000000000000 : ℝ)*(sp1) + (292080543/10000000000000 : ℝ)*(sp2) + (178737526701819/10000000000000 : ℝ)*(sp4) + (178737182690747/10000000000000 : ℝ)*(sp5) + (446842958919173/25000000000000 : ℝ)*(sp6) + (84474725521239/10000000000000 : ℝ)*(sp7) + (422373640159861/50000000000000 : ℝ)*(f.failure) + (893687620955429/50000000000000 : ℝ)*(f.sum) + (105968180788743/31328750000000000000000000000 : ℝ)*base66 + (60556066755934165953/12531500000000000000000000000000000 : ℝ)*base68 + (106038031341415834047/12531500000000000000000000000000000 : ℝ)*base69 + (74574550210035165953/12531500000000000000000000000000000 : ℝ)*base72 + (122117145134293/31328750000000000000000000000 : ℝ)*base74 + (47936418430524165953/12531500000000000000000000000000000 : ℝ)*base76 + (169610795822848165953/12531500000000000000000000000000000 : ℝ)*base78 + (32464144834207165953/12531500000000000000000000000000000 : ℝ)*base80 + (285325927138329/62657500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (6872167/2500000000000000000000 : ℝ)*base89 + (6872167/2500000000000000000000 : ℝ)*base91 + (6872167/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1369_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (323/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9631/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1369_s2_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2012078591/10000000000 : ℝ)*x 0 + (547257931/1000000000 : ℝ)*x 1 + (5189881441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012078591/10000000000 : ℝ)^4329 ≤ (6121540955603/50000000000000 : ℝ)^3305 := by
    have hnat : (2012078591 : ℕ)^4329*50000000000000^3305 ≤ 6121540955603^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012078591 10000000000 6121540955603 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547257931/1000000000 : ℝ)^4329 ≤ (9080403938757/20000000000000 : ℝ)^3305 := by
    have hnat : (547257931 : ℕ)^4329*20000000000000^3305 ≤ 9080403938757^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547257931 1000000000 9080403938757 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5189881441/10000000000 : ℝ)^4329 ≤ (42354898388183/100000000000000 : ℝ)^3305 := by
    have hnat : (5189881441 : ℕ)^4329*100000000000000^3305 ≤ 42354898388183^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189881441 10000000000 42354898388183 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2012078591/10000000000 : ℝ), (547257931/1000000000 : ℝ), (5189881441/10000000000 : ℝ)] ![(6121540955603/50000000000000 : ℝ), (9080403938757/20000000000000 : ℝ), (42354898388183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2012078591/10000000000 : ℝ)|^4329 ≤ (6121540955603/50000000000000 : ℝ)^3305
        have hw : |(-2012078591/10000000000 : ℝ)|=(2012078591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547257931/1000000000 : ℝ)|^4329 ≤ (9080403938757/20000000000000 : ℝ)^3305
        have hw : |(547257931/1000000000 : ℝ)|=(547257931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5189881441/10000000000 : ℝ)|^4329 ≤ (42354898388183/100000000000000 : ℝ)^3305
        have hw : |(5189881441/10000000000 : ℝ)|=(5189881441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364081369/10000000000 : ℝ)*x 0 + (-2157941123/10000000000 : ℝ)*x 1 + (5189881669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364081369/10000000000 : ℝ)^4329 ≤ (44226638726199/100000000000000 : ℝ)^3305 := by
    have hnat : (5364081369 : ℕ)^4329*100000000000000^3305 ≤ 44226638726199^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364081369 10000000000 44226638726199 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157941123/10000000000 : ℝ)^4329 ≤ (3354615109283/25000000000000 : ℝ)^3305 := by
    have hnat : (2157941123 : ℕ)^4329*25000000000000^3305 ≤ 3354615109283^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157941123 10000000000 3354615109283 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5189881669/10000000000 : ℝ)^4329 ≤ (5294362603177/12500000000000 : ℝ)^3305 := by
    have hnat : (5189881669 : ℕ)^4329*12500000000000^3305 ≤ 5294362603177^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189881669 10000000000 5294362603177 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364081369/10000000000 : ℝ), (-2157941123/10000000000 : ℝ), (5189881669/10000000000 : ℝ)] ![(44226638726199/100000000000000 : ℝ), (3354615109283/25000000000000 : ℝ), (5294362603177/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364081369/10000000000 : ℝ)|^4329 ≤ (44226638726199/100000000000000 : ℝ)^3305
        have hw : |(5364081369/10000000000 : ℝ)|=(5364081369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157941123/10000000000 : ℝ)|^4329 ≤ (3354615109283/25000000000000 : ℝ)^3305
        have hw : |(-2157941123/10000000000 : ℝ)|=(2157941123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5189881669/10000000000 : ℝ)|^4329 ≤ (5294362603177/12500000000000 : ℝ)^3305
        have hw : |(5189881669/10000000000 : ℝ)|=(5189881669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536408137/1000000000 : ℝ)*x 0 + (5189881653/10000000000 : ℝ)*x 1 + (-1078970571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536408137/1000000000 : ℝ)^4329 ≤ (22113319368499/50000000000000 : ℝ)^3305 := by
    have hnat : (536408137 : ℕ)^4329*50000000000000^3305 ≤ 22113319368499^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536408137 1000000000 22113319368499 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5189881653/10000000000 : ℝ)^4329 ≤ (21177450327191/50000000000000 : ℝ)^3305 := by
    have hnat : (5189881653 : ℕ)^4329*50000000000000^3305 ≤ 21177450327191^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5189881653 10000000000 21177450327191 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078970571/5000000000 : ℝ)^4329 ≤ (13418460591883/100000000000000 : ℝ)^3305 := by
    have hnat : (1078970571 : ℕ)^4329*100000000000000^3305 ≤ 13418460591883^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078970571 5000000000 13418460591883 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536408137/1000000000 : ℝ), (5189881653/10000000000 : ℝ), (-1078970571/5000000000 : ℝ)] ![(22113319368499/50000000000000 : ℝ), (21177450327191/50000000000000 : ℝ), (13418460591883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536408137/1000000000 : ℝ)|^4329 ≤ (22113319368499/50000000000000 : ℝ)^3305
        have hw : |(536408137/1000000000 : ℝ)|=(536408137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5189881653/10000000000 : ℝ)|^4329 ≤ (21177450327191/50000000000000 : ℝ)^3305
        have hw : |(5189881653/10000000000 : ℝ)|=(5189881653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1078970571/5000000000 : ℝ)|^4329 ≤ (13418460591883/100000000000000 : ℝ)^3305
        have hw : |(-1078970571/5000000000 : ℝ)|=(1078970571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314034337/10000000000 : ℝ)*x 0 + (2012254653/5000000000 : ℝ)*x 1 + (2311330303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314034337/10000000000 : ℝ)^4329 ≤ (33247444780367/100000000000000 : ℝ)^3305 := by
    have hnat : (4314034337 : ℕ)^4329*100000000000000^3305 ≤ 33247444780367^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314034337 10000000000 33247444780367 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2012254653/5000000000 : ℝ)^4329 ≤ (7588915834779/25000000000000 : ℝ)^3305 := by
    have hnat : (2012254653 : ℕ)^4329*25000000000000^3305 ≤ 7588915834779^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012254653 5000000000 7588915834779 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2311330303/5000000000 : ℝ)^4329 ≤ (18198445935449/50000000000000 : ℝ)^3305 := by
    have hnat : (2311330303 : ℕ)^4329*50000000000000^3305 ≤ 18198445935449^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311330303 5000000000 18198445935449 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314034337/10000000000 : ℝ), (2012254653/5000000000 : ℝ), (2311330303/5000000000 : ℝ)] ![(33247444780367/100000000000000 : ℝ), (7588915834779/25000000000000 : ℝ), (18198445935449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314034337/10000000000 : ℝ)|^4329 ≤ (33247444780367/100000000000000 : ℝ)^3305
        have hw : |(4314034337/10000000000 : ℝ)|=(4314034337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2012254653/5000000000 : ℝ)|^4329 ≤ (7588915834779/25000000000000 : ℝ)^3305
        have hw : |(2012254653/5000000000 : ℝ)|=(2012254653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2311330303/5000000000 : ℝ)|^4329 ≤ (18198445935449/50000000000000 : ℝ)^3305
        have hw : |(2311330303/5000000000 : ℝ)|=(2311330303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201213719/1000000000 : ℝ)*x 0 + (2595801531/5000000000 : ℝ)*x 1 + (2735421299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201213719/1000000000 : ℝ)^4329 ≤ (12243548951231/100000000000000 : ℝ)^3305 := by
    have hnat : (201213719 : ℕ)^4329*100000000000000^3305 ≤ 12243548951231^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201213719 1000000000 12243548951231 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2595801531/5000000000 : ℝ)^4329 ≤ (42373302810783/100000000000000 : ℝ)^3305 := by
    have hnat : (2595801531 : ℕ)^4329*100000000000000^3305 ≤ 42373302810783^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595801531 5000000000 42373302810783 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735421299/5000000000 : ℝ)^4329 ≤ (11345787056473/25000000000000 : ℝ)^3305 := by
    have hnat : (2735421299 : ℕ)^4329*25000000000000^3305 ≤ 11345787056473^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735421299 5000000000 11345787056473 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201213719/1000000000 : ℝ), (2595801531/5000000000 : ℝ), (2735421299/5000000000 : ℝ)] ![(12243548951231/100000000000000 : ℝ), (42373302810783/100000000000000 : ℝ), (11345787056473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201213719/1000000000 : ℝ)|^4329 ≤ (12243548951231/100000000000000 : ℝ)^3305
        have hw : |(-201213719/1000000000 : ℝ)|=(201213719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2595801531/5000000000 : ℝ)|^4329 ≤ (42373302810783/100000000000000 : ℝ)^3305
        have hw : |(2595801531/5000000000 : ℝ)|=(2595801531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735421299/5000000000 : ℝ)|^4329 ≤ (11345787056473/25000000000000 : ℝ)^3305
        have hw : |(2735421299/5000000000 : ℝ)|=(2735421299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330687919/625000000 : ℝ)*x 0 + (-375395987/2000000000 : ℝ)*x 1 + (2735421267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330687919/625000000 : ℝ)^4329 ≤ (271494610699/625000000000 : ℝ)^3305 := by
    have hnat : (330687919 : ℕ)^4329*625000000000^3305 ≤ 271494610699^3305*625000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330687919 625000000 271494610699 625000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375395987/2000000000 : ℝ)^4329 ≤ (698607171493/6250000000000 : ℝ)^3305 := by
    have hnat : (375395987 : ℕ)^4329*6250000000000^3305 ≤ 698607171493^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375395987 2000000000 698607171493 6250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735421267/5000000000 : ℝ)^4329 ≤ (45383147530489/100000000000000 : ℝ)^3305 := by
    have hnat : (2735421267 : ℕ)^4329*100000000000000^3305 ≤ 45383147530489^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735421267 5000000000 45383147530489 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330687919/625000000 : ℝ), (-375395987/2000000000 : ℝ), (2735421267/5000000000 : ℝ)] ![(271494610699/625000000000 : ℝ), (698607171493/6250000000000 : ℝ), (45383147530489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330687919/625000000 : ℝ)|^4329 ≤ (271494610699/625000000000 : ℝ)^3305
        have hw : |(330687919/625000000 : ℝ)|=(330687919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375395987/2000000000 : ℝ)|^4329 ≤ (698607171493/6250000000000 : ℝ)^3305
        have hw : |(-375395987/2000000000 : ℝ)|=(375395987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735421267/5000000000 : ℝ)|^4329 ≤ (45383147530489/100000000000000 : ℝ)^3305
        have hw : |(2735421267/5000000000 : ℝ)|=(2735421267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058201331/2000000000 : ℝ)*x 0 + (27354213/50000000 : ℝ)*x 1 + (-1876979911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058201331/2000000000 : ℝ)^4329 ≤ (43439137184907/100000000000000 : ℝ)^3305 := by
    have hnat : (1058201331 : ℕ)^4329*100000000000000^3305 ≤ 43439137184907^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058201331 2000000000 43439137184907 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27354213/50000000 : ℝ)^4329 ≤ (45383148247623/100000000000000 : ℝ)^3305 := by
    have hnat : (27354213 : ℕ)^4329*100000000000000^3305 ≤ 45383148247623^3305*50000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27354213 50000000 45383148247623 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876979911/10000000000 : ℝ)^4329 ≤ (5588857278341/50000000000000 : ℝ)^3305 := by
    have hnat : (1876979911 : ℕ)^4329*50000000000000^3305 ≤ 5588857278341^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876979911 10000000000 5588857278341 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058201331/2000000000 : ℝ), (27354213/50000000 : ℝ), (-1876979911/10000000000 : ℝ)] ![(43439137184907/100000000000000 : ℝ), (45383148247623/100000000000000 : ℝ), (5588857278341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058201331/2000000000 : ℝ)|^4329 ≤ (43439137184907/100000000000000 : ℝ)^3305
        have hw : |(1058201331/2000000000 : ℝ)|=(1058201331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27354213/50000000 : ℝ)|^4329 ≤ (45383148247623/100000000000000 : ℝ)^3305
        have hw : |(27354213/50000000 : ℝ)|=(27354213/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876979911/10000000000 : ℝ)|^4329 ≤ (5588857278341/50000000000000 : ℝ)^3305
        have hw : |(-1876979911/10000000000 : ℝ)|=(1876979911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s2_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078539631/2500000000 : ℝ)*x 0 + (4619018319/10000000000 : ℝ)*x 1 + (2014091749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078539631/2500000000 : ℝ)^4329 ≤ (16624349204453/50000000000000 : ℝ)^3305 := by
    have hnat : (1078539631 : ℕ)^4329*50000000000000^3305 ≤ 16624349204453^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078539631 2500000000 16624349204453 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4619018319/10000000000 : ℝ)^4329 ≤ (181796666287/500000000000 : ℝ)^3305 := by
    have hnat : (4619018319 : ℕ)^4329*500000000000^3305 ≤ 181796666287^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619018319 10000000000 181796666287 500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014091749/5000000000 : ℝ)^4329 ≤ (30391968316181/100000000000000 : ℝ)^3305 := by
    have hnat : (2014091749 : ℕ)^4329*100000000000000^3305 ≤ 30391968316181^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014091749 5000000000 30391968316181 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078539631/2500000000 : ℝ), (4619018319/10000000000 : ℝ), (2014091749/5000000000 : ℝ)] ![(16624349204453/50000000000000 : ℝ), (181796666287/500000000000 : ℝ), (30391968316181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078539631/2500000000 : ℝ)|^4329 ≤ (16624349204453/50000000000000 : ℝ)^3305
        have hw : |(1078539631/2500000000 : ℝ)|=(1078539631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4619018319/10000000000 : ℝ)|^4329 ≤ (181796666287/500000000000 : ℝ)^3305
        have hw : |(4619018319/10000000000 : ℝ)|=(4619018319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014091749/5000000000 : ℝ)|^4329 ≤ (30391968316181/100000000000000 : ℝ)^3305
        have hw : |(2014091749/5000000000 : ℝ)|=(2014091749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9631/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10023/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16001/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9631/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9631/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9631/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9631/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9631/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9631/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/3125 : ℝ) ^ (541/128 : ℝ) ≤ (1425788895512883/100000000000000000000 : ℝ) := by
    have hpowers : (223/3125 : ℝ)^541 ≤ (1425788895512883/100000000000000000000 : ℝ)^128 := by
      have hnat : (223 : ℕ)^541*100000000000000000000^128 ≤ 1425788895512883^128*3125^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 3125 1425788895512883 100000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/3125 : ℝ)) (X := (1425788895512883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (9631/50000 : ℝ) ^ (541/128 : ℝ) ≤ (94786321679615377/100000000000000000000 : ℝ) := by
    have hpowers : (9631/50000 : ℝ)^541 ≤ (94786321679615377/100000000000000000000 : ℝ)^128 := by
      have hnat : (9631 : ℕ)^541*100000000000000000000^128 ≤ 94786321679615377^128*50000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9631 50000 94786321679615377 100000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9631/50000 : ℝ)) (X := (94786321679615377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001425788895512883/50000000000000000000 : ℝ) ≤ (10000067467279937/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (50001425788895512883/50000000000000000000 : ℝ)^128 ≤ (10000067467279937/10000000000000000 : ℝ)^541 := by
      have hnat : (50001425788895512883 : ℕ)^128*10000000000000000^541 ≤ 10000067467279937^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001425788895512883 50000000000000000000 10000067467279937 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000067467279937/10000000000000000 : ℝ)) (X := (50001425788895512883/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (5004810605528756413/5000000000000000000 : ℝ) ≤ (1250284441544993/1250000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (5004810605528756413/5000000000000000000 : ℝ)^128 ≤ (1250284441544993/1250000000000000 : ℝ)^541 := by
      have hnat : (5004810605528756413 : ℕ)^128*1250000000000000^541 ≤ 1250284441544993^541*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5004810605528756413 5000000000000000000 1250284441544993 1250000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250284441544993/1250000000000000 : ℝ)) (X := (5004810605528756413/5000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50094786321679615377/50000000000000000000 : ℝ) ≤ (10004483597439951/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (50094786321679615377/50000000000000000000 : ℝ)^128 ≤ (10004483597439951/10000000000000000 : ℝ)^541 := by
      have hnat : (50094786321679615377 : ℕ)^128*10000000000000000^541 ≤ 10004483597439951^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50094786321679615377 50000000000000000000 10004483597439951 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004483597439951/10000000000000000 : ℝ)) (X := (50094786321679615377/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1425788895512883/100000000000000000000 : ℝ) ≤ ((60614652301707328079/60630000000000000000 : ℝ)+2*(2208065080007/1212600000000000 : ℝ)*(223/3125 : ℝ))^(541/128 : ℝ) := by
    rw [show (60614652301707328079/60630000000000000000 : ℝ)+2*(2208065080007/1212600000000000 : ℝ)*(223/3125 : ℝ)=(10000067467279937/10000000000000000 : ℝ) by norm_num, show 1+2*(1425788895512883/100000000000000000000 : ℝ)=(50001425788895512883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(94786321679615377/100000000000000000000 : ℝ)+(1425788895512883/100000000000000000000 : ℝ) ≤ ((60614652301707328079/60630000000000000000 : ℝ)+(2208065080007/1212600000000000 : ℝ)*((9631/50000 : ℝ)+(223/3125 : ℝ)))^(541/128 : ℝ) := by
    rw [show (60614652301707328079/60630000000000000000 : ℝ)+(2208065080007/1212600000000000 : ℝ)*((9631/50000 : ℝ)+(223/3125 : ℝ))=(1250284441544993/1250000000000000 : ℝ) by norm_num, show 1+(94786321679615377/100000000000000000000 : ℝ)+(1425788895512883/100000000000000000000 : ℝ)=(5004810605528756413/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(94786321679615377/100000000000000000000 : ℝ) ≤ ((60614652301707328079/60630000000000000000 : ℝ)+2*(2208065080007/1212600000000000 : ℝ)*(9631/50000 : ℝ))^(541/128 : ℝ) := by
    rw [show (60614652301707328079/60630000000000000000 : ℝ)+2*(2208065080007/1212600000000000 : ℝ)*(9631/50000 : ℝ)=(10004483597439951/10000000000000000 : ℝ) by norm_num, show 1+2*(94786321679615377/100000000000000000000 : ℝ)=(50094786321679615377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60614652301707328079/60630000000000000000 : ℝ)*(X 1 0+X 2 0)+(2208065080007/1212600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (223/3125 : ℝ)) (hi := (9631/50000 : ℝ)) (c := (60614652301707328079/60630000000000000000 : ℝ)) (alpha := (2208065080007/1212600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60614652301707328079/60630000000000000000 : ℝ)*(X 0 1+X 2 1)+(2208065080007/1212600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (223/3125 : ℝ)) (hi := (9631/50000 : ℝ)) (c := (60614652301707328079/60630000000000000000 : ℝ)) (alpha := (2208065080007/1212600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60614652301707328079/60630000000000000000 : ℝ)*(X 0 2+X 1 2)+(2208065080007/1212600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (223/3125 : ℝ)) (hi := (9631/50000 : ℝ)) (c := (60614652301707328079/60630000000000000000 : ℝ)) (alpha := (2208065080007/1212600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2012078591/10000000000 : ℝ)*X 0 0+(547257931/1000000000 : ℝ)*X 0 1+(5189881441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364081369/10000000000 : ℝ)*X 1 0+(-2157941123/10000000000 : ℝ)*X 1 1+(5189881669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536408137/1000000000 : ℝ)*X 2 0+(5189881653/10000000000 : ℝ)*X 2 1+(-1078970571/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4314034337/10000000000 : ℝ)*X 0 0+(2012254653/5000000000 : ℝ)*X 0 1+(2311330303/5000000000 : ℝ)*X 0 2+(4314034337/10000000000 : ℝ)*X 1 0+(2012254653/5000000000 : ℝ)*X 1 1+(2311330303/5000000000 : ℝ)*X 1 2+(4314034337/10000000000 : ℝ)*X 2 0+(2012254653/5000000000 : ℝ)*X 2 1+(2311330303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-201213719/1000000000 : ℝ)*X 0 0+(2595801531/5000000000 : ℝ)*X 0 1+(2735421299/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330687919/625000000 : ℝ)*X 1 0+(-375395987/2000000000 : ℝ)*X 1 1+(2735421267/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058201331/2000000000 : ℝ)*X 2 0+(27354213/50000000 : ℝ)*X 2 1+(-1876979911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078539631/2500000000 : ℝ)*X 0 0+(4619018319/10000000000 : ℝ)*X 0 1+(2014091749/5000000000 : ℝ)*X 0 2+(1078539631/2500000000 : ℝ)*X 1 0+(4619018319/10000000000 : ℝ)*X 1 1+(2014091749/5000000000 : ℝ)*X 1 2+(1078539631/2500000000 : ℝ)*X 2 0+(4619018319/10000000000 : ℝ)*X 2 1+(2014091749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4492219485654459438103908751/505250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1527559783/100000000000000 : ℝ)*(base19) + (723653049/50000000000000 : ℝ)*(base23) + (10850617/25000000000000 : ℝ)*(lower2) + (110086037/50000000000000 : ℝ)*(upper3) + (13941097/10000000000000 : ℝ)*(upper5) + (1302306463434923/50000000000000 : ℝ)*(major0) + (1302306463434923/50000000000000 : ℝ)*(major1) + (1302306463434923/50000000000000 : ℝ)*(major2) + (3537367595280441/100000000000000 : ℝ)*(sp0) + (884346813522827/25000000000000 : ℝ)*(sp1) + (3537387334344993/100000000000000 : ℝ)*(sp2) + (334365352092331/20000000000000 : ℝ)*(sp3) + (423727413/2000000000000 : ℝ)*(sp4) + (125190719/1250000000000 : ℝ)*(sp7) + (66873471028767/4000000000000 : ℝ)*(f.failure) + (3537388781651091/100000000000000 : ℝ)*(f.sum) + (130662125501999/30315000000000000000000000000 : ℝ)*base66 + (129763086092410263/21500000000000000000000000000000 : ℝ)*base68 + (33061154738910263/21500000000000000000000000000000 : ℝ)*base70 + (206931155852910263/21500000000000000000000000000000 : ℝ)*base72 + (32500015005271/30315000000000000000000000000 : ℝ)*base73 + (154929365465410263/21500000000000000000000000000000 : ℝ)*base76 + (289414610649910263/21500000000000000000000000000000 : ℝ)*base78 + (165709095600910263/21500000000000000000000000000000 : ℝ)*base80 + (124840885611001/30315000000000000000000000000 : ℝ)*base81 + (720949/200000000000000000000 : ℝ)*base89 + (720949/200000000000000000000 : ℝ)*base91 + (720949/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1799155235818367931349789269/252625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93666361/6250000000000 : ℝ)*(base19) + (324716779/20000000000000 : ℝ)*(base23) + (32868817/20000000000000 : ℝ)*(upper3) + (2601667/4000000000000 : ℝ)*(lower4) + (120461337/100000000000000 : ℝ)*(upper5) + (659209204167537/25000000000000 : ℝ)*(major0) + (659209204167537/25000000000000 : ℝ)*(major1) + (659209204167537/25000000000000 : ℝ)*(major2) + (546677619/3125000000000 : ℝ)*(sp1) + (10019666267/50000000000000 : ℝ)*(sp2) + (1790576450202057/50000000000000 : ℝ)*(sp4) + (3581133908058529/100000000000000 : ℝ)*(sp5) + (895282809371921/25000000000000 : ℝ)*(sp6) + (105782530971341/6250000000000 : ℝ)*(sp7) + (105782530971341/6250000000000 : ℝ)*(f.failure) + (1790576450202057/50000000000000 : ℝ)*(f.sum) + (18888219368157/5052500000000000000000000000 : ℝ)*base66 + (77516335828018997/10750000000000000000000000000000 : ℝ)*base68 + (77834661904018997/10750000000000000000000000000000 : ℝ)*base70 + (43010910363018997/10750000000000000000000000000000 : ℝ)*base72 + (15603130989681/10105000000000000000000000000 : ℝ)*base73 + (34300815463518997/10750000000000000000000000000000 : ℝ)*base76 + (23184438457018997/10750000000000000000000000000000 : ℝ)*base78 + (33391241193518997/10750000000000000000000000000000 : ℝ)*base80 + (2361955950387/5052500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1627727/312500000000000000000 : ℝ)*base89 + (1627727/312500000000000000000 : ℝ)*base91 + (1627727/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1369_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9631/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1369_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1369_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1369_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1369_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1369_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

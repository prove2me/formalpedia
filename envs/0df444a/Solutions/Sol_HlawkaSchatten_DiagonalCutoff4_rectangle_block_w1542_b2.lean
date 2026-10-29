-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1542_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:05.428675+00:00
-- url     : https://prove2.me/submissions/639ca78f-c5d6-43a8-a98e-74ce3691def1

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
theorem support_rectangle_w1542_s6_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824592197/10000000000 : ℝ)*x 0 + (5429356229/10000000000 : ℝ)*x 1 + (1304753477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824592197/10000000000 : ℝ)^4581 ≤ (5590336886897/50000000000000 : ℝ)^3557 := by
    have hnat : (1824592197 : ℕ)^4581*50000000000000^3557 ≤ 5590336886897^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824592197 10000000000 5590336886897 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429356229/10000000000 : ℝ)^4581 ≤ (22769677773101/50000000000000 : ℝ)^3557 := by
    have hnat : (5429356229 : ℕ)^4581*50000000000000^3557 ≤ 22769677773101^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429356229 10000000000 22769677773101 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304753477/2500000000 : ℝ)^4581 ≤ (5409996333147/12500000000000 : ℝ)^3557 := by
    have hnat : (1304753477 : ℕ)^4581*12500000000000^3557 ≤ 5409996333147^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304753477 2500000000 5409996333147 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824592197/10000000000 : ℝ), (5429356229/10000000000 : ℝ), (1304753477/2500000000 : ℝ)] ![(5590336886897/50000000000000 : ℝ), (22769677773101/50000000000000 : ℝ), (5409996333147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824592197/10000000000 : ℝ)|^4581 ≤ (5590336886897/50000000000000 : ℝ)^3557
        have hw : |(-1824592197/10000000000 : ℝ)|=(1824592197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429356229/10000000000 : ℝ)|^4581 ≤ (22769677773101/50000000000000 : ℝ)^3557
        have hw : |(5429356229/10000000000 : ℝ)|=(5429356229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304753477/2500000000 : ℝ)|^4581 ≤ (5409996333147/12500000000000 : ℝ)^3557
        have hw : |(1304753477/2500000000 : ℝ)|=(1304753477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s6_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674936503/5000000000 : ℝ)*x 0 + (-966127957/5000000000 : ℝ)*x 1 + (1304753477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674936503/5000000000 : ℝ)^4581 ≤ (44682572024823/100000000000000 : ℝ)^3557 := by
    have hnat : (2674936503 : ℕ)^4581*100000000000000^3557 ≤ 44682572024823^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674936503 5000000000 44682572024823 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966127957/5000000000 : ℝ)^4581 ≤ (3009364324723/25000000000000 : ℝ)^3557 := by
    have hnat : (966127957 : ℕ)^4581*25000000000000^3557 ≤ 3009364324723^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966127957 5000000000 3009364324723 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304753477/2500000000 : ℝ)^4581 ≤ (5409996333147/12500000000000 : ℝ)^3557 := by
    have hnat : (1304753477 : ℕ)^4581*12500000000000^3557 ≤ 5409996333147^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304753477 2500000000 5409996333147 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674936503/5000000000 : ℝ), (-966127957/5000000000 : ℝ), (1304753477/2500000000 : ℝ)] ![(44682572024823/100000000000000 : ℝ), (3009364324723/25000000000000 : ℝ), (5409996333147/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674936503/5000000000 : ℝ)|^4581 ≤ (44682572024823/100000000000000 : ℝ)^3557
        have hw : |(2674936503/5000000000 : ℝ)|=(2674936503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966127957/5000000000 : ℝ)|^4581 ≤ (3009364324723/25000000000000 : ℝ)^3557
        have hw : |(-966127957/5000000000 : ℝ)|=(966127957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304753477/2500000000 : ℝ)|^4581 ≤ (5409996333147/12500000000000 : ℝ)^3557
        have hw : |(1304753477/2500000000 : ℝ)|=(1304753477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s6_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069974601/2000000000 : ℝ)*x 0 + (5219013907/10000000000 : ℝ)*x 1 + (-483063979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069974601/2000000000 : ℝ)^4581 ≤ (22341286007033/50000000000000 : ℝ)^3557 := by
    have hnat : (1069974601 : ℕ)^4581*50000000000000^3557 ≤ 22341286007033^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069974601 2000000000 22341286007033 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219013907/10000000000 : ℝ)^4581 ≤ (1352499082953/3125000000000 : ℝ)^3557 := by
    have hnat : (5219013907 : ℕ)^4581*3125000000000^3557 ≤ 1352499082953^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219013907 10000000000 1352499082953 3125000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483063979/2500000000 : ℝ)^4581 ≤ (12037457314939/100000000000000 : ℝ)^3557 := by
    have hnat : (483063979 : ℕ)^4581*100000000000000^3557 ≤ 12037457314939^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483063979 2500000000 12037457314939 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069974601/2000000000 : ℝ), (5219013907/10000000000 : ℝ), (-483063979/2500000000 : ℝ)] ![(22341286007033/50000000000000 : ℝ), (1352499082953/3125000000000 : ℝ), (12037457314939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069974601/2000000000 : ℝ)|^4581 ≤ (22341286007033/50000000000000 : ℝ)^3557
        have hw : |(1069974601/2000000000 : ℝ)|=(1069974601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219013907/10000000000 : ℝ)|^4581 ≤ (1352499082953/3125000000000 : ℝ)^3557
        have hw : |(5219013907/10000000000 : ℝ)|=(5219013907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-483063979/2500000000 : ℝ)|^4581 ≤ (12037457314939/100000000000000 : ℝ)^3557
        have hw : |(-483063979/2500000000 : ℝ)|=(483063979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s6_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425600301/1000000000 : ℝ)*x 0 + (2009120073/5000000000 : ℝ)*x 1 + (4505309401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425600301/1000000000 : ℝ)^4581 ≤ (33281115198571/100000000000000 : ℝ)^3557 := by
    have hnat : (425600301 : ℕ)^4581*100000000000000^3557 ≤ 33281115198571^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425600301 1000000000 33281115198571 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009120073/5000000000 : ℝ)^4581 ≤ (30906123321323/100000000000000 : ℝ)^3557 := by
    have hnat : (2009120073 : ℕ)^4581*100000000000000^3557 ≤ 30906123321323^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009120073 5000000000 30906123321323 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505309401/10000000000 : ℝ)^4581 ≤ (4476595183921/12500000000000 : ℝ)^3557 := by
    have hnat : (4505309401 : ℕ)^4581*12500000000000^3557 ≤ 4476595183921^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505309401 10000000000 4476595183921 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425600301/1000000000 : ℝ), (2009120073/5000000000 : ℝ), (4505309401/10000000000 : ℝ)] ![(33281115198571/100000000000000 : ℝ), (30906123321323/100000000000000 : ℝ), (4476595183921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425600301/1000000000 : ℝ)|^4581 ≤ (33281115198571/100000000000000 : ℝ)^3557
        have hw : |(425600301/1000000000 : ℝ)|=(425600301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009120073/5000000000 : ℝ)|^4581 ≤ (30906123321323/100000000000000 : ℝ)^3557
        have hw : |(2009120073/5000000000 : ℝ)|=(2009120073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505309401/10000000000 : ℝ)|^4581 ≤ (4476595183921/12500000000000 : ℝ)^3557
        have hw : |(4505309401/10000000000 : ℝ)|=(4505309401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s6_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824619793/10000000000 : ℝ)*x 0 + (2610051583/5000000000 : ℝ)*x 1 + (2714129533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824619793/10000000000 : ℝ)^4581 ≤ (2795222889411/25000000000000 : ℝ)^3557 := by
    have hnat : (1824619793 : ℕ)^4581*25000000000000^3557 ≤ 2795222889411^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824619793 10000000000 2795222889411 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610051583/5000000000 : ℝ)^4581 ≤ (21645802194297/50000000000000 : ℝ)^3557 := by
    have hnat : (2610051583 : ℕ)^4581*50000000000000^3557 ≤ 21645802194297^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610051583 5000000000 21645802194297 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714129533/5000000000 : ℝ)^4581 ≤ (14227345013/31250000000 : ℝ)^3557 := by
    have hnat : (2714129533 : ℕ)^4581*31250000000^3557 ≤ 14227345013^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714129533 5000000000 14227345013 31250000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824619793/10000000000 : ℝ), (2610051583/5000000000 : ℝ), (2714129533/5000000000 : ℝ)] ![(2795222889411/25000000000000 : ℝ), (21645802194297/50000000000000 : ℝ), (14227345013/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824619793/10000000000 : ℝ)|^4581 ≤ (2795222889411/25000000000000 : ℝ)^3557
        have hw : |(-1824619793/10000000000 : ℝ)|=(1824619793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610051583/5000000000 : ℝ)|^4581 ≤ (21645802194297/50000000000000 : ℝ)^3557
        have hw : |(2610051583/5000000000 : ℝ)|=(2610051583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714129533/5000000000 : ℝ)|^4581 ≤ (14227345013/31250000000 : ℝ)^3557
        have hw : |(2714129533/5000000000 : ℝ)|=(2714129533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_s6_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170242681/400000000 : ℝ)*x 0 + (4502787369/10000000000 : ℝ)*x 1 + (804156221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170242681/400000000 : ℝ)^4581 ≤ (33281759894697/100000000000000 : ℝ)^3557 := by
    have hnat : (170242681 : ℕ)^4581*100000000000000^3557 ≤ 33281759894697^3557*400000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170242681 400000000 33281759894697 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502787369/10000000000 : ℝ)^4581 ≤ (8946736126269/25000000000000 : ℝ)^3557 := by
    have hnat : (4502787369 : ℕ)^4581*25000000000000^3557 ≤ 8946736126269^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502787369 10000000000 8946736126269 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804156221/2000000000 : ℝ)^4581 ≤ (6186259116761/20000000000000 : ℝ)^3557 := by
    have hnat : (804156221 : ℕ)^4581*20000000000000^3557 ≤ 6186259116761^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804156221 2000000000 6186259116761 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170242681/400000000 : ℝ), (4502787369/10000000000 : ℝ), (804156221/2000000000 : ℝ)] ![(33281759894697/100000000000000 : ℝ), (8946736126269/25000000000000 : ℝ), (6186259116761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170242681/400000000 : ℝ)|^4581 ≤ (33281759894697/100000000000000 : ℝ)^3557
        have hw : |(170242681/400000000 : ℝ)|=(170242681/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502787369/10000000000 : ℝ)|^4581 ≤ (8946736126269/25000000000000 : ℝ)^3557
        have hw : |(4502787369/10000000000 : ℝ)|=(4502787369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804156221/2000000000 : ℝ)|^4581 ≤ (6186259116761/20000000000000 : ℝ)^3557
        have hw : |(804156221/2000000000 : ℝ)|=(804156221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11027/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5513/50000 : ℝ) ^ (4579/1024 : ℝ) ≤ (5223961510666231/100000000000000000000 : ℝ) := by
    have hpowers : (5513/50000 : ℝ)^4579 ≤ (5223961510666231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5513 : ℕ)^4579*100000000000000000000^1024 ≤ 5223961510666231^1024*50000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5513 50000 5223961510666231 100000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5513/50000 : ℝ)) (X := (5223961510666231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4579/1024 : ℝ) ≤ (5963241804510387/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4579 ≤ (5963241804510387/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4579*25000000000000000000^1024 ≤ 5963241804510387^1024*20000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5963241804510387 25000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5963241804510387/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005223961510666231/50000000000000000000 : ℝ) ≤ (5000116818511591/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50005223961510666231/50000000000000000000 : ℝ)^1024 ≤ (5000116818511591/5000000000000000 : ℝ)^4579 := by
      have hnat : (50005223961510666231 : ℕ)^1024*5000000000000000^4579 ≤ 5000116818511591^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005223961510666231 50000000000000000000 5000116818511591 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000116818511591/5000000000000000 : ℝ)) (X := (50005223961510666231/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029076928728707779/100000000000000000000 : ℝ) ≤ (400026006914041/400000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (100029076928728707779/100000000000000000000 : ℝ)^1024 ≤ (400026006914041/400000000000000 : ℝ)^4579 := by
      have hnat : (100029076928728707779 : ℕ)^1024*400000000000000^4579 ≤ 400026006914041^4579*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029076928728707779 100000000000000000000 400026006914041 400000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400026006914041/400000000000000 : ℝ)) (X := (100029076928728707779/100000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505963241804510387/12500000000000000000 : ℝ) ≤ (2500266677169717/2500000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (12505963241804510387/12500000000000000000 : ℝ)^1024 ≤ (2500266677169717/2500000000000000 : ℝ)^4579 := by
      have hnat : (12505963241804510387 : ℕ)^1024*2500000000000000^4579 ≤ 2500266677169717^4579*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505963241804510387 12500000000000000000 2500266677169717 2500000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500266677169717/2500000000000000 : ℝ)) (X := (12505963241804510387/12500000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5223961510666231/100000000000000000000 : ℝ) ≤ ((22290928169705387351/22295000000000000000 : ℝ)+2*(416535827843/445900000000000 : ℝ)*(5513/50000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (22290928169705387351/22295000000000000000 : ℝ)+2*(416535827843/445900000000000 : ℝ)*(5513/50000 : ℝ)=(5000116818511591/5000000000000000 : ℝ) by norm_num, show 1+2*(5223961510666231/100000000000000000000 : ℝ)=(50005223961510666231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5963241804510387/25000000000000000000 : ℝ)+(5223961510666231/100000000000000000000 : ℝ) ≤ ((22290928169705387351/22295000000000000000 : ℝ)+(416535827843/445900000000000 : ℝ)*((3097/20000 : ℝ)+(5513/50000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (22290928169705387351/22295000000000000000 : ℝ)+(416535827843/445900000000000 : ℝ)*((3097/20000 : ℝ)+(5513/50000 : ℝ))=(400026006914041/400000000000000 : ℝ) by norm_num, show 1+(5963241804510387/25000000000000000000 : ℝ)+(5223961510666231/100000000000000000000 : ℝ)=(100029076928728707779/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5963241804510387/25000000000000000000 : ℝ) ≤ ((22290928169705387351/22295000000000000000 : ℝ)+2*(416535827843/445900000000000 : ℝ)*(3097/20000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (22290928169705387351/22295000000000000000 : ℝ)+2*(416535827843/445900000000000 : ℝ)*(3097/20000 : ℝ)=(2500266677169717/2500000000000000 : ℝ) by norm_num, show 1+2*(5963241804510387/25000000000000000000 : ℝ)=(12505963241804510387/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22290928169705387351/22295000000000000000 : ℝ)*(X 1 0+X 2 0)+(416535827843/445900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22290928169705387351/22295000000000000000 : ℝ)) (alpha := (416535827843/445900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22290928169705387351/22295000000000000000 : ℝ)*(X 0 1+X 2 1)+(416535827843/445900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22290928169705387351/22295000000000000000 : ℝ)) (alpha := (416535827843/445900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22290928169705387351/22295000000000000000 : ℝ)*(X 0 2+X 1 2)+(416535827843/445900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (5513/50000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (22290928169705387351/22295000000000000000 : ℝ)) (alpha := (416535827843/445900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1824592197/10000000000 : ℝ)*X 0 0+(5429356229/10000000000 : ℝ)*X 0 1+(1304753477/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674936503/5000000000 : ℝ)*X 1 0+(-966127957/5000000000 : ℝ)*X 1 1+(1304753477/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069974601/2000000000 : ℝ)*X 2 0+(5219013907/10000000000 : ℝ)*X 2 1+(-483063979/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((425600301/1000000000 : ℝ)*X 0 0+(2009120073/5000000000 : ℝ)*X 0 1+(4505309401/10000000000 : ℝ)*X 0 2+(425600301/1000000000 : ℝ)*X 1 0+(2009120073/5000000000 : ℝ)*X 1 1+(4505309401/10000000000 : ℝ)*X 1 2+(425600301/1000000000 : ℝ)*X 2 0+(2009120073/5000000000 : ℝ)*X 2 1+(4505309401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1824619793/10000000000 : ℝ)*X 0 0+(2610051583/5000000000 : ℝ)*X 0 1+(2714129533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((170242681/400000000 : ℝ)*X 0 0+(4502787369/10000000000 : ℝ)*X 0 1+(804156221/2000000000 : ℝ)*X 0 2+(170242681/400000000 : ℝ)*X 1 0+(4502787369/10000000000 : ℝ)*X 1 1+(804156221/2000000000 : ℝ)*X 1 2+(170242681/400000000 : ℝ)*X 2 0+(4502787369/10000000000 : ℝ)*X 2 1+(804156221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12749698715492487757797639/2843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (787850891/100000000000000 : ℝ)*(base19) + (737436617/100000000000000 : ℝ)*(base23) + (13247789/50000000000000 : ℝ)*(lower2) + (115319541/100000000000000 : ℝ)*(upper3) + (7704329/10000000000000 : ℝ)*(upper5) + (850910999028237/25000000000000 : ℝ)*(major0) + (850910999028237/25000000000000 : ℝ)*(major1) + (850910999028237/25000000000000 : ℝ)*(major2) + (4754168025378501/100000000000000 : ℝ)*(sp0) + (4754179727703089/100000000000000 : ℝ)*(sp1) + (4754179778117363/100000000000000 : ℝ)*(sp2) + (2053101412157149/100000000000000 : ℝ)*(sp3) + (12490175479/100000000000000 : ℝ)*(sp4) + (5915067741/100000000000000 : ℝ)*(sp5) + (205310732722489/10000000000000 : ℝ)*(f.failure) + (4754180515553981/100000000000000 : ℝ)*(f.sum) + (638556176331/455000000000000000000000000 : ℝ)*base65 + (3226374551617849/875000000000000000000000000000 : ℝ)*base68 + (7527926745367849/875000000000000000000000000000 : ℝ)*base70 + (999343340757151/875000000000000000000000000000 : ℝ)*base71 + (1292919900199/455000000000000000000000000 : ℝ)*base74 + (8306438124117849/875000000000000000000000000000 : ℝ)*base76 + (2335780655117849/875000000000000000000000000000 : ℝ)*base78 + (8007959049867849/875000000000000000000000000000 : ℝ)*base80 + (354639605147/227500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (34357/100000000000000000000 : ℝ)*base89 + (34357/100000000000000000000 : ℝ)*base91 + (34357/100000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1542_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11027/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1542_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1542_box_0 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-808087801/5000000000 : ℝ)*x 0 + (5399597943/10000000000 : ℝ)*x 1 + (269979887/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808087801/5000000000 : ℝ)^4581 ≤ (597731074439/6250000000000 : ℝ)^3557 := by
    have hnat : (808087801 : ℕ)^4581*6250000000000^3557 ≤ 597731074439^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808087801 5000000000 597731074439 6250000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399597943/10000000000 : ℝ)^4581 ≤ (45218152491451/100000000000000 : ℝ)^3557 := by
    have hnat : (5399597943 : ℕ)^4581*100000000000000^3557 ≤ 45218152491451^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399597943 10000000000 45218152491451 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269979887/500000000 : ℝ)^4581 ≤ (22609075151029/50000000000000 : ℝ)^3557 := by
    have hnat : (269979887 : ℕ)^4581*50000000000000^3557 ≤ 22609075151029^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269979887 500000000 22609075151029 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-808087801/5000000000 : ℝ), (5399597943/10000000000 : ℝ), (269979887/500000000 : ℝ)] ![(597731074439/6250000000000 : ℝ), (45218152491451/100000000000000 : ℝ), (22609075151029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-808087801/5000000000 : ℝ)|^4581 ≤ (597731074439/6250000000000 : ℝ)^3557
        have hw : |(-808087801/5000000000 : ℝ)|=(808087801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399597943/10000000000 : ℝ)|^4581 ≤ (45218152491451/100000000000000 : ℝ)^3557
        have hw : |(5399597943/10000000000 : ℝ)|=(5399597943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269979887/500000000 : ℝ)|^4581 ≤ (22609075151029/50000000000000 : ℝ)^3557
        have hw : |(269979887/500000000 : ℝ)|=(269979887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_1 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635529497/5000000000 : ℝ)*x 0 + (-179468821/1000000000 : ℝ)*x 1 + (5399597903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635529497/5000000000 : ℝ)^4581 ≤ (43836612879499/100000000000000 : ℝ)^3557 := by
    have hnat : (2635529497 : ℕ)^4581*100000000000000^3557 ≤ 43836612879499^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635529497 5000000000 43836612879499 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179468821/1000000000 : ℝ)^4581 ≤ (10945235047699/100000000000000 : ℝ)^3557 := by
    have hnat : (179468821 : ℕ)^4581*100000000000000^3557 ≤ 10945235047699^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179468821 1000000000 10945235047699 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399597903/10000000000 : ℝ)^4581 ≤ (11304538015011/25000000000000 : ℝ)^3557 := by
    have hnat : (5399597903 : ℕ)^4581*25000000000000^3557 ≤ 11304538015011^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399597903 10000000000 11304538015011 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635529497/5000000000 : ℝ), (-179468821/1000000000 : ℝ), (5399597903/10000000000 : ℝ)] ![(43836612879499/100000000000000 : ℝ), (10945235047699/100000000000000 : ℝ), (11304538015011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635529497/5000000000 : ℝ)|^4581 ≤ (43836612879499/100000000000000 : ℝ)^3557
        have hw : |(2635529497/5000000000 : ℝ)|=(2635529497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179468821/1000000000 : ℝ)|^4581 ≤ (10945235047699/100000000000000 : ℝ)^3557
        have hw : |(-179468821/1000000000 : ℝ)|=(179468821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399597903/10000000000 : ℝ)|^4581 ≤ (11304538015011/25000000000000 : ℝ)^3557
        have hw : |(5399597903/10000000000 : ℝ)|=(5399597903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_2 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271059177/10000000000 : ℝ)*x 0 + (269979893/500000000 : ℝ)*x 1 + (-1794688019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271059177/10000000000 : ℝ)^4581 ≤ (43836614839547/100000000000000 : ℝ)^3557 := by
    have hnat : (5271059177 : ℕ)^4581*100000000000000^3557 ≤ 43836614839547^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271059177 10000000000 43836614839547 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269979893/500000000 : ℝ)^4581 ≤ (1130453789907/2500000000000 : ℝ)^3557 := by
    have hnat : (269979893 : ℕ)^4581*2500000000000^3557 ≤ 1130453789907^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269979893 500000000 1130453789907 2500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794688019/10000000000 : ℝ)^4581 ≤ (1094523354751/10000000000000 : ℝ)^3557 := by
    have hnat : (1794688019 : ℕ)^4581*10000000000000^3557 ≤ 1094523354751^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794688019 10000000000 1094523354751 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271059177/10000000000 : ℝ), (269979893/500000000 : ℝ), (-1794688019/10000000000 : ℝ)] ![(43836614839547/100000000000000 : ℝ), (1130453789907/2500000000000 : ℝ), (1094523354751/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271059177/10000000000 : ℝ)|^4581 ≤ (43836614839547/100000000000000 : ℝ)^3557
        have hw : |(5271059177/10000000000 : ℝ)|=(5271059177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269979893/500000000 : ℝ)|^4581 ≤ (1130453789907/2500000000000 : ℝ)^3557
        have hw : |(269979893/500000000 : ℝ)|=(269979893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794688019/10000000000 : ℝ)|^4581 ≤ (1094523354751/10000000000000 : ℝ)^3557
        have hw : |(-1794688019/10000000000 : ℝ)|=(1794688019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_3 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4457776867/10000000000 : ℝ)*x 0 + (4161911589/10000000000 : ℝ)*x 1 + (4161911817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4457776867/10000000000 : ℝ)^4581 ≤ (1766344640579/5000000000000 : ℝ)^3557 := by
    have hnat : (4457776867 : ℕ)^4581*5000000000000^3557 ≤ 1766344640579^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4457776867 10000000000 1766344640579 5000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4161911589/10000000000 : ℝ)^4581 ≤ (32336552446749/100000000000000 : ℝ)^3557 := by
    have hnat : (4161911589 : ℕ)^4581*100000000000000^3557 ≤ 32336552446749^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161911589 10000000000 32336552446749 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161911817/10000000000 : ℝ)^4581 ≤ (6467310945641/20000000000000 : ℝ)^3557 := by
    have hnat : (4161911817 : ℕ)^4581*20000000000000^3557 ≤ 6467310945641^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161911817 10000000000 6467310945641 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4457776867/10000000000 : ℝ), (4161911589/10000000000 : ℝ), (4161911817/10000000000 : ℝ)] ![(1766344640579/5000000000000 : ℝ), (32336552446749/100000000000000 : ℝ), (6467310945641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4457776867/10000000000 : ℝ)|^4581 ≤ (1766344640579/5000000000000 : ℝ)^3557
        have hw : |(4457776867/10000000000 : ℝ)|=(4457776867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4161911589/10000000000 : ℝ)|^4581 ≤ (32336552446749/100000000000000 : ℝ)^3557
        have hw : |(4161911589/10000000000 : ℝ)|=(4161911589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161911817/10000000000 : ℝ)|^4581 ≤ (6467310945641/20000000000000 : ℝ)^3557
        have hw : |(4161911817/10000000000 : ℝ)|=(4161911817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_4 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038419843/10000000000 : ℝ)*x 0 + (262223613/500000000 : ℝ)*x 1 + (1048894493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038419843/10000000000 : ℝ)^4581 ≤ (128958800813/1000000000000 : ℝ)^3557 := by
    have hnat : (2038419843 : ℕ)^4581*1000000000000^3557 ≤ 128958800813^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038419843 10000000000 128958800813 1000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262223613/500000000 : ℝ)^4581 ≤ (43552058858217/100000000000000 : ℝ)^3557 := by
    have hnat : (262223613 : ℕ)^4581*100000000000000^3557 ≤ 43552058858217^3557*500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262223613 500000000 43552058858217 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048894493/2000000000 : ℝ)^4581 ≤ (8710412210141/20000000000000 : ℝ)^3557 := by
    have hnat : (1048894493 : ℕ)^4581*20000000000000^3557 ≤ 8710412210141^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048894493 2000000000 8710412210141 20000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038419843/10000000000 : ℝ), (262223613/500000000 : ℝ), (1048894493/2000000000 : ℝ)] ![(128958800813/1000000000000 : ℝ), (43552058858217/100000000000000 : ℝ), (8710412210141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038419843/10000000000 : ℝ)|^4581 ≤ (128958800813/1000000000000 : ℝ)^3557
        have hw : |(-2038419843/10000000000 : ℝ)|=(2038419843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262223613/500000000 : ℝ)|^4581 ≤ (43552058858217/100000000000000 : ℝ)^3557
        have hw : |(262223613/500000000 : ℝ)|=(262223613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048894493/2000000000 : ℝ)|^4581 ≤ (8710412210141/20000000000000 : ℝ)^3557
        have hw : |(1048894493/2000000000 : ℝ)|=(1048894493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_5 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378812923/10000000000 : ℝ)*x 0 + (-1859111039/10000000000 : ℝ)*x 1 + (524447273/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378812923/10000000000 : ℝ)^4581 ≤ (44994106415537/100000000000000 : ℝ)^3557 := by
    have hnat : (5378812923 : ℕ)^4581*100000000000000^3557 ≤ 44994106415537^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378812923 10000000000 44994106415537 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1859111039/10000000000 : ℝ)^4581 ≤ (11453829688117/100000000000000 : ℝ)^3557 := by
    have hnat : (1859111039 : ℕ)^4581*100000000000000^3557 ≤ 11453829688117^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859111039 10000000000 11453829688117 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524447273/1000000000 : ℝ)^4581 ≤ (1361001996403/3125000000000 : ℝ)^3557 := by
    have hnat : (524447273 : ℕ)^4581*3125000000000^3557 ≤ 1361001996403^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524447273 1000000000 1361001996403 3125000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378812923/10000000000 : ℝ), (-1859111039/10000000000 : ℝ), (524447273/1000000000 : ℝ)] ![(44994106415537/100000000000000 : ℝ), (11453829688117/100000000000000 : ℝ), (1361001996403/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378812923/10000000000 : ℝ)|^4581 ≤ (44994106415537/100000000000000 : ℝ)^3557
        have hw : |(5378812923/10000000000 : ℝ)|=(5378812923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1859111039/10000000000 : ℝ)|^4581 ≤ (11453829688117/100000000000000 : ℝ)^3557
        have hw : |(-1859111039/10000000000 : ℝ)|=(1859111039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524447273/1000000000 : ℝ)|^4581 ≤ (1361001996403/3125000000000 : ℝ)^3557
        have hw : |(524447273/1000000000 : ℝ)|=(524447273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_6 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378814139/10000000000 : ℝ)*x 0 + (5244472243/10000000000 : ℝ)*x 1 + (-1859110043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378814139/10000000000 : ℝ)^4581 ≤ (1799764780631/4000000000000 : ℝ)^3557 := by
    have hnat : (5378814139 : ℕ)^4581*4000000000000^3557 ≤ 1799764780631^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378814139 10000000000 1799764780631 4000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244472243/10000000000 : ℝ)^4581 ≤ (43552058676401/100000000000000 : ℝ)^3557 := by
    have hnat : (5244472243 : ℕ)^4581*100000000000000^3557 ≤ 43552058676401^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244472243 10000000000 43552058676401 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859110043/10000000000 : ℝ)^4581 ≤ (5726910892657/50000000000000 : ℝ)^3557 := by
    have hnat : (1859110043 : ℕ)^4581*50000000000000^3557 ≤ 5726910892657^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859110043 10000000000 5726910892657 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378814139/10000000000 : ℝ), (5244472243/10000000000 : ℝ), (-1859110043/10000000000 : ℝ)] ![(1799764780631/4000000000000 : ℝ), (43552058676401/100000000000000 : ℝ), (5726910892657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378814139/10000000000 : ℝ)|^4581 ≤ (1799764780631/4000000000000 : ℝ)^3557
        have hw : |(5378814139/10000000000 : ℝ)|=(5378814139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244472243/10000000000 : ℝ)|^4581 ≤ (43552058676401/100000000000000 : ℝ)^3557
        have hw : |(5244472243/10000000000 : ℝ)|=(5244472243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1859110043/10000000000 : ℝ)|^4581 ≤ (5726910892657/50000000000000 : ℝ)^3557
        have hw : |(-1859110043/10000000000 : ℝ)|=(1859110043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_7 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (810333389/2000000000 : ℝ)*x 0 + (2182418087/5000000000 : ℝ)*x 1 + (545604497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810333389/2000000000 : ℝ)^4581 ≤ (15618817395699/50000000000000 : ℝ)^3557 := by
    have hnat : (810333389 : ℕ)^4581*50000000000000^3557 ≤ 15618817395699^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810333389 2000000000 15618817395699 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182418087/5000000000 : ℝ)^4581 ≤ (4297647950091/12500000000000 : ℝ)^3557 := by
    have hnat : (2182418087 : ℕ)^4581*12500000000000^3557 ≤ 4297647950091^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182418087 5000000000 4297647950091 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545604497/1250000000 : ℝ)^4581 ≤ (8595295398031/25000000000000 : ℝ)^3557 := by
    have hnat : (545604497 : ℕ)^4581*25000000000000^3557 ≤ 8595295398031^3557*1250000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545604497 1250000000 8595295398031 25000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(810333389/2000000000 : ℝ), (2182418087/5000000000 : ℝ), (545604497/1250000000 : ℝ)] ![(15618817395699/50000000000000 : ℝ), (4297647950091/12500000000000 : ℝ), (8595295398031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(810333389/2000000000 : ℝ)|^4581 ≤ (15618817395699/50000000000000 : ℝ)^3557
        have hw : |(810333389/2000000000 : ℝ)|=(810333389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2182418087/5000000000 : ℝ)|^4581 ≤ (4297647950091/12500000000000 : ℝ)^3557
        have hw : |(2182418087/5000000000 : ℝ)|=(2182418087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545604497/1250000000 : ℝ)|^4581 ≤ (8595295398031/25000000000000 : ℝ)^3557
        have hw : |(545604497/1250000000 : ℝ)|=(545604497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_8 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949041857/10000000000 : ℝ)*x 0 + (1027094949/2000000000 : ℝ)*x 1 + (5419959013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949041857/10000000000 : ℝ)^4581 ≤ (6086151001713/50000000000000 : ℝ)^3557 := by
    have hnat : (1949041857 : ℕ)^4581*50000000000000^3557 ≤ 6086151001713^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949041857 10000000000 6086151001713 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027094949/2000000000 : ℝ)^4581 ≤ (21194914190659/50000000000000 : ℝ)^3557 := by
    have hnat : (1027094949 : ℕ)^4581*50000000000000^3557 ≤ 21194914190659^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027094949 2000000000 21194914190659 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419959013/10000000000 : ℝ)^4581 ≤ (5679733699493/12500000000000 : ℝ)^3557 := by
    have hnat : (5419959013 : ℕ)^4581*12500000000000^3557 ≤ 5679733699493^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419959013 10000000000 5679733699493 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949041857/10000000000 : ℝ), (1027094949/2000000000 : ℝ), (5419959013/10000000000 : ℝ)] ![(6086151001713/50000000000000 : ℝ), (21194914190659/50000000000000 : ℝ), (5679733699493/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949041857/10000000000 : ℝ)|^4581 ≤ (6086151001713/50000000000000 : ℝ)^3557
        have hw : |(-1949041857/10000000000 : ℝ)|=(1949041857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027094949/2000000000 : ℝ)|^4581 ≤ (21194914190659/50000000000000 : ℝ)^3557
        have hw : |(1027094949/2000000000 : ℝ)|=(1027094949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419959013/10000000000 : ℝ)|^4581 ≤ (5679733699493/12500000000000 : ℝ)^3557
        have hw : |(5419959013/10000000000 : ℝ)|=(5419959013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_9 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525691083/1000000000 : ℝ)*x 0 + (-1785993839/10000000000 : ℝ)*x 1 + (5419959117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525691083/1000000000 : ℝ)^4581 ≤ (21842567765729/50000000000000 : ℝ)^3557 := by
    have hnat : (525691083 : ℕ)^4581*50000000000000^3557 ≤ 21842567765729^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525691083 1000000000 21842567765729 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1785993839/10000000000 : ℝ)^4581 ≤ (5438496867049/50000000000000 : ℝ)^3557 := by
    have hnat : (1785993839 : ℕ)^4581*50000000000000^3557 ≤ 5438496867049^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785993839 10000000000 5438496867049 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419959117/10000000000 : ℝ)^4581 ≤ (2271893535941/5000000000000 : ℝ)^3557 := by
    have hnat : (5419959117 : ℕ)^4581*5000000000000^3557 ≤ 2271893535941^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419959117 10000000000 2271893535941 5000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525691083/1000000000 : ℝ), (-1785993839/10000000000 : ℝ), (5419959117/10000000000 : ℝ)] ![(21842567765729/50000000000000 : ℝ), (5438496867049/50000000000000 : ℝ), (2271893535941/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525691083/1000000000 : ℝ)|^4581 ≤ (21842567765729/50000000000000 : ℝ)^3557
        have hw : |(525691083/1000000000 : ℝ)|=(525691083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1785993839/10000000000 : ℝ)|^4581 ≤ (5438496867049/50000000000000 : ℝ)^3557
        have hw : |(-1785993839/10000000000 : ℝ)|=(1785993839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419959117/10000000000 : ℝ)|^4581 ≤ (2271893535941/5000000000000 : ℝ)^3557
        have hw : |(5419959117/10000000000 : ℝ)|=(5419959117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_10 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105138221/200000000 : ℝ)*x 0 + (2709979421/5000000000 : ℝ)*x 1 + (-892996959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105138221/200000000 : ℝ)^4581 ≤ (43685137885977/100000000000000 : ℝ)^3557 := by
    have hnat : (105138221 : ℕ)^4581*100000000000000^3557 ≤ 43685137885977^3557*200000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105138221 200000000 43685137885977 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709979421/5000000000 : ℝ)^4581 ≤ (22718933874839/50000000000000 : ℝ)^3557 := by
    have hnat : (2709979421 : ℕ)^4581*50000000000000^3557 ≤ 22718933874839^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709979421 5000000000 22718933874839 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (892996959/5000000000 : ℝ)^4581 ≤ (169953036777/1562500000000 : ℝ)^3557 := by
    have hnat : (892996959 : ℕ)^4581*1562500000000^3557 ≤ 169953036777^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892996959 5000000000 169953036777 1562500000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105138221/200000000 : ℝ), (2709979421/5000000000 : ℝ), (-892996959/5000000000 : ℝ)] ![(43685137885977/100000000000000 : ℝ), (22718933874839/50000000000000 : ℝ), (169953036777/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105138221/200000000 : ℝ)|^4581 ≤ (43685137885977/100000000000000 : ℝ)^3557
        have hw : |(105138221/200000000 : ℝ)|=(105138221/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709979421/5000000000 : ℝ)|^4581 ≤ (22718933874839/50000000000000 : ℝ)^3557
        have hw : |(2709979421/5000000000 : ℝ)|=(2709979421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-892996959/5000000000 : ℝ)|^4581 ≤ (169953036777/1562500000000 : ℝ)^3557
        have hw : |(-892996959/5000000000 : ℝ)|=(892996959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_11 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (140935401/312500000 : ℝ)*x 0 + (4135243671/10000000000 : ℝ)*x 1 + (2067621873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140935401/312500000 : ℝ)^4581 ≤ (89650250919/250000000000 : ℝ)^3557 := by
    have hnat : (140935401 : ℕ)^4581*250000000000^3557 ≤ 89650250919^3557*312500000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140935401 312500000 89650250919 250000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4135243671/10000000000 : ℝ)^4581 ≤ (32069949437159/100000000000000 : ℝ)^3557 := by
    have hnat : (4135243671 : ℕ)^4581*100000000000000^3557 ≤ 32069949437159^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135243671 10000000000 32069949437159 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067621873/5000000000 : ℝ)^4581 ≤ (32069950186251/100000000000000 : ℝ)^3557 := by
    have hnat : (2067621873 : ℕ)^4581*100000000000000^3557 ≤ 32069950186251^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067621873 5000000000 32069950186251 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140935401/312500000 : ℝ), (4135243671/10000000000 : ℝ), (2067621873/5000000000 : ℝ)] ![(89650250919/250000000000 : ℝ), (32069949437159/100000000000000 : ℝ), (32069950186251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140935401/312500000 : ℝ)|^4581 ≤ (89650250919/250000000000 : ℝ)^3557
        have hw : |(140935401/312500000 : ℝ)|=(140935401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4135243671/10000000000 : ℝ)|^4581 ≤ (32069949437159/100000000000000 : ℝ)^3557
        have hw : |(4135243671/10000000000 : ℝ)|=(4135243671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2067621873/5000000000 : ℝ)|^4581 ≤ (32069950186251/100000000000000 : ℝ)^3557
        have hw : |(2067621873/5000000000 : ℝ)|=(2067621873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_12 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-852673963/5000000000 : ℝ)*x 0 + (344074303/625000000 : ℝ)*x 1 + (5229428211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852673963/5000000000 : ℝ)^4581 ≤ (1024861035761/10000000000000 : ℝ)^3557 := by
    have hnat : (852673963 : ℕ)^4581*10000000000000^3557 ≤ 1024861035761^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852673963 5000000000 1024861035761 10000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344074303/625000000 : ℝ)^4581 ≤ (46360161324183/100000000000000 : ℝ)^3557 := by
    have hnat : (344074303 : ℕ)^4581*100000000000000^3557 ≤ 46360161324183^3557*625000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344074303 625000000 46360161324183 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229428211/10000000000 : ℝ)^4581 ≤ (43391228295123/100000000000000 : ℝ)^3557 := by
    have hnat : (5229428211 : ℕ)^4581*100000000000000^3557 ≤ 43391228295123^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229428211 10000000000 43391228295123 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-852673963/5000000000 : ℝ), (344074303/625000000 : ℝ), (5229428211/10000000000 : ℝ)] ![(1024861035761/10000000000000 : ℝ), (46360161324183/100000000000000 : ℝ), (43391228295123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-852673963/5000000000 : ℝ)|^4581 ≤ (1024861035761/10000000000000 : ℝ)^3557
        have hw : |(-852673963/5000000000 : ℝ)|=(852673963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344074303/625000000 : ℝ)|^4581 ≤ (46360161324183/100000000000000 : ℝ)^3557
        have hw : |(344074303/625000000 : ℝ)|=(344074303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229428211/10000000000 : ℝ)|^4581 ≤ (43391228295123/100000000000000 : ℝ)^3557
        have hw : |(5229428211/10000000000 : ℝ)|=(5229428211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_13 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694632169/5000000000 : ℝ)*x 0 + (-1865183927/10000000000 : ℝ)*x 1 + (1045885651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694632169/5000000000 : ℝ)^4581 ≤ (5638341663621/12500000000000 : ℝ)^3557 := by
    have hnat : (2694632169 : ℕ)^4581*12500000000000^3557 ≤ 5638341663621^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694632169 5000000000 5638341663621 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1865183927/10000000000 : ℝ)^4581 ≤ (5751018953483/50000000000000 : ℝ)^3557 := by
    have hnat : (1865183927 : ℕ)^4581*50000000000000^3557 ≤ 5751018953483^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865183927 10000000000 5751018953483 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045885651/2000000000 : ℝ)^4581 ≤ (43391228765317/100000000000000 : ℝ)^3557 := by
    have hnat : (1045885651 : ℕ)^4581*100000000000000^3557 ≤ 43391228765317^3557*2000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045885651 2000000000 43391228765317 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694632169/5000000000 : ℝ), (-1865183927/10000000000 : ℝ), (1045885651/2000000000 : ℝ)] ![(5638341663621/12500000000000 : ℝ), (5751018953483/50000000000000 : ℝ), (43391228765317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694632169/5000000000 : ℝ)|^4581 ≤ (5638341663621/12500000000000 : ℝ)^3557
        have hw : |(2694632169/5000000000 : ℝ)|=(2694632169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1865183927/10000000000 : ℝ)|^4581 ≤ (5751018953483/50000000000000 : ℝ)^3557
        have hw : |(-1865183927/10000000000 : ℝ)|=(1865183927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045885651/2000000000 : ℝ)|^4581 ≤ (43391228765317/100000000000000 : ℝ)^3557
        have hw : |(1045885651/2000000000 : ℝ)|=(1045885651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_14 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2694632169/5000000000 : ℝ)*x 0 + (2614714149/5000000000 : ℝ)*x 1 + (-186518387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2694632169/5000000000 : ℝ)^4581 ≤ (5638341663621/12500000000000 : ℝ)^3557 := by
    have hnat : (2694632169 : ℕ)^4581*12500000000000^3557 ≤ 5638341663621^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694632169 5000000000 5638341663621 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614714149/5000000000 : ℝ)^4581 ≤ (5423903653103/12500000000000 : ℝ)^3557 := by
    have hnat : (2614714149 : ℕ)^4581*12500000000000^3557 ≤ 5423903653103^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614714149 5000000000 5423903653103 12500000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186518387/1000000000 : ℝ)^4581 ≤ (179719335223/1562500000000 : ℝ)^3557 := by
    have hnat : (186518387 : ℕ)^4581*1562500000000^3557 ≤ 179719335223^3557*1000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186518387 1000000000 179719335223 1562500000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2694632169/5000000000 : ℝ), (2614714149/5000000000 : ℝ), (-186518387/1000000000 : ℝ)] ![(5638341663621/12500000000000 : ℝ), (5423903653103/12500000000000 : ℝ), (179719335223/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2694632169/5000000000 : ℝ)|^4581 ≤ (5638341663621/12500000000000 : ℝ)^3557
        have hw : |(2694632169/5000000000 : ℝ)|=(2694632169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614714149/5000000000 : ℝ)|^4581 ≤ (5423903653103/12500000000000 : ℝ)^3557
        have hw : |(2614714149/5000000000 : ℝ)|=(2614714149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-186518387/1000000000 : ℝ)|^4581 ≤ (179719335223/1562500000000 : ℝ)^3557
        have hw : |(-186518387/1000000000 : ℝ)|=(186518387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1542_box_15 (p : ℝ) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1002854877/2500000000 : ℝ)*x 0 + (4384492099/10000000000 : ℝ)*x 1 + (2192246053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1002854877/2500000000 : ℝ)^4581 ≤ (15419288328641/50000000000000 : ℝ)^3557 := by
    have hnat : (1002854877 : ℕ)^4581*50000000000000^3557 ≤ 15419288328641^3557*2500000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002854877 2500000000 15419288328641 50000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384492099/10000000000 : ℝ)^4581 ≤ (34580711627957/100000000000000 : ℝ)^3557 := by
    have hnat : (4384492099 : ℕ)^4581*100000000000000^3557 ≤ 34580711627957^3557*10000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384492099 10000000000 34580711627957 100000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192246053/5000000000 : ℝ)^4581 ≤ (1729035584953/5000000000000 : ℝ)^3557 := by
    have hnat : (2192246053 : ℕ)^4581*5000000000000^3557 ≤ 1729035584953^3557*5000000000^4581 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192246053 5000000000 1729035584953 5000000000000 4581 3557 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4581/1024 : ℝ)) 4581 3557 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1002854877/2500000000 : ℝ), (4384492099/10000000000 : ℝ), (2192246053/5000000000 : ℝ)] ![(15419288328641/50000000000000 : ℝ), (34580711627957/100000000000000 : ℝ), (1729035584953/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1002854877/2500000000 : ℝ)|^4581 ≤ (15419288328641/50000000000000 : ℝ)^3557
        have hw : |(1002854877/2500000000 : ℝ)|=(1002854877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384492099/10000000000 : ℝ)|^4581 ≤ (34580711627957/100000000000000 : ℝ)^3557
        have hw : |(4384492099/10000000000 : ℝ)|=(4384492099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2192246053/5000000000 : ℝ)|^4581 ≤ (1729035584953/5000000000000 : ℝ)^3557
        have hw : |(2192246053/5000000000 : ℝ)|=(2192246053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1542_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31891/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58769/100000 : ℝ) ∧ (20159/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5387/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11027/100000 : ℝ) ^ (4579/1024 : ℝ) ≤ (2613040231137213/50000000000000000000 : ℝ) := by
    have hpowers : (11027/100000 : ℝ)^4579 ≤ (2613040231137213/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11027 : ℕ)^4579*50000000000000000000^1024 ≤ 2613040231137213^1024*100000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11027 100000 2613040231137213 50000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11027/100000 : ℝ)) (X := (2613040231137213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4579/1024 : ℝ) ≤ (5963241804510387/25000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4579 ≤ (5963241804510387/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4579*25000000000000000000^1024 ≤ 5963241804510387^1024*20000^4579 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 5963241804510387 25000000000000000000 4579 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (5963241804510387/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002613040231137213/25000000000000000000 : ℝ) ≤ (250005843294689/250000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (25002613040231137213/25000000000000000000 : ℝ)^1024 ≤ (250005843294689/250000000000000 : ℝ)^4579 := by
      have hnat : (25002613040231137213 : ℕ)^1024*250000000000000^4579 ≤ 250005843294689^4579*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002613040231137213 25000000000000000000 250005843294689 250000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250005843294689/250000000000000 : ℝ)) (X := (25002613040231137213/25000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014539523840157987/50000000000000000000 : ℝ) ≤ (10000650220226363/10000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (50014539523840157987/50000000000000000000 : ℝ)^1024 ≤ (10000650220226363/10000000000000000 : ℝ)^4579 := by
      have hnat : (50014539523840157987 : ℕ)^1024*10000000000000000^4579 ≤ 10000650220226363^4579*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014539523840157987 50000000000000000000 10000650220226363 10000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650220226363/10000000000000000 : ℝ)) (X := (50014539523840157987/50000000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505963241804510387/12500000000000000000 : ℝ) ≤ (5000533354332583/5000000000000000 : ℝ) ^ (4579/1024 : ℝ) := by
    have hpowers : (12505963241804510387/12500000000000000000 : ℝ)^1024 ≤ (5000533354332583/5000000000000000 : ℝ)^4579 := by
      have hnat : (12505963241804510387 : ℕ)^1024*5000000000000000^4579 ≤ 5000533354332583^4579*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505963241804510387 12500000000000000000 5000533354332583 5000000000000000 1024 4579 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000533354332583/5000000000000000 : ℝ)) (X := (12505963241804510387/12500000000000000000 : ℝ)) (by norm_num) 4579 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2613040231137213/50000000000000000000 : ℝ) ≤ ((7428642790046596853/7430000000000000000 : ℝ)+2*(138829479601/148600000000000 : ℝ)*(11027/100000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (7428642790046596853/7430000000000000000 : ℝ)+2*(138829479601/148600000000000 : ℝ)*(11027/100000 : ℝ)=(250005843294689/250000000000000 : ℝ) by norm_num, show 1+2*(2613040231137213/50000000000000000000 : ℝ)=(25002613040231137213/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5963241804510387/25000000000000000000 : ℝ)+(2613040231137213/50000000000000000000 : ℝ) ≤ ((7428642790046596853/7430000000000000000 : ℝ)+(138829479601/148600000000000 : ℝ)*((3097/20000 : ℝ)+(11027/100000 : ℝ)))^(4579/1024 : ℝ) := by
    rw [show (7428642790046596853/7430000000000000000 : ℝ)+(138829479601/148600000000000 : ℝ)*((3097/20000 : ℝ)+(11027/100000 : ℝ))=(10000650220226363/10000000000000000 : ℝ) by norm_num, show 1+(5963241804510387/25000000000000000000 : ℝ)+(2613040231137213/50000000000000000000 : ℝ)=(50014539523840157987/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5963241804510387/25000000000000000000 : ℝ) ≤ ((7428642790046596853/7430000000000000000 : ℝ)+2*(138829479601/148600000000000 : ℝ)*(3097/20000 : ℝ))^(4579/1024 : ℝ) := by
    rw [show (7428642790046596853/7430000000000000000 : ℝ)+2*(138829479601/148600000000000 : ℝ)*(3097/20000 : ℝ)=(5000533354332583/5000000000000000 : ℝ) by norm_num, show 1+2*(5963241804510387/25000000000000000000 : ℝ)=(12505963241804510387/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7428642790046596853/7430000000000000000 : ℝ)*(X 1 0+X 2 0)+(138829479601/148600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (11027/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7428642790046596853/7430000000000000000 : ℝ)) (alpha := (138829479601/148600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7428642790046596853/7430000000000000000 : ℝ)*(X 0 1+X 2 1)+(138829479601/148600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (11027/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7428642790046596853/7430000000000000000 : ℝ)) (alpha := (138829479601/148600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7428642790046596853/7430000000000000000 : ℝ)*(X 0 2+X 1 2)+(138829479601/148600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4579/1024 : ℝ)) (lo := (11027/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (7428642790046596853/7430000000000000000 : ℝ)) (alpha := (138829479601/148600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-808087801/5000000000 : ℝ)*X 0 0+(5399597943/10000000000 : ℝ)*X 0 1+(269979887/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635529497/5000000000 : ℝ)*X 1 0+(-179468821/1000000000 : ℝ)*X 1 1+(5399597903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271059177/10000000000 : ℝ)*X 2 0+(269979893/500000000 : ℝ)*X 2 1+(-1794688019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4457776867/10000000000 : ℝ)*X 0 0+(4161911589/10000000000 : ℝ)*X 0 1+(4161911817/10000000000 : ℝ)*X 0 2+(4457776867/10000000000 : ℝ)*X 1 0+(4161911589/10000000000 : ℝ)*X 1 1+(4161911817/10000000000 : ℝ)*X 1 2+(4457776867/10000000000 : ℝ)*X 2 0+(4161911589/10000000000 : ℝ)*X 2 1+(4161911817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2038419843/10000000000 : ℝ)*X 0 0+(262223613/500000000 : ℝ)*X 0 1+(1048894493/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5378812923/10000000000 : ℝ)*X 1 0+(-1859111039/10000000000 : ℝ)*X 1 1+(524447273/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378814139/10000000000 : ℝ)*X 2 0+(5244472243/10000000000 : ℝ)*X 2 1+(-1859110043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((810333389/2000000000 : ℝ)*X 0 0+(2182418087/5000000000 : ℝ)*X 0 1+(545604497/1250000000 : ℝ)*X 0 2+(810333389/2000000000 : ℝ)*X 1 0+(2182418087/5000000000 : ℝ)*X 1 1+(545604497/1250000000 : ℝ)*X 1 2+(810333389/2000000000 : ℝ)*X 2 0+(2182418087/5000000000 : ℝ)*X 2 1+(545604497/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1949041857/10000000000 : ℝ)*X 0 0+(1027094949/2000000000 : ℝ)*X 0 1+(5419959013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((525691083/1000000000 : ℝ)*X 1 0+(-1785993839/10000000000 : ℝ)*X 1 1+(5419959117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((105138221/200000000 : ℝ)*X 2 0+(2709979421/5000000000 : ℝ)*X 2 1+(-892996959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((140935401/312500000 : ℝ)*X 0 0+(4135243671/10000000000 : ℝ)*X 0 1+(2067621873/5000000000 : ℝ)*X 0 2+(140935401/312500000 : ℝ)*X 1 0+(4135243671/10000000000 : ℝ)*X 1 1+(2067621873/5000000000 : ℝ)*X 1 2+(140935401/312500000 : ℝ)*X 2 0+(4135243671/10000000000 : ℝ)*X 2 1+(2067621873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-852673963/5000000000 : ℝ)*X 0 0+(344074303/625000000 : ℝ)*X 0 1+(5229428211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2694632169/5000000000 : ℝ)*X 1 0+(-1865183927/10000000000 : ℝ)*X 1 1+(1045885651/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2694632169/5000000000 : ℝ)*X 2 0+(2614714149/5000000000 : ℝ)*X 2 1+(-186518387/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1002854877/2500000000 : ℝ)*X 0 0+(4384492099/10000000000 : ℝ)*X 0 1+(2192246053/5000000000 : ℝ)*X 0 2+(1002854877/2500000000 : ℝ)*X 1 0+(4384492099/10000000000 : ℝ)*X 1 1+(2192246053/5000000000 : ℝ)*X 1 2+(1002854877/2500000000 : ℝ)*X 2 0+(4384492099/10000000000 : ℝ)*X 2 1+(2192246053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1542_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31891/50000 : ℝ) ≤ (-29617716200526355419074238387573/46437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10442947/10000000000000 : ℝ)*(upper0) + (421320821/100000000000000 : ℝ)*(lower2) + (166046347/100000000000000 : ℝ)*(upper5) + (283417214348247/12500000000000 : ℝ)*(major0) + (283417214348247/12500000000000 : ℝ)*(major1) + (283417214348247/12500000000000 : ℝ)*(major2) + (2504094601/100000000000000 : ℝ)*(sp1) + (6032868409/100000000000000 : ℝ)*(sp3) + (398531338431657/12500000000000 : ℝ)*(sp4) + (797063807863813/25000000000000 : ℝ)*(sp5) + (797062843947041/25000000000000 : ℝ)*(sp6) + (341917893520907/25000000000000 : ℝ)*(sp7) + (7028096597/100000000000000 : ℝ)*(sp8) + (794970211/12500000000000 : ℝ)*(sp14) + (1367677606952037/100000000000000 : ℝ)*(f.failure) + (797064433887463/25000000000000 : ℝ)*(f.sum) + (8371799426401/1857500000000000000000000000 : ℝ)*base66 + (586205919476866691/92875000000000000000000000000000 : ℝ)*base67 + (67447623187133309/92875000000000000000000000000000 : ℝ)*base70 + (112335891193758309/92875000000000000000000000000000 : ℝ)*base72 + (48865786613737/3715000000000000000000000000 : ℝ)*base74 + (184139155254616691/92875000000000000000000000000000 : ℝ)*base75 + (61579943799991691/92875000000000000000000000000000 : ℝ)*base77 + (358034561927741691/92875000000000000000000000000000 : ℝ)*base79 + (10816817294547/3715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (237519/1000000000000000000000 : ℝ)*base90 + (237519/1000000000000000000000 : ℝ)*base92 + (237519/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58769/100000 : ℝ) ≤ (109168628777022276697259118867549/185750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76631057/100000000000000 : ℝ)*(lower1) + (43708383/100000000000000 : ℝ)*(lower2) + (11300137/25000000000000 : ℝ)*(upper4) + (1172822613904611/50000000000000 : ℝ)*(major0) + (1172822613904611/50000000000000 : ℝ)*(major1) + (1172822613904611/50000000000000 : ℝ)*(major2) + (1628392438078721/50000000000000 : ℝ)*(sp0) + (325677331228557/10000000000000 : ℝ)*(sp1) + (3256785490665799/100000000000000 : ℝ)*(sp2) + (70745623229011/5000000000000 : ℝ)*(sp3) + (123864403/12500000000000 : ℝ)*(sp6) + (18152259/2000000000000 : ℝ)*(sp7) + (802711791/50000000000000 : ℝ)*(sp8) + (13169295453/100000000000000 : ℝ)*(sp9) + (1414913372193171/100000000000000 : ℝ)*(f.failure) + (3256786481581023/100000000000000 : ℝ)*(f.sum) + (54081769202331/3715000000000000000000000000 : ℝ)*base65 + (4581282728108660817/371500000000000000000000000000000 : ℝ)*base68 + (5472909962773660817/371500000000000000000000000000000 : ℝ)*base70 + (3734343632135339183/371500000000000000000000000000000 : ℝ)*base71 + (1660699866927/464375000000000000000000000 : ℝ)*base73 + (4065715910421160817/371500000000000000000000000000000 : ℝ)*base76 + (3633976595721839183/371500000000000000000000000000000 : ℝ)*base77 + (1510441131992660817/371500000000000000000000000000000 : ℝ)*base80 + (3349460205797/1857500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7349223/1000000000000000000000 : ℝ)*base89 + (7349223/1000000000000000000000 : ℝ)*base91 + (7349223/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20159/25000 : ℝ) ≤ (299570316220036215927469113846219/371500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29961709/100000000000000 : ℝ)*(upper0) + (9862753/100000000000000 : ℝ)*(upper1) + (4526537/25000000000000 : ℝ)*(upper4) + (2535822540238741/100000000000000 : ℝ)*(major0) + (2535822540238741/100000000000000 : ℝ)*(major1) + (2535822540238741/100000000000000 : ℝ)*(major2) + (10465463797/25000000000000 : ℝ)*(sp1) + (3550199277/100000000000000 : ℝ)*(sp3) + (983761991/100000000000000 : ℝ)*(sp4) + (3515133656677053/100000000000000 : ℝ)*(sp8) + (878773477434289/25000000000000 : ℝ)*(sp9) + (3515135771592343/100000000000000 : ℝ)*(sp10) + (305925282446547/20000000000000 : ℝ)*(sp11) + (1131153299/100000000000000 : ℝ)*(sp12) + (382407490608003/25000000000000 : ℝ)*(f.failure) + (3515135771592343/100000000000000 : ℝ)*(f.sum) + (8262767902189/7430000000000000000000000000 : ℝ)*base66 + (435889644688667927/743000000000000000000000000000000 : ℝ)*base68 + (2155421363199667927/743000000000000000000000000000000 : ℝ)*base70 + (5441513333716667927/743000000000000000000000000000000 : ℝ)*base72 + (47503111935521/7430000000000000000000000000 : ℝ)*base73 + (5753991348488667927/743000000000000000000000000000000 : ℝ)*base76 + (540134626369332073/743000000000000000000000000000000 : ℝ)*base77 + (2324547711324332073/743000000000000000000000000000000 : ℝ)*base79 + (3325552156991/7430000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (861961/250000000000000000000 : ℝ)*base90 + (861961/250000000000000000000 : ℝ)*base92 + (861961/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-5387/6250 : ℝ) ≤ (-800489168460080509948743561/928750000000000000000000000 : ℝ) := by norm_num
    linear_combination (10203551/25000000000000 : ℝ)*(lower0) + (51542301/100000000000000 : ℝ)*(lower1) + (18985557/100000000000000 : ℝ)*(lower2) + (643905038261791/25000000000000 : ℝ)*(major0) + (643905038261791/25000000000000 : ℝ)*(major1) + (643905038261791/25000000000000 : ℝ)*(major2) + (731796107/100000000000000 : ℝ)*(sp0) + (7982892549/25000000000000 : ℝ)*(sp5) + (6883817621/50000000000000 : ℝ)*(sp6) + (4456471091/100000000000000 : ℝ)*(sp7) + (906583333301317/25000000000000 : ℝ)*(sp12) + (1813151066715589/50000000000000 : ℝ)*(sp13) + (906580074341533/25000000000000 : ℝ)*(sp14) + (388407942059099/25000000000000 : ℝ)*(sp15) + (1553636224707487/100000000000000 : ℝ)*(f.failure) + (1813167032500687/50000000000000 : ℝ)*(f.sum) + (7568688332367/3715000000000000000000000000 : ℝ)*base65 + (885682022386956277/185750000000000000000000000000000 : ℝ)*base68 + (845269011019706277/185750000000000000000000000000000 : ℝ)*base70 + (1244455691919043723/185750000000000000000000000000000 : ℝ)*base71 + (9813051427819/1857500000000000000000000000 : ℝ)*base74 + (212971819903793723/185750000000000000000000000000000 : ℝ)*base75 + (2418077282612543723/185750000000000000000000000000000 : ℝ)*base77 + (964464537114706277/185750000000000000000000000000000 : ℝ)*base80 + (63240821661/29023437500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (683331/1000000000000000000000 : ℝ)*base89 + (683331/1000000000000000000000 : ℝ)*base91 + (683331/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1542_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31891/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58769/100000 : ℝ) else (20159/25000 : ℝ) ≤ X j i ∧ X j i ≤ (5387/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1542_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1542_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31891/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58769/100000 : ℝ) else (20159/25000 : ℝ) ≤ X j i ∧ X j i ≤ (5387/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1542_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1542_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4579/1024 : ℝ) ≤ p) (hpb : p ≤ (4581/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16578013/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31891/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58769/100000 : ℝ) else (20159/25000 : ℝ) ≤ X j i ∧ X j i ≤ (5387/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1542_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

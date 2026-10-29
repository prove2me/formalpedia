-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1331_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:57.692996+00:00
-- url     : https://prove2.me/submissions/e3b0382b-ebf9-400b-8bbd-6848868f2449

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
theorem support_rectangle_w1331_s3_0 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025818333/5000000000 : ℝ)*x 0 + (542859761/1000000000 : ℝ)*x 1 + (2615086189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025818333/5000000000 : ℝ)^4291 ≤ (195122355109/1562500000000 : ℝ)^3267 := by
    have hnat : (1025818333 : ℕ)^4291*1562500000000^3267 ≤ 195122355109^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025818333 5000000000 195122355109 1562500000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542859761/1000000000 : ℝ)^4291 ≤ (44825881343201/100000000000000 : ℝ)^3267 := by
    have hnat : (542859761 : ℕ)^4291*100000000000000^3267 ≤ 44825881343201^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542859761 1000000000 44825881343201 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615086189/5000000000 : ℝ)^4291 ≤ (2134314395511/5000000000000 : ℝ)^3267 := by
    have hnat : (2615086189 : ℕ)^4291*5000000000000^3267 ≤ 2134314395511^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615086189 5000000000 2134314395511 5000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025818333/5000000000 : ℝ), (542859761/1000000000 : ℝ), (2615086189/5000000000 : ℝ)] ![(195122355109/1562500000000 : ℝ), (44825881343201/100000000000000 : ℝ), (2134314395511/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025818333/5000000000 : ℝ)|^4291 ≤ (195122355109/1562500000000 : ℝ)^3267
        have hw : |(-1025818333/5000000000 : ℝ)|=(1025818333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542859761/1000000000 : ℝ)|^4291 ≤ (44825881343201/100000000000000 : ℝ)^3267
        have hw : |(542859761/1000000000 : ℝ)|=(542859761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615086189/5000000000 : ℝ)|^4291 ≤ (2134314395511/5000000000000 : ℝ)^3267
        have hw : |(2615086189/5000000000 : ℝ)|=(2615086189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_1 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070617123/2000000000 : ℝ)*x 0 + (-1076537703/5000000000 : ℝ)*x 1 + (2615086253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070617123/2000000000 : ℝ)^4291 ≤ (44008705174539/100000000000000 : ℝ)^3267 := by
    have hnat : (1070617123 : ℕ)^4291*100000000000000^3267 ≤ 44008705174539^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070617123 2000000000 44008705174539 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076537703/5000000000 : ℝ)^4291 ≤ (6652502767101/50000000000000 : ℝ)^3267 := by
    have hnat : (1076537703 : ℕ)^4291*50000000000000^3267 ≤ 6652502767101^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076537703 5000000000 6652502767101 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615086253/5000000000 : ℝ)^4291 ≤ (21343144641169/50000000000000 : ℝ)^3267 := by
    have hnat : (2615086253 : ℕ)^4291*50000000000000^3267 ≤ 21343144641169^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615086253 5000000000 21343144641169 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070617123/2000000000 : ℝ), (-1076537703/5000000000 : ℝ), (2615086253/5000000000 : ℝ)] ![(44008705174539/100000000000000 : ℝ), (6652502767101/50000000000000 : ℝ), (21343144641169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070617123/2000000000 : ℝ)|^4291 ≤ (44008705174539/100000000000000 : ℝ)^3267
        have hw : |(1070617123/2000000000 : ℝ)|=(1070617123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076537703/5000000000 : ℝ)|^4291 ≤ (6652502767101/50000000000000 : ℝ)^3267
        have hw : |(-1076537703/5000000000 : ℝ)|=(1076537703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615086253/5000000000 : ℝ)|^4291 ≤ (21343144641169/50000000000000 : ℝ)^3267
        have hw : |(2615086253/5000000000 : ℝ)|=(2615086253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_2 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669135671/1250000000 : ℝ)*x 0 + (2615086401/5000000000 : ℝ)*x 1 + (-2153075343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669135671/1250000000 : ℝ)^4291 ≤ (4400870250743/10000000000000 : ℝ)^3267 := by
    have hnat : (669135671 : ℕ)^4291*10000000000000^3267 ≤ 4400870250743^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669135671 1250000000 4400870250743 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615086401/5000000000 : ℝ)^4291 ≤ (42686292455363/100000000000000 : ℝ)^3267 := by
    have hnat : (2615086401 : ℕ)^4291*100000000000000^3267 ≤ 42686292455363^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615086401 5000000000 42686292455363 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153075343/10000000000 : ℝ)^4291 ≤ (6652502511433/50000000000000 : ℝ)^3267 := by
    have hnat : (2153075343 : ℕ)^4291*50000000000000^3267 ≤ 6652502511433^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153075343 10000000000 6652502511433 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669135671/1250000000 : ℝ), (2615086401/5000000000 : ℝ), (-2153075343/10000000000 : ℝ)] ![(4400870250743/10000000000000 : ℝ), (42686292455363/100000000000000 : ℝ), (6652502511433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669135671/1250000000 : ℝ)|^4291 ≤ (4400870250743/10000000000000 : ℝ)^3267
        have hw : |(669135671/1250000000 : ℝ)|=(669135671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615086401/5000000000 : ℝ)|^4291 ≤ (42686292455363/100000000000000 : ℝ)^3267
        have hw : |(2615086401/5000000000 : ℝ)|=(2615086401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153075343/10000000000 : ℝ)|^4291 ≤ (6652502511433/50000000000000 : ℝ)^3267
        have hw : |(-2153075343/10000000000 : ℝ)|=(2153075343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_3 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328370051/10000000000 : ℝ)*x 0 + (2063032951/5000000000 : ℝ)*x 1 + (4539962161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328370051/10000000000 : ℝ)^4291 ≤ (66583226703/200000000000 : ℝ)^3267 := by
    have hnat : (4328370051 : ℕ)^4291*200000000000^3267 ≤ 66583226703^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328370051 10000000000 66583226703 200000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063032951/5000000000 : ℝ)^4291 ≤ (6252602327949/20000000000000 : ℝ)^3267 := by
    have hnat : (2063032951 : ℕ)^4291*20000000000000^3267 ≤ 6252602327949^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063032951 5000000000 6252602327949 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4539962161/10000000000 : ℝ)^4291 ≤ (17722687496753/50000000000000 : ℝ)^3267 := by
    have hnat : (4539962161 : ℕ)^4291*50000000000000^3267 ≤ 17722687496753^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539962161 10000000000 17722687496753 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328370051/10000000000 : ℝ), (2063032951/5000000000 : ℝ), (4539962161/10000000000 : ℝ)] ![(66583226703/200000000000 : ℝ), (6252602327949/20000000000000 : ℝ), (17722687496753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328370051/10000000000 : ℝ)|^4291 ≤ (66583226703/200000000000 : ℝ)^3267
        have hw : |(4328370051/10000000000 : ℝ)|=(4328370051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063032951/5000000000 : ℝ)|^4291 ≤ (6252602327949/20000000000000 : ℝ)^3267
        have hw : |(2063032951/5000000000 : ℝ)|=(2063032951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4539962161/10000000000 : ℝ)|^4291 ≤ (17722687496753/50000000000000 : ℝ)^3267
        have hw : |(4539962161/10000000000 : ℝ)|=(4539962161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_4 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025828311/5000000000 : ℝ)*x 0 + (163468901/312500000 : ℝ)*x 1 + (84808751/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025828311/5000000000 : ℝ)^4291 ≤ (312199756679/2500000000000 : ℝ)^3267 := by
    have hnat : (1025828311 : ℕ)^4291*2500000000000^3267 ≤ 312199756679^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025828311 5000000000 312199756679 2500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163468901/312500000 : ℝ)^4291 ≤ (2668450735761/6250000000000 : ℝ)^3267 := by
    have hnat : (163468901 : ℕ)^4291*6250000000000^3267 ≤ 2668450735761^3267*312500000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163468901 312500000 2668450735761 6250000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84808751/156250000 : ℝ)^4291 ≤ (5602099742131/12500000000000 : ℝ)^3267 := by
    have hnat : (84808751 : ℕ)^4291*12500000000000^3267 ≤ 5602099742131^3267*156250000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84808751 156250000 5602099742131 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025828311/5000000000 : ℝ), (163468901/312500000 : ℝ), (84808751/156250000 : ℝ)] ![(312199756679/2500000000000 : ℝ), (2668450735761/6250000000000 : ℝ), (5602099742131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025828311/5000000000 : ℝ)|^4291 ≤ (312199756679/2500000000000 : ℝ)^3267
        have hw : |(-1025828311/5000000000 : ℝ)|=(1025828311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163468901/312500000 : ℝ)|^4291 ≤ (2668450735761/6250000000000 : ℝ)^3267
        have hw : |(163468901/312500000 : ℝ)|=(163468901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84808751/156250000 : ℝ)|^4291 ≤ (5602099742131/12500000000000 : ℝ)^3267
        have hw : |(84808751/156250000 : ℝ)|=(84808751/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_5 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325509777/2500000000 : ℝ)*x 0 + (-977744041/5000000000 : ℝ)*x 1 + (5427760261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325509777/2500000000 : ℝ)^4291 ≤ (10864582489851/25000000000000 : ℝ)^3267 := by
    have hnat : (1325509777 : ℕ)^4291*25000000000000^3267 ≤ 10864582489851^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325509777 2500000000 10864582489851 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977744041/5000000000 : ℝ)^4291 ≤ (5862434979571/50000000000000 : ℝ)^3267 := by
    have hnat : (977744041 : ℕ)^4291*50000000000000^3267 ≤ 5862434979571^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977744041 5000000000 5862434979571 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427760261/10000000000 : ℝ)^4291 ≤ (44816800073513/100000000000000 : ℝ)^3267 := by
    have hnat : (5427760261 : ℕ)^4291*100000000000000^3267 ≤ 44816800073513^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427760261 10000000000 44816800073513 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325509777/2500000000 : ℝ), (-977744041/5000000000 : ℝ), (5427760261/10000000000 : ℝ)] ![(10864582489851/25000000000000 : ℝ), (5862434979571/50000000000000 : ℝ), (44816800073513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325509777/2500000000 : ℝ)|^4291 ≤ (10864582489851/25000000000000 : ℝ)^3267
        have hw : |(1325509777/2500000000 : ℝ)|=(1325509777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977744041/5000000000 : ℝ)|^4291 ≤ (5862434979571/50000000000000 : ℝ)^3267
        have hw : |(-977744041/5000000000 : ℝ)|=(977744041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427760261/10000000000 : ℝ)|^4291 ≤ (44816800073513/100000000000000 : ℝ)^3267
        have hw : |(5427760261/10000000000 : ℝ)|=(5427760261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_6 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325510193/2500000000 : ℝ)*x 0 + (5427759097/10000000000 : ℝ)*x 1 + (-122217963/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325510193/2500000000 : ℝ)^4291 ≤ (8691669574683/20000000000000 : ℝ)^3267 := by
    have hnat : (1325510193 : ℕ)^4291*20000000000000^3267 ≤ 8691669574683^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325510193 2500000000 8691669574683 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427759097/10000000000 : ℝ)^4291 ≤ (44816787449933/100000000000000 : ℝ)^3267 := by
    have hnat : (5427759097 : ℕ)^4291*100000000000000^3267 ≤ 44816787449933^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427759097 10000000000 44816787449933 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122217963/625000000 : ℝ)^4291 ≤ (11724864651249/100000000000000 : ℝ)^3267 := by
    have hnat : (122217963 : ℕ)^4291*100000000000000^3267 ≤ 11724864651249^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122217963 625000000 11724864651249 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325510193/2500000000 : ℝ), (5427759097/10000000000 : ℝ), (-122217963/625000000 : ℝ)] ![(8691669574683/20000000000000 : ℝ), (44816787449933/100000000000000 : ℝ), (11724864651249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325510193/2500000000 : ℝ)|^4291 ≤ (8691669574683/20000000000000 : ℝ)^3267
        have hw : |(1325510193/2500000000 : ℝ)|=(1325510193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427759097/10000000000 : ℝ)|^4291 ≤ (44816787449933/100000000000000 : ℝ)^3267
        have hw : |(5427759097/10000000000 : ℝ)|=(5427759097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122217963/625000000 : ℝ)|^4291 ≤ (11724864651249/100000000000000 : ℝ)^3267
        have hw : |(-122217963/625000000 : ℝ)|=(122217963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s3_7 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17313649/40000000 : ℝ)*x 0 + (453822583/1000000000 : ℝ)*x 1 + (825562397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17313649/40000000 : ℝ)^4291 ≤ (6658407931739/20000000000000 : ℝ)^3267 := by
    have hnat : (17313649 : ℕ)^4291*20000000000000^3267 ≤ 6658407931739^3267*40000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17313649 40000000 6658407931739 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453822583/1000000000 : ℝ)^4291 ≤ (4428446345379/12500000000000 : ℝ)^3267 := by
    have hnat : (453822583 : ℕ)^4291*12500000000000^3267 ≤ 4428446345379^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453822583 1000000000 4428446345379 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825562397/2000000000 : ℝ)^4291 ≤ (7820097389151/25000000000000 : ℝ)^3267 := by
    have hnat : (825562397 : ℕ)^4291*25000000000000^3267 ≤ 7820097389151^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825562397 2000000000 7820097389151 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17313649/40000000 : ℝ), (453822583/1000000000 : ℝ), (825562397/2000000000 : ℝ)] ![(6658407931739/20000000000000 : ℝ), (4428446345379/12500000000000 : ℝ), (7820097389151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17313649/40000000 : ℝ)|^4291 ≤ (6658407931739/20000000000000 : ℝ)^3267
        have hw : |(17313649/40000000 : ℝ)|=(17313649/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453822583/1000000000 : ℝ)|^4291 ≤ (4428446345379/12500000000000 : ℝ)^3267
        have hw : |(453822583/1000000000 : ℝ)|=(453822583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825562397/2000000000 : ℝ)|^4291 ≤ (7820097389151/25000000000000 : ℝ)^3267
        have hw : |(825562397/2000000000 : ℝ)|=(825562397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1331_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4037/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5411/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (751/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4037/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4037/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9779/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4037/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4037/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9779/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4037/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4037/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9779/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9779/100000 : ℝ) ^ (2145/512 : ℝ) ≤ (1177377976041753/20000000000000000000 : ℝ) := by
    have hpowers : (9779/100000 : ℝ)^2145 ≤ (1177377976041753/20000000000000000000 : ℝ)^512 := by
      have hnat : (9779 : ℕ)^2145*20000000000000000000^512 ≤ 1177377976041753^512*100000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9779 100000 1177377976041753 20000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9779/100000 : ℝ)) (X := (1177377976041753/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4037/25000 : ℝ) ^ (2145/512 : ℝ) ≤ (48133848173467629/100000000000000000000 : ℝ) := by
    have hpowers : (4037/25000 : ℝ)^2145 ≤ (48133848173467629/100000000000000000000 : ℝ)^512 := by
      have hnat : (4037 : ℕ)^2145*100000000000000000000^512 ≤ 48133848173467629^512*25000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4037 25000 48133848173467629 100000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4037/25000 : ℝ)) (X := (48133848173467629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001177377976041753/10000000000000000000 : ℝ) ≤ (10000281021216319/10000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (10001177377976041753/10000000000000000000 : ℝ)^512 ≤ (10000281021216319/10000000000000000 : ℝ)^2145 := by
      have hnat : (10001177377976041753 : ℕ)^512*10000000000000000^2145 ≤ 10000281021216319^2145*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001177377976041753 10000000000000000000 10000281021216319 10000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281021216319/10000000000000000 : ℝ)) (X := (10001177377976041753/10000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027010369026838197/50000000000000000000 : ℝ) ≤ (625080573811791/625000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50027010369026838197/50000000000000000000 : ℝ)^512 ≤ (625080573811791/625000000000000 : ℝ)^2145 := by
      have hnat : (50027010369026838197 : ℕ)^512*625000000000000^2145 ≤ 625080573811791^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027010369026838197 50000000000000000000 625080573811791 625000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625080573811791/625000000000000 : ℝ)) (X := (50027010369026838197/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048133848173467629/50000000000000000000 : ℝ) ≤ (10002297340760993/10000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50048133848173467629/50000000000000000000 : ℝ)^512 ≤ (10002297340760993/10000000000000000 : ℝ)^2145 := by
      have hnat : (50048133848173467629 : ℕ)^512*10000000000000000^2145 ≤ 10002297340760993^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048133848173467629 50000000000000000000 10002297340760993 10000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002297340760993/10000000000000000 : ℝ)) (X := (50048133848173467629/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1177377976041753/20000000000000000000 : ℝ) ≤ ((1157674040641806703/1158000000000000000 : ℝ)+2*(1008159772337/636900000000000 : ℝ)*(9779/100000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (1157674040641806703/1158000000000000000 : ℝ)+2*(1008159772337/636900000000000 : ℝ)*(9779/100000 : ℝ)=(10000281021216319/10000000000000000 : ℝ) by norm_num, show 1+2*(1177377976041753/20000000000000000000 : ℝ)=(10001177377976041753/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48133848173467629/100000000000000000000 : ℝ)+(1177377976041753/20000000000000000000 : ℝ) ≤ ((1157674040641806703/1158000000000000000 : ℝ)+(1008159772337/636900000000000 : ℝ)*((4037/25000 : ℝ)+(9779/100000 : ℝ)))^(2145/512 : ℝ) := by
    rw [show (1157674040641806703/1158000000000000000 : ℝ)+(1008159772337/636900000000000 : ℝ)*((4037/25000 : ℝ)+(9779/100000 : ℝ))=(625080573811791/625000000000000 : ℝ) by norm_num, show 1+(48133848173467629/100000000000000000000 : ℝ)+(1177377976041753/20000000000000000000 : ℝ)=(50027010369026838197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48133848173467629/100000000000000000000 : ℝ) ≤ ((1157674040641806703/1158000000000000000 : ℝ)+2*(1008159772337/636900000000000 : ℝ)*(4037/25000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (1157674040641806703/1158000000000000000 : ℝ)+2*(1008159772337/636900000000000 : ℝ)*(4037/25000 : ℝ)=(10002297340760993/10000000000000000 : ℝ) by norm_num, show 1+2*(48133848173467629/100000000000000000000 : ℝ)=(50048133848173467629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1157674040641806703/1158000000000000000 : ℝ)*(X 1 0+X 2 0)+(1008159772337/636900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (4037/25000 : ℝ)) (c := (1157674040641806703/1158000000000000000 : ℝ)) (alpha := (1008159772337/636900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1157674040641806703/1158000000000000000 : ℝ)*(X 0 1+X 2 1)+(1008159772337/636900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (4037/25000 : ℝ)) (c := (1157674040641806703/1158000000000000000 : ℝ)) (alpha := (1008159772337/636900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1157674040641806703/1158000000000000000 : ℝ)*(X 0 2+X 1 2)+(1008159772337/636900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (9779/100000 : ℝ)) (hi := (4037/25000 : ℝ)) (c := (1157674040641806703/1158000000000000000 : ℝ)) (alpha := (1008159772337/636900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1025818333/5000000000 : ℝ)*X 0 0+(542859761/1000000000 : ℝ)*X 0 1+(2615086189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070617123/2000000000 : ℝ)*X 1 0+(-1076537703/5000000000 : ℝ)*X 1 1+(2615086253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669135671/1250000000 : ℝ)*X 2 0+(2615086401/5000000000 : ℝ)*X 2 1+(-2153075343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328370051/10000000000 : ℝ)*X 0 0+(2063032951/5000000000 : ℝ)*X 0 1+(4539962161/10000000000 : ℝ)*X 0 2+(4328370051/10000000000 : ℝ)*X 1 0+(2063032951/5000000000 : ℝ)*X 1 1+(4539962161/10000000000 : ℝ)*X 1 2+(4328370051/10000000000 : ℝ)*X 2 0+(2063032951/5000000000 : ℝ)*X 2 1+(4539962161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1025828311/5000000000 : ℝ)*X 0 0+(163468901/312500000 : ℝ)*X 0 1+(84808751/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325509777/2500000000 : ℝ)*X 1 0+(-977744041/5000000000 : ℝ)*X 1 1+(5427760261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325510193/2500000000 : ℝ)*X 2 0+(5427759097/10000000000 : ℝ)*X 2 1+(-122217963/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17313649/40000000 : ℝ)*X 0 0+(453822583/1000000000 : ℝ)*X 0 1+(825562397/2000000000 : ℝ)*X 0 2+(17313649/40000000 : ℝ)*X 1 0+(453822583/1000000000 : ℝ)*X 1 1+(825562397/2000000000 : ℝ)*X 1 2+(17313649/40000000 : ℝ)*X 2 0+(453822583/1000000000 : ℝ)*X 2 1+(825562397/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (899446694833201299337385913/212300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (720794091/100000000000000 : ℝ)*(base19) + (93994449/25000000000000 : ℝ)*(base23) + (26499849/20000000000000 : ℝ)*(upper3) + (60102249/100000000000000 : ℝ)*(upper4) + (37578851/50000000000000 : ℝ)*(upper5) + (3727894359398487/100000000000000 : ℝ)*(major0) + (3727894359398487/100000000000000 : ℝ)*(major1) + (3727894359398487/100000000000000 : ℝ)*(major2) + (2519848803778787/50000000000000 : ℝ)*(sp0) + (2519855422951599/50000000000000 : ℝ)*(sp1) + (5039711190719493/100000000000000 : ℝ)*(sp2) + (1208035239216493/50000000000000 : ℝ)*(sp3) + (2791827943/20000000000000 : ℝ)*(sp4) + (65324441/1000000000000 : ℝ)*(sp7) + (1208038505438543/50000000000000 : ℝ)*(f.failure) + (5039711566697289/100000000000000 : ℝ)*(f.sum) + (74187845624093/10615000000000000000000000000 : ℝ)*base65 + (2182222627598659343/424600000000000000000000000000000 : ℝ)*base68 + (6972205960014259343/424600000000000000000000000000000 : ℝ)*base70 + (3522165399133059343/424600000000000000000000000000000 : ℝ)*base72 + (27042154151213/10615000000000000000000000000 : ℝ)*base73 + (2074122882231859343/424600000000000000000000000000000 : ℝ)*base76 + (1175987849421459343/424600000000000000000000000000000 : ℝ)*base78 + (3548555011802259343/424600000000000000000000000000000 : ℝ)*base80 + (1160061013629/1326875000000000000000000000 : ℝ)*base82 + (3696467/1000000000000000000000 : ℝ)*base89 + (3696467/1000000000000000000000 : ℝ)*base91 + (3696467/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1804179894128892230459/5307500000000000000000000000 : ℝ) := by norm_num
    linear_combination (122971361/25000000000000 : ℝ)*(base19) + (2468807577/100000000000000 : ℝ)*(base23) + (26913523/12500000000000 : ℝ)*(upper3) + (52021751/100000000000000 : ℝ)*(lower4) + (31189031/50000000000000 : ℝ)*(upper5) + (1879758802238723/50000000000000 : ℝ)*(major0) + (1879758802238723/50000000000000 : ℝ)*(major1) + (1879758802238723/50000000000000 : ℝ)*(major2) + (1388220547/25000000000000 : ℝ)*(sp1) + (17511569811/50000000000000 : ℝ)*(sp2) + (5082462918351651/100000000000000 : ℝ)*(sp4) + (254122843679201/5000000000000 : ℝ)*(sp5) + (5082425426404453/100000000000000 : ℝ)*(sp6) + (2436572279272227/100000000000000 : ℝ)*(sp7) + (2436572279272227/100000000000000 : ℝ)*(f.failure) + (5082462918351651/100000000000000 : ℝ)*(f.sum) + (43106632189321/15922500000000000000000000000 : ℝ)*base65 + (1276233623522127653/212300000000000000000000000000000 : ℝ)*base67 + (1494094775953027653/212300000000000000000000000000000 : ℝ)*base69 + (1178159624219727653/212300000000000000000000000000000 : ℝ)*base71 + (7724602703/7961250000000000000000000000 : ℝ)*base73 + (444010327060172347/212300000000000000000000000000000 : ℝ)*base76 + (643635256813872347/212300000000000000000000000000000 : ℝ)*base78 + (326385565559772347/212300000000000000000000000000000 : ℝ)*base80 + (48308760162823/31845000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2776663/2000000000000000000000 : ℝ)*base89 + (2776663/2000000000000000000000 : ℝ)*base91 + (2776663/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1331_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4037/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (751/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1331_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1331_s4_0 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2053188001/10000000000 : ℝ)*x 0 + (135400953/250000000 : ℝ)*x 1 + (5241713613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053188001/10000000000 : ℝ)^4291 ≤ (1562529309517/12500000000000 : ℝ)^3267 := by
    have hnat : (2053188001 : ℕ)^4291*12500000000000^3267 ≤ 1562529309517^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053188001 10000000000 1562529309517 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135400953/250000000 : ℝ)^4291 ≤ (11172429124901/25000000000000 : ℝ)^3267 := by
    have hnat : (135400953 : ℕ)^4291*25000000000000^3267 ≤ 11172429124901^3267*250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135400953 250000000 11172429124901 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241713613/10000000000 : ℝ)^4291 ≤ (42810049004059/100000000000000 : ℝ)^3267 := by
    have hnat : (5241713613 : ℕ)^4291*100000000000000^3267 ≤ 42810049004059^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241713613 10000000000 42810049004059 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2053188001/10000000000 : ℝ), (135400953/250000000 : ℝ), (5241713613/10000000000 : ℝ)] ![(1562529309517/12500000000000 : ℝ), (11172429124901/25000000000000 : ℝ), (42810049004059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2053188001/10000000000 : ℝ)|^4291 ≤ (1562529309517/12500000000000 : ℝ)^3267
        have hw : |(-2053188001/10000000000 : ℝ)|=(2053188001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135400953/250000000 : ℝ)|^4291 ≤ (11172429124901/25000000000000 : ℝ)^3267
        have hw : |(135400953/250000000 : ℝ)|=(135400953/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241713613/10000000000 : ℝ)|^4291 ≤ (42810049004059/100000000000000 : ℝ)^3267
        have hw : |(5241713613/10000000000 : ℝ)|=(5241713613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_1 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349890463/10000000000 : ℝ)*x 0 + (-1071034573/5000000000 : ℝ)*x 1 + (104834269/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349890463/10000000000 : ℝ)^4291 ≤ (1374193972331/3125000000000 : ℝ)^3267 := by
    have hnat : (5349890463 : ℕ)^4291*3125000000000^3267 ≤ 1374193972331^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349890463 10000000000 1374193972331 3125000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071034573/5000000000 : ℝ)^4291 ≤ (13215745613919/100000000000000 : ℝ)^3267 := by
    have hnat : (1071034573 : ℕ)^4291*100000000000000^3267 ≤ 13215745613919^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071034573 5000000000 13215745613919 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104834269/200000000 : ℝ)^4291 ≤ (5351255906943/12500000000000 : ℝ)^3267 := by
    have hnat : (104834269 : ℕ)^4291*12500000000000^3267 ≤ 5351255906943^3267*200000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104834269 200000000 5351255906943 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349890463/10000000000 : ℝ), (-1071034573/5000000000 : ℝ), (104834269/200000000 : ℝ)] ![(1374193972331/3125000000000 : ℝ), (13215745613919/100000000000000 : ℝ), (5351255906943/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349890463/10000000000 : ℝ)|^4291 ≤ (1374193972331/3125000000000 : ℝ)^3267
        have hw : |(5349890463/10000000000 : ℝ)|=(5349890463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071034573/5000000000 : ℝ)|^4291 ≤ (13215745613919/100000000000000 : ℝ)^3267
        have hw : |(-1071034573/5000000000 : ℝ)|=(1071034573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104834269/200000000 : ℝ)|^4291 ≤ (5351255906943/12500000000000 : ℝ)^3267
        have hw : |(104834269/200000000 : ℝ)|=(104834269/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_2 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069978113/2000000000 : ℝ)*x 0 + (5241713207/10000000000 : ℝ)*x 1 + (-535517333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069978113/2000000000 : ℝ)^4291 ≤ (43974208215783/100000000000000 : ℝ)^3267 := by
    have hnat : (1069978113 : ℕ)^4291*100000000000000^3267 ≤ 43974208215783^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069978113 2000000000 43974208215783 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241713207/10000000000 : ℝ)^4291 ≤ (21405022324431/50000000000000 : ℝ)^3267 := by
    have hnat : (5241713207 : ℕ)^4291*50000000000000^3267 ≤ 21405022324431^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241713207 10000000000 21405022324431 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535517333/2500000000 : ℝ)^4291 ≤ (13215747121153/100000000000000 : ℝ)^3267 := by
    have hnat : (535517333 : ℕ)^4291*100000000000000^3267 ≤ 13215747121153^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535517333 2500000000 13215747121153 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069978113/2000000000 : ℝ), (5241713207/10000000000 : ℝ), (-535517333/2500000000 : ℝ)] ![(43974208215783/100000000000000 : ℝ), (21405022324431/50000000000000 : ℝ), (13215747121153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069978113/2000000000 : ℝ)|^4291 ≤ (43974208215783/100000000000000 : ℝ)^3267
        have hw : |(1069978113/2000000000 : ℝ)|=(1069978113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241713207/10000000000 : ℝ)|^4291 ≤ (21405022324431/50000000000000 : ℝ)^3267
        have hw : |(5241713207/10000000000 : ℝ)|=(5241713207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535517333/2500000000 : ℝ)|^4291 ≤ (13215747121153/100000000000000 : ℝ)^3267
        have hw : |(-535517333/2500000000 : ℝ)|=(535517333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_3 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329311811/10000000000 : ℝ)*x 0 + (2075542061/5000000000 : ℝ)*x 1 + (4514709549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329311811/10000000000 : ℝ)^4291 ≤ (2081320475543/6250000000000 : ℝ)^3267 := by
    have hnat : (4329311811 : ℕ)^4291*6250000000000^3267 ≤ 2081320475543^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329311811 10000000000 2081320475543 6250000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075542061/5000000000 : ℝ)^4291 ≤ (15756112799259/50000000000000 : ℝ)^3267 := by
    have hnat : (2075542061 : ℕ)^4291*50000000000000^3267 ≤ 15756112799259^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075542061 5000000000 15756112799259 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514709549/10000000000 : ℝ)^4291 ≤ (703732935499/2000000000000 : ℝ)^3267 := by
    have hnat : (4514709549 : ℕ)^4291*2000000000000^3267 ≤ 703732935499^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514709549 10000000000 703732935499 2000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329311811/10000000000 : ℝ), (2075542061/5000000000 : ℝ), (4514709549/10000000000 : ℝ)] ![(2081320475543/6250000000000 : ℝ), (15756112799259/50000000000000 : ℝ), (703732935499/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329311811/10000000000 : ℝ)|^4291 ≤ (2081320475543/6250000000000 : ℝ)^3267
        have hw : |(4329311811/10000000000 : ℝ)|=(4329311811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075542061/5000000000 : ℝ)|^4291 ≤ (15756112799259/50000000000000 : ℝ)^3267
        have hw : |(2075542061/5000000000 : ℝ)|=(2075542061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514709549/10000000000 : ℝ)|^4291 ≤ (703732935499/2000000000000 : ℝ)^3267
        have hw : |(4514709549/10000000000 : ℝ)|=(4514709549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_4 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-64162551/312500000 : ℝ)*x 0 + (5242356457/10000000000 : ℝ)*x 1 + (5415391753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64162551/312500000 : ℝ)^4291 ≤ (12500343476259/100000000000000 : ℝ)^3267 := by
    have hnat : (64162551 : ℕ)^4291*100000000000000^3267 ≤ 12500343476259^3267*312500000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64162551 312500000 12500343476259 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242356457/10000000000 : ℝ)^4291 ≤ (10704236245079/25000000000000 : ℝ)^3267 := by
    have hnat : (5242356457 : ℕ)^4291*25000000000000^3267 ≤ 10704236245079^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242356457 10000000000 10704236245079 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415391753/10000000000 : ℝ)^4291 ≤ (44682711528957/100000000000000 : ℝ)^3267 := by
    have hnat : (5415391753 : ℕ)^4291*100000000000000^3267 ≤ 44682711528957^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415391753 10000000000 44682711528957 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64162551/312500000 : ℝ), (5242356457/10000000000 : ℝ), (5415391753/10000000000 : ℝ)] ![(12500343476259/100000000000000 : ℝ), (10704236245079/25000000000000 : ℝ), (44682711528957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64162551/312500000 : ℝ)|^4291 ≤ (12500343476259/100000000000000 : ℝ)^3267
        have hw : |(-64162551/312500000 : ℝ)|=(64162551/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242356457/10000000000 : ℝ)|^4291 ≤ (10704236245079/25000000000000 : ℝ)^3267
        have hw : |(5242356457/10000000000 : ℝ)|=(5242356457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415391753/10000000000 : ℝ)|^4291 ≤ (44682711528957/100000000000000 : ℝ)^3267
        have hw : |(5415391753/10000000000 : ℝ)|=(5415391753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_5 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061009137/2000000000 : ℝ)*x 0 + (-984195489/5000000000 : ℝ)*x 1 + (5415391753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061009137/2000000000 : ℝ)^4291 ≤ (8698140106759/20000000000000 : ℝ)^3267 := by
    have hnat : (1061009137 : ℕ)^4291*20000000000000^3267 ≤ 8698140106759^3267*2000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061009137 2000000000 8698140106759 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984195489/5000000000 : ℝ)^4291 ≤ (11826587915097/100000000000000 : ℝ)^3267 := by
    have hnat : (984195489 : ℕ)^4291*100000000000000^3267 ≤ 11826587915097^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984195489 5000000000 11826587915097 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415391753/10000000000 : ℝ)^4291 ≤ (44682711528957/100000000000000 : ℝ)^3267 := by
    have hnat : (5415391753 : ℕ)^4291*100000000000000^3267 ≤ 44682711528957^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415391753 10000000000 44682711528957 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061009137/2000000000 : ℝ), (-984195489/5000000000 : ℝ), (5415391753/10000000000 : ℝ)] ![(8698140106759/20000000000000 : ℝ), (11826587915097/100000000000000 : ℝ), (44682711528957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061009137/2000000000 : ℝ)|^4291 ≤ (8698140106759/20000000000000 : ℝ)^3267
        have hw : |(1061009137/2000000000 : ℝ)|=(1061009137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984195489/5000000000 : ℝ)|^4291 ≤ (11826587915097/100000000000000 : ℝ)^3267
        have hw : |(-984195489/5000000000 : ℝ)|=(984195489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415391753/10000000000 : ℝ)|^4291 ≤ (44682711528957/100000000000000 : ℝ)^3267
        have hw : |(5415391753/10000000000 : ℝ)|=(5415391753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_6 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652522849/5000000000 : ℝ)*x 0 + (676923967/1250000000 : ℝ)*x 1 + (-246048873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652522849/5000000000 : ℝ)^4291 ≤ (21745350336887/50000000000000 : ℝ)^3267 := by
    have hnat : (2652522849 : ℕ)^4291*50000000000000^3267 ≤ 21745350336887^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652522849 5000000000 21745350336887 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676923967/1250000000 : ℝ)^4291 ≤ (44682711344723/100000000000000 : ℝ)^3267 := by
    have hnat : (676923967 : ℕ)^4291*100000000000000^3267 ≤ 44682711344723^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676923967 1250000000 44682711344723 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246048873/1250000000 : ℝ)^4291 ≤ (5913293981223/50000000000000 : ℝ)^3267 := by
    have hnat : (246048873 : ℕ)^4291*50000000000000^3267 ≤ 5913293981223^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246048873 1250000000 5913293981223 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652522849/5000000000 : ℝ), (676923967/1250000000 : ℝ), (-246048873/1250000000 : ℝ)] ![(21745350336887/50000000000000 : ℝ), (44682711344723/100000000000000 : ℝ), (5913293981223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652522849/5000000000 : ℝ)|^4291 ≤ (21745350336887/50000000000000 : ℝ)^3267
        have hw : |(2652522849/5000000000 : ℝ)|=(2652522849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676923967/1250000000 : ℝ)|^4291 ≤ (44682711344723/100000000000000 : ℝ)^3267
        have hw : |(676923967/1250000000 : ℝ)|=(676923967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246048873/1250000000 : ℝ)|^4291 ≤ (5913293981223/50000000000000 : ℝ)^3267
        have hw : |(-246048873/1250000000 : ℝ)|=(246048873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s4_7 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (432933983/1000000000 : ℝ)*x 0 + (1128342051/2500000000 : ℝ)*x 1 + (1038108179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432933983/1000000000 : ℝ)^4291 ≤ (16650705342173/50000000000000 : ℝ)^3267 := by
    have hnat : (432933983 : ℕ)^4291*50000000000000^3267 ≤ 16650705342173^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432933983 1000000000 16650705342173 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128342051/2500000000 : ℝ)^4291 ≤ (35172916547959/100000000000000 : ℝ)^3267 := by
    have hnat : (1128342051 : ℕ)^4291*100000000000000^3267 ≤ 35172916547959^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128342051 2500000000 35172916547959 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038108179/2500000000 : ℝ)^4291 ≤ (31525672748703/100000000000000 : ℝ)^3267 := by
    have hnat : (1038108179 : ℕ)^4291*100000000000000^3267 ≤ 31525672748703^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038108179 2500000000 31525672748703 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432933983/1000000000 : ℝ), (1128342051/2500000000 : ℝ), (1038108179/2500000000 : ℝ)] ![(16650705342173/50000000000000 : ℝ), (35172916547959/100000000000000 : ℝ), (31525672748703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432933983/1000000000 : ℝ)|^4291 ≤ (16650705342173/50000000000000 : ℝ)^3267
        have hw : |(432933983/1000000000 : ℝ)|=(432933983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128342051/2500000000 : ℝ)|^4291 ≤ (35172916547959/100000000000000 : ℝ)^3267
        have hw : |(1128342051/2500000000 : ℝ)|=(1128342051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038108179/2500000000 : ℝ)|^4291 ≤ (31525672748703/100000000000000 : ℝ)^3267
        have hw : |(1038108179/2500000000 : ℝ)|=(1038108179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1331_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (751/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2767/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7379/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (751/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5411/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (751/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5411/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (751/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5411/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (751/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5411/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (751/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5411/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (751/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5411/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5411/50000 : ℝ) ^ (2145/512 : ℝ) ≤ (4500353891033843/50000000000000000000 : ℝ) := by
    have hpowers : (5411/50000 : ℝ)^2145 ≤ (4500353891033843/50000000000000000000 : ℝ)^512 := by
      have hnat : (5411 : ℕ)^2145*50000000000000000000^512 ≤ 4500353891033843^512*50000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5411 50000 4500353891033843 50000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5411/50000 : ℝ)) (X := (4500353891033843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hpowhi : (751/5000 : ℝ) ^ (2145/512 : ℝ) ≤ (4442293916814917/12500000000000000000 : ℝ) := by
    have hpowers : (751/5000 : ℝ)^2145 ≤ (4442293916814917/12500000000000000000 : ℝ)^512 := by
      have hnat : (751 : ℕ)^2145*12500000000000000000^512 ≤ 4442293916814917^512*5000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        751 5000 4442293916814917 12500000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (751/5000 : ℝ)) (X := (4442293916814917/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004500353891033843/25000000000000000000 : ℝ) ≤ (1250053706837291/1250000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (25004500353891033843/25000000000000000000 : ℝ)^512 ≤ (1250053706837291/1250000000000000 : ℝ)^2145 := by
      have hnat : (25004500353891033843 : ℕ)^512*1250000000000000^2145 ≤ 1250053706837291^2145*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004500353891033843 25000000000000000000 1250053706837291 1250000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250053706837291/1250000000000000 : ℝ)) (X := (25004500353891033843/25000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022269529558293511/50000000000000000000 : ℝ) ≤ (5000531471634231/5000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50022269529558293511/50000000000000000000 : ℝ)^512 ≤ (5000531471634231/5000000000000000 : ℝ)^2145 := by
      have hnat : (50022269529558293511 : ℕ)^512*5000000000000000^2145 ≤ 5000531471634231^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022269529558293511 50000000000000000000 5000531471634231 5000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000531471634231/5000000000000000 : ℝ)) (X := (50022269529558293511/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254442293916814917/6250000000000000000 : ℝ) ≤ (2500424057959649/2500000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (6254442293916814917/6250000000000000000 : ℝ)^512 ≤ (2500424057959649/2500000000000000 : ℝ)^2145 := by
      have hnat : (6254442293916814917 : ℕ)^512*2500000000000000^2145 ≤ 2500424057959649^2145*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254442293916814917 6250000000000000000 2500424057959649 2500000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500424057959649/2500000000000000 : ℝ)) (X := (6254442293916814917/6250000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4500353891033843/50000000000000000000 : ℝ) ≤ ((5246012099076450081/5247500000000000000 : ℝ)+2*(316644285067/209900000000000 : ℝ)*(5411/50000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (5246012099076450081/5247500000000000000 : ℝ)+2*(316644285067/209900000000000 : ℝ)*(5411/50000 : ℝ)=(1250053706837291/1250000000000000 : ℝ) by norm_num, show 1+2*(4500353891033843/50000000000000000000 : ℝ)=(25004500353891033843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4442293916814917/12500000000000000000 : ℝ)+(4500353891033843/50000000000000000000 : ℝ) ≤ ((5246012099076450081/5247500000000000000 : ℝ)+(316644285067/209900000000000 : ℝ)*((751/5000 : ℝ)+(5411/50000 : ℝ)))^(2145/512 : ℝ) := by
    rw [show (5246012099076450081/5247500000000000000 : ℝ)+(316644285067/209900000000000 : ℝ)*((751/5000 : ℝ)+(5411/50000 : ℝ))=(5000531471634231/5000000000000000 : ℝ) by norm_num, show 1+(4442293916814917/12500000000000000000 : ℝ)+(4500353891033843/50000000000000000000 : ℝ)=(50022269529558293511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4442293916814917/12500000000000000000 : ℝ) ≤ ((5246012099076450081/5247500000000000000 : ℝ)+2*(316644285067/209900000000000 : ℝ)*(751/5000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (5246012099076450081/5247500000000000000 : ℝ)+2*(316644285067/209900000000000 : ℝ)*(751/5000 : ℝ)=(2500424057959649/2500000000000000 : ℝ) by norm_num, show 1+2*(4442293916814917/12500000000000000000 : ℝ)=(6254442293916814917/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5246012099076450081/5247500000000000000 : ℝ)*(X 1 0+X 2 0)+(316644285067/209900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (751/5000 : ℝ)) (c := (5246012099076450081/5247500000000000000 : ℝ)) (alpha := (316644285067/209900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5246012099076450081/5247500000000000000 : ℝ)*(X 0 1+X 2 1)+(316644285067/209900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (751/5000 : ℝ)) (c := (5246012099076450081/5247500000000000000 : ℝ)) (alpha := (316644285067/209900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5246012099076450081/5247500000000000000 : ℝ)*(X 0 2+X 1 2)+(316644285067/209900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (751/5000 : ℝ)) (c := (5246012099076450081/5247500000000000000 : ℝ)) (alpha := (316644285067/209900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2053188001/10000000000 : ℝ)*X 0 0+(135400953/250000000 : ℝ)*X 0 1+(5241713613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349890463/10000000000 : ℝ)*X 1 0+(-1071034573/5000000000 : ℝ)*X 1 1+(104834269/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069978113/2000000000 : ℝ)*X 2 0+(5241713207/10000000000 : ℝ)*X 2 1+(-535517333/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329311811/10000000000 : ℝ)*X 0 0+(2075542061/5000000000 : ℝ)*X 0 1+(4514709549/10000000000 : ℝ)*X 0 2+(4329311811/10000000000 : ℝ)*X 1 0+(2075542061/5000000000 : ℝ)*X 1 1+(4514709549/10000000000 : ℝ)*X 1 2+(4329311811/10000000000 : ℝ)*X 2 0+(2075542061/5000000000 : ℝ)*X 2 1+(4514709549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-64162551/312500000 : ℝ)*X 0 0+(5242356457/10000000000 : ℝ)*X 0 1+(5415391753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061009137/2000000000 : ℝ)*X 1 0+(-984195489/5000000000 : ℝ)*X 1 1+(5415391753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652522849/5000000000 : ℝ)*X 2 0+(676923967/1250000000 : ℝ)*X 2 1+(-246048873/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432933983/1000000000 : ℝ)*X 0 0+(1128342051/2500000000 : ℝ)*X 0 1+(1038108179/2500000000 : ℝ)*X 0 2+(432933983/1000000000 : ℝ)*X 1 0+(1128342051/2500000000 : ℝ)*X 1 1+(1038108179/2500000000 : ℝ)*X 1 2+(432933983/1000000000 : ℝ)*X 2 0+(1128342051/2500000000 : ℝ)*X 2 1+(1038108179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (509534989517568825893667993/65593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414177667/25000000000000 : ℝ)*(base19) + (1661981891/100000000000000 : ℝ)*(base23) + (545203/500000000000 : ℝ)*(lower2) + (278219301/100000000000000 : ℝ)*(upper3) + (3334283/6250000000000 : ℝ)*(lower4) + (2121649863038249/50000000000000 : ℝ)*(major0) + (2121649863038249/50000000000000 : ℝ)*(major1) + (2121649863038249/50000000000000 : ℝ)*(major2) + (1147292002672533/20000000000000 : ℝ)*(sp0) + (1434120585692231/25000000000000 : ℝ)*(sp1) + (57364823374977/1000000000000 : ℝ)*(sp2) + (687524127288063/25000000000000 : ℝ)*(sp3) + (11993058463/50000000000000 : ℝ)*(sp4) + (18684586417/100000000000000 : ℝ)*(sp7) + (2750115193738669/100000000000000 : ℝ)*(f.failure) + (5736483999479591/100000000000000 : ℝ)*(f.sum) + (55848767929209/10495000000000000000000000000 : ℝ)*base66 + (3512904982408473169/262375000000000000000000000000000 : ℝ)*base67 + (2851789761302098169/262375000000000000000000000000000 : ℝ)*base69 + (2477940426220973169/262375000000000000000000000000000 : ℝ)*base71 + (11642846717047/5247500000000000000000000000 : ℝ)*base74 + (2023730149175776831/262375000000000000000000000000000 : ℝ)*base76 + (531425249206973169/262375000000000000000000000000000 : ℝ)*base77 + (6917419246798223169/262375000000000000000000000000000 : ℝ)*base79 + (22457564361017/5247500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5360839/2000000000000000000000 : ℝ)*base90 + (5360839/2000000000000000000000 : ℝ)*base92 + (5360839/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104581169623166683590126177/16398437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1136782529/100000000000000 : ℝ)*(base19) + (617029969/50000000000000 : ℝ)*(base23) + (32555651/25000000000000 : ℝ)*(upper3) + (7792897/20000000000000 : ℝ)*(lower4) + (13788561/10000000000000 : ℝ)*(upper5) + (133589772145593/3125000000000 : ℝ)*(major0) + (133589772145593/3125000000000 : ℝ)*(major1) + (133589772145593/3125000000000 : ℝ)*(major2) + (5627468201/25000000000000 : ℝ)*(sp1) + (2956685509/12500000000000 : ℝ)*(sp2) + (5779167318111139/100000000000000 : ℝ)*(sp4) + (2889571835727903/50000000000000 : ℝ)*(sp5) + (5779142430567129/100000000000000 : ℝ)*(sp6) + (2770577886623201/100000000000000 : ℝ)*(sp7) + (2770577886623201/100000000000000 : ℝ)*(f.failure) + (5779167318111139/100000000000000 : ℝ)*(f.sum) + (25148375042651/5247500000000000000000000000 : ℝ)*base65 + (143629033881757941/32796875000000000000000000000000 : ℝ)*base67 + (11532894623257941/32796875000000000000000000000000 : ℝ)*base69 + (180893878574980533/16398437500000000000000000000000 : ℝ)*base71 + (5905289312231/1311875000000000000000000000 : ℝ)*base74 + (63976035180314421/8199218750000000000000000000000 : ℝ)*base76 + (36242009202793033/16398437500000000000000000000000 : ℝ)*base77 + (147368807841738217/16398437500000000000000000000000 : ℝ)*base80 + (2501308247807/2623750000000000000000000000 : ℝ)*base82 + (16659869/2000000000000000000000 : ℝ)*base89 + (16659869/2000000000000000000000 : ℝ)*base91 + (16659869/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1331_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (751/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1331_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1331_s5_0 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1642769/8000000 : ℝ)*x 0 + (1353425341/2500000000 : ℝ)*x 1 + (262193523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1642769/8000000 : ℝ)^4291 ≤ (12502419551703/100000000000000 : ℝ)^3267 := by
    have hnat : (1642769 : ℕ)^4291*100000000000000^3267 ≤ 12502419551703^3267*8000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642769 8000000 12502419551703 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353425341/2500000000 : ℝ)^4291 ≤ (4466439325999/10000000000000 : ℝ)^3267 := by
    have hnat : (1353425341 : ℕ)^4291*10000000000000^3267 ≤ 4466439325999^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353425341 2500000000 4466439325999 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262193523/500000000 : ℝ)^4291 ≤ (1713327487281/4000000000000 : ℝ)^3267 := by
    have hnat : (262193523 : ℕ)^4291*4000000000000^3267 ≤ 1713327487281^3267*500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262193523 500000000 1713327487281 4000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1642769/8000000 : ℝ), (1353425341/2500000000 : ℝ), (262193523/500000000 : ℝ)] ![(12502419551703/100000000000000 : ℝ), (4466439325999/10000000000000 : ℝ), (1713327487281/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1642769/8000000 : ℝ)|^4291 ≤ (12502419551703/100000000000000 : ℝ)^3267
        have hw : |(-1642769/8000000 : ℝ)|=(1642769/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353425341/2500000000 : ℝ)|^4291 ≤ (4466439325999/10000000000000 : ℝ)^3267
        have hw : |(1353425341/2500000000 : ℝ)|=(1353425341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262193523/500000000 : ℝ)|^4291 ≤ (1713327487281/4000000000000 : ℝ)^3267
        have hw : |(262193523/500000000 : ℝ)|=(262193523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_1 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349294317/10000000000 : ℝ)*x 0 + (-2140006953/10000000000 : ℝ)*x 1 + (5243870853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349294317/10000000000 : ℝ)^4291 ≤ (5495971405029/12500000000000 : ℝ)^3267 := by
    have hnat : (5349294317 : ℕ)^4291*12500000000000^3267 ≤ 5495971405029^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349294317 10000000000 5495971405029 12500000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140006953/10000000000 : ℝ)^4291 ≤ (6599518674943/50000000000000 : ℝ)^3267 := by
    have hnat : (2140006953 : ℕ)^4291*50000000000000^3267 ≤ 6599518674943^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140006953 10000000000 6599518674943 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243870853/10000000000 : ℝ)^4291 ≤ (21416595699157/50000000000000 : ℝ)^3267 := by
    have hnat : (5243870853 : ℕ)^4291*50000000000000^3267 ≤ 21416595699157^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243870853 10000000000 21416595699157 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349294317/10000000000 : ℝ), (-2140006953/10000000000 : ℝ), (5243870853/10000000000 : ℝ)] ![(5495971405029/12500000000000 : ℝ), (6599518674943/50000000000000 : ℝ), (21416595699157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349294317/10000000000 : ℝ)|^4291 ≤ (5495971405029/12500000000000 : ℝ)^3267
        have hw : |(5349294317/10000000000 : ℝ)|=(5349294317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140006953/10000000000 : ℝ)|^4291 ≤ (6599518674943/50000000000000 : ℝ)^3267
        have hw : |(-2140006953/10000000000 : ℝ)|=(2140006953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243870853/10000000000 : ℝ)|^4291 ≤ (21416595699157/50000000000000 : ℝ)^3267
        have hw : |(5243870853/10000000000 : ℝ)|=(5243870853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_2 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334330821/625000000 : ℝ)*x 0 + (5243871387/10000000000 : ℝ)*x 1 + (-2140007819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334330821/625000000 : ℝ)^4291 ≤ (10991939622653/25000000000000 : ℝ)^3267 := by
    have hnat : (334330821 : ℕ)^4291*25000000000000^3267 ≤ 10991939622653^3267*625000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334330821 625000000 10991939622653 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243871387/10000000000 : ℝ)^4291 ≤ (21416598563659/50000000000000 : ℝ)^3267 := by
    have hnat : (5243871387 : ℕ)^4291*50000000000000^3267 ≤ 21416598563659^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243871387 10000000000 21416598563659 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140007819/10000000000 : ℝ)^4291 ≤ (13199044365317/100000000000000 : ℝ)^3267 := by
    have hnat : (2140007819 : ℕ)^4291*100000000000000^3267 ≤ 13199044365317^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140007819 10000000000 13199044365317 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334330821/625000000 : ℝ), (5243871387/10000000000 : ℝ), (-2140007819/10000000000 : ℝ)] ![(10991939622653/25000000000000 : ℝ), (21416598563659/50000000000000 : ℝ), (13199044365317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334330821/625000000 : ℝ)|^4291 ≤ (10991939622653/25000000000000 : ℝ)^3267
        have hw : |(334330821/625000000 : ℝ)|=(334330821/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243871387/10000000000 : ℝ)|^4291 ≤ (21416598563659/50000000000000 : ℝ)^3267
        have hw : |(5243871387/10000000000 : ℝ)|=(5243871387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140007819/10000000000 : ℝ)|^4291 ≤ (13199044365317/100000000000000 : ℝ)^3267
        have hw : |(-2140007819/10000000000 : ℝ)|=(2140007819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_3 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082368247/2500000000 : ℝ)*x 0 + (2077875989/5000000000 : ℝ)*x 1 + (35234393/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082368247/2500000000 : ℝ)^4291 ≤ (16651377993023/50000000000000 : ℝ)^3267 := by
    have hnat : (1082368247 : ℕ)^4291*50000000000000^3267 ≤ 16651377993023^3267*2500000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082368247 2500000000 16651377993023 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077875989/5000000000 : ℝ)^4291 ≤ (31558775726699/100000000000000 : ℝ)^3267 := by
    have hnat : (2077875989 : ℕ)^4291*100000000000000^3267 ≤ 31558775726699^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077875989 5000000000 31558775726699 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35234393/78125000 : ℝ)^4291 ≤ (3513846827641/10000000000000 : ℝ)^3267 := by
    have hnat : (35234393 : ℕ)^4291*10000000000000^3267 ≤ 3513846827641^3267*78125000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35234393 78125000 3513846827641 10000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082368247/2500000000 : ℝ), (2077875989/5000000000 : ℝ), (35234393/78125000 : ℝ)] ![(16651377993023/50000000000000 : ℝ), (31558775726699/100000000000000 : ℝ), (3513846827641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082368247/2500000000 : ℝ)|^4291 ≤ (16651377993023/50000000000000 : ℝ)^3267
        have hw : |(1082368247/2500000000 : ℝ)|=(1082368247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077875989/5000000000 : ℝ)|^4291 ≤ (31558775726699/100000000000000 : ℝ)^3267
        have hw : |(2077875989/5000000000 : ℝ)|=(2077875989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35234393/78125000 : ℝ)|^4291 ≤ (3513846827641/10000000000000 : ℝ)^3267
        have hw : |(35234393/78125000 : ℝ)|=(35234393/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_4 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-205347287/1000000000 : ℝ)*x 0 + (65556017/125000000 : ℝ)*x 1 + (2706543969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205347287/1000000000 : ℝ)^4291 ≤ (12502512474751/100000000000000 : ℝ)^3267 := by
    have hnat : (205347287 : ℕ)^4291*100000000000000^3267 ≤ 12502512474751^3267*1000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205347287 1000000000 12502512474751 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65556017/125000000 : ℝ)^4291 ≤ (21419870662193/50000000000000 : ℝ)^3267 := by
    have hnat : (65556017 : ℕ)^4291*50000000000000^3267 ≤ 21419870662193^3267*125000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65556017 125000000 21419870662193 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706543969/5000000000 : ℝ)^4291 ≤ (44657746178687/100000000000000 : ℝ)^3267 := by
    have hnat : (2706543969 : ℕ)^4291*100000000000000^3267 ≤ 44657746178687^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706543969 5000000000 44657746178687 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-205347287/1000000000 : ℝ), (65556017/125000000 : ℝ), (2706543969/5000000000 : ℝ)] ![(12502512474751/100000000000000 : ℝ), (21419870662193/50000000000000 : ℝ), (44657746178687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-205347287/1000000000 : ℝ)|^4291 ≤ (12502512474751/100000000000000 : ℝ)^3267
        have hw : |(-205347287/1000000000 : ℝ)|=(205347287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65556017/125000000 : ℝ)|^4291 ≤ (21419870662193/50000000000000 : ℝ)^3267
        have hw : |(65556017/125000000 : ℝ)|=(65556017/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706543969/5000000000 : ℝ)|^4291 ≤ (44657746178687/100000000000000 : ℝ)^3267
        have hw : |(2706543969/5000000000 : ℝ)|=(2706543969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_5 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605741/10000000000 : ℝ)*x 0 + (-19707899/100000000 : ℝ)*x 1 + (2706543979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605741/10000000000 : ℝ)^4291 ≤ (43496731061187/100000000000000 : ℝ)^3267 := by
    have hnat : (5305605741 : ℕ)^4291*100000000000000^3267 ≤ 43496731061187^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605741 10000000000 43496731061187 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19707899/100000000 : ℝ)^4291 ≤ (11845522532051/100000000000000 : ℝ)^3267 := by
    have hnat : (19707899 : ℕ)^4291*100000000000000^3267 ≤ 11845522532051^3267*100000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19707899 100000000 11845522532051 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706543979/5000000000 : ℝ)^4291 ≤ (44657746395403/100000000000000 : ℝ)^3267 := by
    have hnat : (2706543979 : ℕ)^4291*100000000000000^3267 ≤ 44657746395403^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706543979 5000000000 44657746395403 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605741/10000000000 : ℝ), (-19707899/100000000 : ℝ), (2706543979/5000000000 : ℝ)] ![(43496731061187/100000000000000 : ℝ), (11845522532051/100000000000000 : ℝ), (44657746395403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605741/10000000000 : ℝ)|^4291 ≤ (43496731061187/100000000000000 : ℝ)^3267
        have hw : |(5305605741/10000000000 : ℝ)|=(5305605741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19707899/100000000 : ℝ)|^4291 ≤ (11845522532051/100000000000000 : ℝ)^3267
        have hw : |(-19707899/100000000 : ℝ)|=(19707899/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706543979/5000000000 : ℝ)|^4291 ≤ (44657746395403/100000000000000 : ℝ)^3267
        have hw : |(2706543979/5000000000 : ℝ)|=(2706543979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_6 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605571/10000000000 : ℝ)*x 0 + (2706544059/5000000000 : ℝ)*x 1 + (-246348739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605571/10000000000 : ℝ)^4291 ≤ (10874182307661/25000000000000 : ℝ)^3267 := by
    have hnat : (5305605571 : ℕ)^4291*25000000000000^3267 ≤ 10874182307661^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605571 10000000000 10874182307661 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706544059/5000000000 : ℝ)^4291 ≤ (44657748129131/100000000000000 : ℝ)^3267 := by
    have hnat : (2706544059 : ℕ)^4291*100000000000000^3267 ≤ 44657748129131^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706544059 5000000000 44657748129131 100000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246348739/1250000000 : ℝ)^4291 ≤ (2369104525357/20000000000000 : ℝ)^3267 := by
    have hnat : (246348739 : ℕ)^4291*20000000000000^3267 ≤ 2369104525357^3267*1250000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246348739 1250000000 2369104525357 20000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605571/10000000000 : ℝ), (2706544059/5000000000 : ℝ), (-246348739/1250000000 : ℝ)] ![(10874182307661/25000000000000 : ℝ), (44657748129131/100000000000000 : ℝ), (2369104525357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605571/10000000000 : ℝ)|^4291 ≤ (10874182307661/25000000000000 : ℝ)^3267
        have hw : |(5305605571/10000000000 : ℝ)|=(5305605571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706544059/5000000000 : ℝ)|^4291 ≤ (44657748129131/100000000000000 : ℝ)^3267
        have hw : |(2706544059/5000000000 : ℝ)|=(2706544059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246348739/1250000000 : ℝ)|^4291 ≤ (2369104525357/20000000000000 : ℝ)^3267
        have hw : |(-246348739/1250000000 : ℝ)|=(246348739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1331_s5_7 (p : ℝ) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2164749879/5000000000 : ℝ)*x 0 + (4508729047/10000000000 : ℝ)*x 1 + (4157031069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164749879/5000000000 : ℝ)^4291 ≤ (16651513223107/50000000000000 : ℝ)^3267 := by
    have hnat : (2164749879 : ℕ)^4291*50000000000000^3267 ≤ 16651513223107^3267*5000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164749879 5000000000 16651513223107 50000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508729047/10000000000 : ℝ)^4291 ≤ (8781359809997/25000000000000 : ℝ)^3267 := by
    have hnat : (4508729047 : ℕ)^4291*25000000000000^3267 ≤ 8781359809997^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508729047 10000000000 8781359809997 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4157031069/10000000000 : ℝ)^4291 ≤ (7892883576349/25000000000000 : ℝ)^3267 := by
    have hnat : (4157031069 : ℕ)^4291*25000000000000^3267 ≤ 7892883576349^3267*10000000000^4291 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157031069 10000000000 7892883576349 25000000000000 4291 3267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4291/1024 : ℝ)) 4291 3267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164749879/5000000000 : ℝ), (4508729047/10000000000 : ℝ), (4157031069/10000000000 : ℝ)] ![(16651513223107/50000000000000 : ℝ), (8781359809997/25000000000000 : ℝ), (7892883576349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164749879/5000000000 : ℝ)|^4291 ≤ (16651513223107/50000000000000 : ℝ)^3267
        have hw : |(2164749879/5000000000 : ℝ)|=(2164749879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508729047/10000000000 : ℝ)|^4291 ≤ (8781359809997/25000000000000 : ℝ)^3267
        have hw : |(4508729047/10000000000 : ℝ)|=(4508729047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4157031069/10000000000 : ℝ)|^4291 ≤ (7892883576349/25000000000000 : ℝ)^3267
        have hw : |(4157031069/10000000000 : ℝ)|=(4157031069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1331_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5557/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7379/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7379/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2767/25000 : ℝ) ^ (2145/512 : ℝ) ≤ (19778917128103/200000000000000000 : ℝ) := by
    have hpowers : (2767/25000 : ℝ)^2145 ≤ (19778917128103/200000000000000000 : ℝ)^512 := by
      have hnat : (2767 : ℕ)^2145*200000000000000000^512 ≤ 19778917128103^512*25000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2767 25000 19778917128103 200000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2767/25000 : ℝ)) (X := (19778917128103/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7379/50000 : ℝ) ^ (2145/512 : ℝ) ≤ (33012596845521257/100000000000000000000 : ℝ) := by
    have hpowers : (7379/50000 : ℝ)^2145 ≤ (33012596845521257/100000000000000000000 : ℝ)^512 := by
      have hnat : (7379 : ℕ)^2145*100000000000000000000^512 ≤ 33012596845521257^512*50000^2145 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7379 50000 33012596845521257 100000000000000000000 2145 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7379/50000 : ℝ)) (X := (33012596845521257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (100019778917128103/100000000000000000 : ℝ) ≤ (10000472076607053/10000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (100019778917128103/100000000000000000 : ℝ)^512 ≤ (10000472076607053/10000000000000000 : ℝ)^2145 := by
      have hnat : (100019778917128103 : ℕ)^512*10000000000000000^2145 ≤ 10000472076607053^2145*100000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019778917128103 100000000000000000 10000472076607053 10000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000472076607053/10000000000000000 : ℝ)) (X := (100019778917128103/100000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042902055409572757/100000000000000000000 : ℝ) ≤ (2500255970467103/2500000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (100042902055409572757/100000000000000000000 : ℝ)^512 ≤ (2500255970467103/2500000000000000 : ℝ)^2145 := by
      have hnat : (100042902055409572757 : ℕ)^512*2500000000000000^2145 ≤ 2500255970467103^2145*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042902055409572757 100000000000000000000 2500255970467103 2500000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500255970467103/2500000000000000 : ℝ)) (X := (100042902055409572757/100000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033012596845521257/50000000000000000000 : ℝ) ≤ (10001575687129771/10000000000000000 : ℝ) ^ (2145/512 : ℝ) := by
    have hpowers : (50033012596845521257/50000000000000000000 : ℝ)^512 ≤ (10001575687129771/10000000000000000 : ℝ)^2145 := by
      have hnat : (50033012596845521257 : ℕ)^512*10000000000000000^2145 ≤ 10001575687129771^2145*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033012596845521257 50000000000000000000 10001575687129771 10000000000000000 512 2145 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001575687129771/10000000000000000 : ℝ)) (X := (50033012596845521257/50000000000000000000 : ℝ)) (by norm_num) 2145 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19778917128103/200000000000000000 : ℝ) ≤ ((18444763600707291373/18450000000000000000 : ℝ)+2*(551805261359/369000000000000 : ℝ)*(2767/25000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (18444763600707291373/18450000000000000000 : ℝ)+2*(551805261359/369000000000000 : ℝ)*(2767/25000 : ℝ)=(10000472076607053/10000000000000000 : ℝ) by norm_num, show 1+2*(19778917128103/200000000000000000 : ℝ)=(100019778917128103/100000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33012596845521257/100000000000000000000 : ℝ)+(19778917128103/200000000000000000 : ℝ) ≤ ((18444763600707291373/18450000000000000000 : ℝ)+(551805261359/369000000000000 : ℝ)*((7379/50000 : ℝ)+(2767/25000 : ℝ)))^(2145/512 : ℝ) := by
    rw [show (18444763600707291373/18450000000000000000 : ℝ)+(551805261359/369000000000000 : ℝ)*((7379/50000 : ℝ)+(2767/25000 : ℝ))=(2500255970467103/2500000000000000 : ℝ) by norm_num, show 1+(33012596845521257/100000000000000000000 : ℝ)+(19778917128103/200000000000000000 : ℝ)=(100042902055409572757/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33012596845521257/100000000000000000000 : ℝ) ≤ ((18444763600707291373/18450000000000000000 : ℝ)+2*(551805261359/369000000000000 : ℝ)*(7379/50000 : ℝ))^(2145/512 : ℝ) := by
    rw [show (18444763600707291373/18450000000000000000 : ℝ)+2*(551805261359/369000000000000 : ℝ)*(7379/50000 : ℝ)=(10001575687129771/10000000000000000 : ℝ) by norm_num, show 1+2*(33012596845521257/100000000000000000000 : ℝ)=(50033012596845521257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18444763600707291373/18450000000000000000 : ℝ)*(X 1 0+X 2 0)+(551805261359/369000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (18444763600707291373/18450000000000000000 : ℝ)) (alpha := (551805261359/369000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18444763600707291373/18450000000000000000 : ℝ)*(X 0 1+X 2 1)+(551805261359/369000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (18444763600707291373/18450000000000000000 : ℝ)) (alpha := (551805261359/369000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18444763600707291373/18450000000000000000 : ℝ)*(X 0 2+X 1 2)+(551805261359/369000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2145/512 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (7379/50000 : ℝ)) (c := (18444763600707291373/18450000000000000000 : ℝ)) (alpha := (551805261359/369000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1642769/8000000 : ℝ)*X 0 0+(1353425341/2500000000 : ℝ)*X 0 1+(262193523/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349294317/10000000000 : ℝ)*X 1 0+(-2140006953/10000000000 : ℝ)*X 1 1+(5243870853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334330821/625000000 : ℝ)*X 2 0+(5243871387/10000000000 : ℝ)*X 2 1+(-2140007819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1082368247/2500000000 : ℝ)*X 0 0+(2077875989/5000000000 : ℝ)*X 0 1+(35234393/78125000 : ℝ)*X 0 2+(1082368247/2500000000 : ℝ)*X 1 0+(2077875989/5000000000 : ℝ)*X 1 1+(35234393/78125000 : ℝ)*X 1 2+(1082368247/2500000000 : ℝ)*X 2 0+(2077875989/5000000000 : ℝ)*X 2 1+(35234393/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-205347287/1000000000 : ℝ)*X 0 0+(65556017/125000000 : ℝ)*X 0 1+(2706543969/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305605741/10000000000 : ℝ)*X 1 0+(-19707899/100000000 : ℝ)*X 1 1+(2706543979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305605571/10000000000 : ℝ)*X 2 0+(2706544059/5000000000 : ℝ)*X 2 1+(-246348739/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2164749879/5000000000 : ℝ)*X 0 0+(4508729047/10000000000 : ℝ)*X 0 1+(4157031069/10000000000 : ℝ)*X 0 2+(2164749879/5000000000 : ℝ)*X 1 0+(4508729047/10000000000 : ℝ)*X 1 1+(4157031069/10000000000 : ℝ)*X 1 2+(2164749879/5000000000 : ℝ)*X 2 0+(4508729047/10000000000 : ℝ)*X 2 1+(4157031069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1331_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188562303174357642266361877/20500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (421280559/25000000000000 : ℝ)*(base19) + (1133717073/100000000000000 : ℝ)*(base23) + (143686783/25000000000000 : ℝ)*(upper2) + (744756417/100000000000000 : ℝ)*(upper3) + (87151493/50000000000000 : ℝ)*(upper4) + (871118352970249/20000000000000 : ℝ)*(major0) + (871118352970249/20000000000000 : ℝ)*(major1) + (871118352970249/20000000000000 : ℝ)*(major2) + (368017104291339/6250000000000 : ℝ)*(sp0) + (588828901010811/10000000000000 : ℝ)*(sp1) + (5888289561513273/100000000000000 : ℝ)*(sp2) + (564575172027759/20000000000000 : ℝ)*(sp3) + (8513284461/50000000000000 : ℝ)*(sp4) + (1666772797/10000000000000 : ℝ)*(sp7) + (705723131966691/25000000000000 : ℝ)*(f.failure) + (2944145347615173/50000000000000 : ℝ)*(f.sum) + (21170550708191/3690000000000000000000000000 : ℝ)*base65 + (6694150472901088123/369000000000000000000000000000000 : ℝ)*base68 + (2789419826871088123/369000000000000000000000000000000 : ℝ)*base70 + (3574109435247088123/369000000000000000000000000000000 : ℝ)*base72 + (4620134332091/3690000000000000000000000000 : ℝ)*base73 + (4320371289897088123/369000000000000000000000000000000 : ℝ)*base76 + (863134057449088123/369000000000000000000000000000000 : ℝ)*base78 + (2029305385656088123/369000000000000000000000000000000 : ℝ)*base80 + (2331006843521/3690000000000000000000000000 : ℝ)*base81 + (1729321/500000000000000000000 : ℝ)*base90 + (1729321/500000000000000000000 : ℝ)*base92 + (1729321/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (707436754093076777573858027/153750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244301351/25000000000000 : ℝ)*(base19) + (117872067/12500000000000 : ℝ)*(base23) + (33278277/50000000000000 : ℝ)*(upper2) + (164767319/100000000000000 : ℝ)*(upper3) + (16694159/20000000000000 : ℝ)*(upper5) + (2193577478545933/50000000000000 : ℝ)*(major0) + (2193577478545933/50000000000000 : ℝ)*(major1) + (2193577478545933/50000000000000 : ℝ)*(major2) + (4363183729/25000000000000 : ℝ)*(sp1) + (21140521263/100000000000000 : ℝ)*(sp2) + (1482740221313619/25000000000000 : ℝ)*(sp4) + (1482735613828539/25000000000000 : ℝ)*(sp5) + (5930938801756677/100000000000000 : ℝ)*(sp6) + (2843348875555427/100000000000000 : ℝ)*(sp7) + (2843348875555427/100000000000000 : ℝ)*(f.failure) + (1482740221313619/25000000000000 : ℝ)*(f.sum) + (6719161966097/9225000000000000000000000000 : ℝ)*base65 + (12667828377110013991/922500000000000000000000000000000 : ℝ)*base68 + (15497243368655013991/922500000000000000000000000000000 : ℝ)*base70 + (11903973658722513991/922500000000000000000000000000000 : ℝ)*base72 + (7530793075861/4612500000000000000000000000 : ℝ)*base73 + (2584297137785013991/922500000000000000000000000000000 : ℝ)*base76 + (2132075407280013991/922500000000000000000000000000000 : ℝ)*base78 + (7933649065317513991/922500000000000000000000000000000 : ℝ)*base80 + (24687748094503/9225000000000000000000000000 : ℝ)*base82 + (15117463/2000000000000000000000 : ℝ)*base89 + (15117463/2000000000000000000000 : ℝ)*base91 + (15117463/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1331_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7379/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1331_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1331_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4037/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1331_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1331_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1331_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2145/512 : ℝ) ≤ p) (hpb : p ≤ (4291/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30859069/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4037/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9779/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5557/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1331_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

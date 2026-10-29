-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1425_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:51.93963+00:00
-- url     : https://prove2.me/submissions/d5b1fe55-950a-4af4-a68e-9601026c1bc7

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
theorem support_rectangle_w1425_s6_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-987189569/5000000000 : ℝ)*x 0 + (1081685997/2000000000 : ℝ)*x 1 + (1311703141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987189569/5000000000 : ℝ)^4385 ≤ (1505492261221/12500000000000 : ℝ)^3361 := by
    have hnat : (987189569 : ℕ)^4385*12500000000000^3361 ≤ 1505492261221^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987189569 5000000000 1505492261221 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081685997/2000000000 : ℝ)^4385 ≤ (44848269486751/100000000000000 : ℝ)^3361 := by
    have hnat : (1081685997 : ℕ)^4385*100000000000000^3361 ≤ 44848269486751^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081685997 2000000000 44848269486751 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311703141/2500000000 : ℝ)^4385 ≤ (21553896205381/50000000000000 : ℝ)^3361 := by
    have hnat : (1311703141 : ℕ)^4385*50000000000000^3361 ≤ 21553896205381^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311703141 2500000000 21553896205381 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987189569/5000000000 : ℝ), (1081685997/2000000000 : ℝ), (1311703141/2500000000 : ℝ)] ![(1505492261221/12500000000000 : ℝ), (44848269486751/100000000000000 : ℝ), (21553896205381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987189569/5000000000 : ℝ)|^4385 ≤ (1505492261221/12500000000000 : ℝ)^3361
        have hw : |(-987189569/5000000000 : ℝ)|=(987189569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081685997/2000000000 : ℝ)|^4385 ≤ (44848269486751/100000000000000 : ℝ)^3361
        have hw : |(1081685997/2000000000 : ℝ)|=(1081685997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311703141/2500000000 : ℝ)|^4385 ≤ (21553896205381/50000000000000 : ℝ)^3361
        have hw : |(1311703141/2500000000 : ℝ)|=(1311703141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347412473/10000000000 : ℝ)*x 0 + (-51416599/250000000 : ℝ)*x 1 + (5246812529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347412473/10000000000 : ℝ)^4385 ≤ (5523659512481/12500000000000 : ℝ)^3361 := by
    have hnat : (5347412473 : ℕ)^4385*12500000000000^3361 ≤ 5523659512481^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347412473 10000000000 5523659512481 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51416599/250000000 : ℝ)^4385 ≤ (12702931842549/100000000000000 : ℝ)^3361 := by
    have hnat : (51416599 : ℕ)^4385*100000000000000^3361 ≤ 12702931842549^3361*250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51416599 250000000 12702931842549 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246812529/10000000000 : ℝ)^4385 ≤ (43107792035591/100000000000000 : ℝ)^3361 := by
    have hnat : (5246812529 : ℕ)^4385*100000000000000^3361 ≤ 43107792035591^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246812529 10000000000 43107792035591 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347412473/10000000000 : ℝ), (-51416599/250000000 : ℝ), (5246812529/10000000000 : ℝ)] ![(5523659512481/12500000000000 : ℝ), (12702931842549/100000000000000 : ℝ), (43107792035591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347412473/10000000000 : ℝ)|^4385 ≤ (5523659512481/12500000000000 : ℝ)^3361
        have hw : |(5347412473/10000000000 : ℝ)|=(5347412473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51416599/250000000 : ℝ)|^4385 ≤ (12702931842549/100000000000000 : ℝ)^3361
        have hw : |(-51416599/250000000 : ℝ)|=(51416599/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246812529/10000000000 : ℝ)|^4385 ≤ (43107792035591/100000000000000 : ℝ)^3361
        have hw : |(5246812529/10000000000 : ℝ)|=(5246812529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668426563/1250000000 : ℝ)*x 0 + (2623406261/5000000000 : ℝ)*x 1 + (-2056663929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668426563/1250000000 : ℝ)^4385 ≤ (44189276434071/100000000000000 : ℝ)^3361 := by
    have hnat : (668426563 : ℕ)^4385*100000000000000^3361 ≤ 44189276434071^3361*1250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668426563 1250000000 44189276434071 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623406261/5000000000 : ℝ)^4385 ≤ (43107791960557/100000000000000 : ℝ)^3361 := by
    have hnat : (2623406261 : ℕ)^4385*100000000000000^3361 ≤ 43107791960557^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623406261 5000000000 43107791960557 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056663929/10000000000 : ℝ)^4385 ≤ (12702931592743/100000000000000 : ℝ)^3361 := by
    have hnat : (2056663929 : ℕ)^4385*100000000000000^3361 ≤ 12702931592743^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056663929 10000000000 12702931592743 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668426563/1250000000 : ℝ), (2623406261/5000000000 : ℝ), (-2056663929/10000000000 : ℝ)] ![(44189276434071/100000000000000 : ℝ), (43107791960557/100000000000000 : ℝ), (12702931592743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668426563/1250000000 : ℝ)|^4385 ≤ (44189276434071/100000000000000 : ℝ)^3361
        have hw : |(668426563/1250000000 : ℝ)|=(668426563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623406261/5000000000 : ℝ)|^4385 ≤ (43107791960557/100000000000000 : ℝ)^3361
        have hw : |(2623406261/5000000000 : ℝ)|=(2623406261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056663929/10000000000 : ℝ)|^4385 ≤ (12702931592743/100000000000000 : ℝ)^3361
        have hw : |(-2056663929/10000000000 : ℝ)|=(2056663929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305374281/10000000000 : ℝ)*x 0 + (1033500653/2500000000 : ℝ)*x 1 + (2241561447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305374281/10000000000 : ℝ)^4385 ≤ (266437011671/800000000000 : ℝ)^3361 := by
    have hnat : (4305374281 : ℕ)^4385*800000000000^3361 ≤ 266437011671^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305374281 10000000000 266437011671 800000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033500653/2500000000 : ℝ)^4385 ≤ (15792829801201/50000000000000 : ℝ)^3361 := by
    have hnat : (1033500653 : ℕ)^4385*50000000000000^3361 ≤ 15792829801201^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033500653 2500000000 15792829801201 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241561447/5000000000 : ℝ)^4385 ≤ (702194278579/2000000000000 : ℝ)^3361 := by
    have hnat : (2241561447 : ℕ)^4385*2000000000000^3361 ≤ 702194278579^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241561447 5000000000 702194278579 2000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305374281/10000000000 : ℝ), (1033500653/2500000000 : ℝ), (2241561447/5000000000 : ℝ)] ![(266437011671/800000000000 : ℝ), (15792829801201/50000000000000 : ℝ), (702194278579/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305374281/10000000000 : ℝ)|^4385 ≤ (266437011671/800000000000 : ℝ)^3361
        have hw : |(4305374281/10000000000 : ℝ)|=(4305374281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033500653/2500000000 : ℝ)|^4385 ≤ (15792829801201/50000000000000 : ℝ)^3361
        have hw : |(1033500653/2500000000 : ℝ)|=(1033500653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241561447/5000000000 : ℝ)|^4385 ≤ (702194278579/2000000000000 : ℝ)^3361
        have hw : |(2241561447/5000000000 : ℝ)|=(2241561447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-493597527/2500000000 : ℝ)*x 0 + (5247395257/10000000000 : ℝ)*x 1 + (1351961141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493597527/2500000000 : ℝ)^4385 ≤ (37637579363/312500000000 : ℝ)^3361 := by
    have hnat : (493597527 : ℕ)^4385*312500000000^3361 ≤ 37637579363^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493597527 2500000000 37637579363 312500000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247395257/10000000000 : ℝ)^4385 ≤ (2694627406503/6250000000000 : ℝ)^3361 := by
    have hnat : (5247395257 : ℕ)^4385*6250000000000^3361 ≤ 2694627406503^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247395257 10000000000 2694627406503 6250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351961141/2500000000 : ℝ)^4385 ≤ (22420968044969/50000000000000 : ℝ)^3361 := by
    have hnat : (1351961141 : ℕ)^4385*50000000000000^3361 ≤ 22420968044969^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351961141 2500000000 22420968044969 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493597527/2500000000 : ℝ), (5247395257/10000000000 : ℝ), (1351961141/2500000000 : ℝ)] ![(37637579363/312500000000 : ℝ), (2694627406503/6250000000000 : ℝ), (22420968044969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493597527/2500000000 : ℝ)|^4385 ≤ (37637579363/312500000000 : ℝ)^3361
        have hw : |(-493597527/2500000000 : ℝ)|=(493597527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247395257/10000000000 : ℝ)|^4385 ≤ (2694627406503/6250000000000 : ℝ)^3361
        have hw : |(5247395257/10000000000 : ℝ)|=(5247395257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351961141/2500000000 : ℝ)|^4385 ≤ (22420968044969/50000000000000 : ℝ)^3361
        have hw : |(1351961141/2500000000 : ℝ)|=(1351961141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305413171/10000000000 : ℝ)*x 0 + (-1895632173/10000000000 : ℝ)*x 1 + (5407843887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305413171/10000000000 : ℝ)^4385 ≤ (43737008494981/100000000000000 : ℝ)^3361 := by
    have hnat : (5305413171 : ℕ)^4385*100000000000000^3361 ≤ 43737008494981^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305413171 10000000000 43737008494981 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895632173/10000000000 : ℝ)^4385 ≤ (91368501721/800000000000 : ℝ)^3361 := by
    have hnat : (1895632173 : ℕ)^4385*800000000000^3361 ≤ 91368501721^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895632173 10000000000 91368501721 800000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407843887/10000000000 : ℝ)^4385 ≤ (44841928765911/100000000000000 : ℝ)^3361 := by
    have hnat : (5407843887 : ℕ)^4385*100000000000000^3361 ≤ 44841928765911^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407843887 10000000000 44841928765911 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305413171/10000000000 : ℝ), (-1895632173/10000000000 : ℝ), (5407843887/10000000000 : ℝ)] ![(43737008494981/100000000000000 : ℝ), (91368501721/800000000000 : ℝ), (44841928765911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305413171/10000000000 : ℝ)|^4385 ≤ (43737008494981/100000000000000 : ℝ)^3361
        have hw : |(5305413171/10000000000 : ℝ)|=(5305413171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895632173/10000000000 : ℝ)|^4385 ≤ (91368501721/800000000000 : ℝ)^3361
        have hw : |(-1895632173/10000000000 : ℝ)|=(1895632173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407843887/10000000000 : ℝ)|^4385 ≤ (44841928765911/100000000000000 : ℝ)^3361
        have hw : |(5407843887/10000000000 : ℝ)|=(5407843887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663176597/1250000000 : ℝ)*x 0 + (5407844169/10000000000 : ℝ)*x 1 + (-1895632327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663176597/1250000000 : ℝ)^4385 ≤ (8747400849311/20000000000000 : ℝ)^3361 := by
    have hnat : (663176597 : ℕ)^4385*20000000000000^3361 ≤ 8747400849311^3361*1250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663176597 1250000000 8747400849311 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407844169/10000000000 : ℝ)^4385 ≤ (44841931816687/100000000000000 : ℝ)^3361 := by
    have hnat : (5407844169 : ℕ)^4385*100000000000000^3361 ≤ 44841931816687^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407844169 10000000000 44841931816687 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895632327/10000000000 : ℝ)^4385 ≤ (2855265981413/25000000000000 : ℝ)^3361 := by
    have hnat : (1895632327 : ℕ)^4385*25000000000000^3361 ≤ 2855265981413^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895632327 10000000000 2855265981413 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663176597/1250000000 : ℝ), (5407844169/10000000000 : ℝ), (-1895632327/10000000000 : ℝ)] ![(8747400849311/20000000000000 : ℝ), (44841931816687/100000000000000 : ℝ), (2855265981413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663176597/1250000000 : ℝ)|^4385 ≤ (8747400849311/20000000000000 : ℝ)^3361
        have hw : |(663176597/1250000000 : ℝ)|=(663176597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407844169/10000000000 : ℝ)|^4385 ≤ (44841931816687/100000000000000 : ℝ)^3361
        have hw : |(5407844169/10000000000 : ℝ)|=(5407844169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895632327/10000000000 : ℝ)|^4385 ≤ (2855265981413/25000000000000 : ℝ)^3361
        have hw : |(-1895632327/10000000000 : ℝ)|=(1895632327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s6_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4305398717/10000000000 : ℝ)*x 0 + (7002913/15625000 : ℝ)*x 1 + (2067633903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4305398717/10000000000 : ℝ)^4385 ≤ (2081554567321/6250000000000 : ℝ)^3361 := by
    have hnat : (4305398717 : ℕ)^4385*6250000000000^3361 ≤ 2081554567321^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305398717 10000000000 2081554567321 6250000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7002913/15625000 : ℝ)^4385 ≤ (3509685490773/10000000000000 : ℝ)^3361 := by
    have hnat : (7002913 : ℕ)^4385*10000000000000^3361 ≤ 3509685490773^3361*15625000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7002913 15625000 3509685490773 10000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067633903/5000000000 : ℝ)^4385 ≤ (6319654400031/20000000000000 : ℝ)^3361 := by
    have hnat : (2067633903 : ℕ)^4385*20000000000000^3361 ≤ 6319654400031^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067633903 5000000000 6319654400031 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4305398717/10000000000 : ℝ), (7002913/15625000 : ℝ), (2067633903/5000000000 : ℝ)] ![(2081554567321/6250000000000 : ℝ), (3509685490773/10000000000000 : ℝ), (6319654400031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4305398717/10000000000 : ℝ)|^4385 ≤ (2081554567321/6250000000000 : ℝ)^3361
        have hw : |(4305398717/10000000000 : ℝ)|=(4305398717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7002913/15625000 : ℝ)|^4385 ≤ (3509685490773/10000000000000 : ℝ)^3361
        have hw : |(7002913/15625000 : ℝ)|=(7002913/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2067633903/5000000000 : ℝ)|^4385 ≤ (6319654400031/20000000000000 : ℝ)^3361
        have hw : |(2067633903/5000000000 : ℝ)|=(2067633903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (354/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (354/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (354/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (354/3125 : ℝ) ^ (137/32 : ℝ) ≤ (8924698640111071/100000000000000000000 : ℝ) := by
    have hpowers : (354/3125 : ℝ)^137 ≤ (8924698640111071/100000000000000000000 : ℝ)^32 := by
      have hnat : (354 : ℕ)^137*100000000000000000000^32 ≤ 8924698640111071^32*3125^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        354 3125 8924698640111071 100000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (354/3125 : ℝ)) (X := (8924698640111071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (137/32 : ℝ) ≤ (27702884625497953/100000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^137 ≤ (27702884625497953/100000000000000000000 : ℝ)^32 := by
      have hnat : (14759 : ℕ)^137*100000000000000000000^32 ≤ 27702884625497953^32*100000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 27702884625497953 100000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (27702884625497953/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008924698640111071/50000000000000000000 : ℝ) ≤ (1000041689171369/1000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50008924698640111071/50000000000000000000 : ℝ)^32 ≤ (1000041689171369/1000000000000000 : ℝ)^137 := by
      have hnat : (50008924698640111071 : ℕ)^32*1000000000000000^137 ≤ 1000041689171369^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008924698640111071 50000000000000000000 1000041689171369 1000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000041689171369/1000000000000000 : ℝ)) (X := (50008924698640111071/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (1563072305988525141/1562500000000000000 : ℝ) ≤ (10000855414733627/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (1563072305988525141/1562500000000000000 : ℝ)^32 ≤ (10000855414733627/10000000000000000 : ℝ)^137 := by
      have hnat : (1563072305988525141 : ℕ)^32*10000000000000000^137 ≤ 10000855414733627^137*1562500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563072305988525141 1562500000000000000 10000855414733627 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000855414733627/10000000000000000 : ℝ)) (X := (1563072305988525141/1562500000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027702884625497953/50000000000000000000 : ℝ) ≤ (2500323484438391/2500000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50027702884625497953/50000000000000000000 : ℝ)^32 ≤ (2500323484438391/2500000000000000 : ℝ)^137 := by
      have hnat : (50027702884625497953 : ℕ)^32*2500000000000000^137 ≤ 2500323484438391^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027702884625497953 50000000000000000000 2500323484438391 2500000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500323484438391/2500000000000000 : ℝ)) (X := (50027702884625497953/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8924698640111071/100000000000000000000 : ℝ) ≤ ((17150747588964988859/17155000000000000000 : ℝ)+2*(438523019937/343100000000000 : ℝ)*(354/3125 : ℝ))^(137/32 : ℝ) := by
    rw [show (17150747588964988859/17155000000000000000 : ℝ)+2*(438523019937/343100000000000 : ℝ)*(354/3125 : ℝ)=(1000041689171369/1000000000000000 : ℝ) by norm_num, show 1+2*(8924698640111071/100000000000000000000 : ℝ)=(50008924698640111071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27702884625497953/100000000000000000000 : ℝ)+(8924698640111071/100000000000000000000 : ℝ) ≤ ((17150747588964988859/17155000000000000000 : ℝ)+(438523019937/343100000000000 : ℝ)*((14759/100000 : ℝ)+(354/3125 : ℝ)))^(137/32 : ℝ) := by
    rw [show (17150747588964988859/17155000000000000000 : ℝ)+(438523019937/343100000000000 : ℝ)*((14759/100000 : ℝ)+(354/3125 : ℝ))=(10000855414733627/10000000000000000 : ℝ) by norm_num, show 1+(27702884625497953/100000000000000000000 : ℝ)+(8924698640111071/100000000000000000000 : ℝ)=(1563072305988525141/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27702884625497953/100000000000000000000 : ℝ) ≤ ((17150747588964988859/17155000000000000000 : ℝ)+2*(438523019937/343100000000000 : ℝ)*(14759/100000 : ℝ))^(137/32 : ℝ) := by
    rw [show (17150747588964988859/17155000000000000000 : ℝ)+2*(438523019937/343100000000000 : ℝ)*(14759/100000 : ℝ)=(2500323484438391/2500000000000000 : ℝ) by norm_num, show 1+2*(27702884625497953/100000000000000000000 : ℝ)=(50027702884625497953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17150747588964988859/17155000000000000000 : ℝ)*(X 1 0+X 2 0)+(438523019937/343100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17150747588964988859/17155000000000000000 : ℝ)) (alpha := (438523019937/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17150747588964988859/17155000000000000000 : ℝ)*(X 0 1+X 2 1)+(438523019937/343100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17150747588964988859/17155000000000000000 : ℝ)) (alpha := (438523019937/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17150747588964988859/17155000000000000000 : ℝ)*(X 0 2+X 1 2)+(438523019937/343100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (354/3125 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17150747588964988859/17155000000000000000 : ℝ)) (alpha := (438523019937/343100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987189569/5000000000 : ℝ)*X 0 0+(1081685997/2000000000 : ℝ)*X 0 1+(1311703141/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347412473/10000000000 : ℝ)*X 1 0+(-51416599/250000000 : ℝ)*X 1 1+(5246812529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668426563/1250000000 : ℝ)*X 2 0+(2623406261/5000000000 : ℝ)*X 2 1+(-2056663929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4305374281/10000000000 : ℝ)*X 0 0+(1033500653/2500000000 : ℝ)*X 0 1+(2241561447/5000000000 : ℝ)*X 0 2+(4305374281/10000000000 : ℝ)*X 1 0+(1033500653/2500000000 : ℝ)*X 1 1+(2241561447/5000000000 : ℝ)*X 1 2+(4305374281/10000000000 : ℝ)*X 2 0+(1033500653/2500000000 : ℝ)*X 2 1+(2241561447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-493597527/2500000000 : ℝ)*X 0 0+(5247395257/10000000000 : ℝ)*X 0 1+(1351961141/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305413171/10000000000 : ℝ)*X 1 0+(-1895632173/10000000000 : ℝ)*X 1 1+(5407843887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663176597/1250000000 : ℝ)*X 2 0+(5407844169/10000000000 : ℝ)*X 2 1+(-1895632327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4305398717/10000000000 : ℝ)*X 0 0+(7002913/15625000 : ℝ)*X 0 1+(2067633903/5000000000 : ℝ)*X 0 2+(4305398717/10000000000 : ℝ)*X 1 0+(7002913/15625000 : ℝ)*X 1 1+(2067633903/5000000000 : ℝ)*X 1 2+(4305398717/10000000000 : ℝ)*X 2 0+(7002913/15625000 : ℝ)*X 2 1+(2067633903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1501392755551273387964423859/428875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (745520127/100000000000000 : ℝ)*(base19) + (17689621/2500000000000 : ℝ)*(base23) + (39466751/100000000000000 : ℝ)*(lower2) + (17978899/20000000000000 : ℝ)*(upper3) + (329017/400000000000 : ℝ)*(upper5) + (4525918791678333/100000000000000 : ℝ)*(major0) + (4525918791678333/100000000000000 : ℝ)*(major1) + (4525918791678333/100000000000000 : ℝ)*(major2) + (618746584305833/10000000000000 : ℝ)*(sp0) + (618748017584653/10000000000000 : ℝ)*(sp1) + (773435026722727/12500000000000 : ℝ)*(sp2) + (1432174567810097/50000000000000 : ℝ)*(sp3) + (15078308327/100000000000000 : ℝ)*(sp4) + (740967747/10000000000000 : ℝ)*(sp7) + (11188892755069/390625000000 : ℝ)*(f.failure) + (6187480921366657/100000000000000 : ℝ)*(f.sum) + (135941498323581/17155000000000000000000000000 : ℝ)*base65 + (2033926117255757953/1715500000000000000000000000000000 : ℝ)*base68 + (9592278847245742047/1715500000000000000000000000000000 : ℝ)*base69 + (32360377023200742047/1715500000000000000000000000000000 : ℝ)*base71 + (13916770808181/17155000000000000000000000000 : ℝ)*base73 + (12554206556604742047/1715500000000000000000000000000000 : ℝ)*base75 + (35533265339503742047/1715500000000000000000000000000000 : ℝ)*base77 + (7563833432767742047/1715500000000000000000000000000000 : ℝ)*base79 + (39536410396261/17155000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (32189/7812500000000000000 : ℝ)*base90 + (32189/7812500000000000000 : ℝ)*base92 + (32189/7812500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1395019564292386183398225249/214437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1036132187/100000000000000 : ℝ)*(base19) + (1104511321/100000000000000 : ℝ)*(base23) + (108745019/100000000000000 : ℝ)*(lower1) + (8518067/3125000000000 : ℝ)*(lower4) + (2562657/12500000000000 : ℝ)*(upper5) + (1139710140960921/25000000000000 : ℝ)*(major0) + (1139710140960921/25000000000000 : ℝ)*(major1) + (1139710140960921/25000000000000 : ℝ)*(major2) + (106493663/3125000000000 : ℝ)*(sp0) + (294141173/12500000000000 : ℝ)*(sp2) + (3116242738526947/50000000000000 : ℝ)*(sp4) + (6232487848718923/100000000000000 : ℝ)*(sp5) + (3116242713605203/50000000000000 : ℝ)*(sp6) + (1442596012993401/50000000000000 : ℝ)*(sp7) + (1442596012993401/50000000000000 : ℝ)*(f.failure) + (623248888485111/10000000000000 : ℝ)*(f.sum) + (45440025152719/8577500000000000000000000000 : ℝ)*base65 + (7034777430530979139/428875000000000000000000000000000 : ℝ)*base67 + (7393898787816729139/428875000000000000000000000000000 : ℝ)*base69 + (5801135343958604139/428875000000000000000000000000000 : ℝ)*base71 + (13448859971953/17155000000000000000000000000 : ℝ)*base73 + (10545778505705354139/428875000000000000000000000000000 : ℝ)*base75 + (2368921731067479139/428875000000000000000000000000000 : ℝ)*base77 + (5165883191472979139/428875000000000000000000000000000 : ℝ)*base79 + (16139806321619/8577500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1812189/250000000000000000000 : ℝ)*base90 + (1812189/250000000000000000000 : ℝ)*base92 + (1812189/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1425_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1425_s7_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673702567/5000000000 : ℝ)*x 0 + (5246839723/10000000000 : ℝ)*x 1 + (-1028318803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673702567/5000000000 : ℝ)^4385 ≤ (44189196975329/100000000000000 : ℝ)^3361 := by
    have hnat : (2673702567 : ℕ)^4385*100000000000000^3361 ≤ 44189196975329^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673702567 5000000000 44189196975329 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246839723/10000000000 : ℝ)^4385 ≤ (10777020883259/25000000000000 : ℝ)^3361 := by
    have hnat : (5246839723 : ℕ)^4385*25000000000000^3361 ≤ 10777020883259^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246839723 10000000000 10777020883259 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028318803/5000000000 : ℝ)^4385 ≤ (2540543895073/20000000000000 : ℝ)^3361 := by
    have hnat : (1028318803 : ℕ)^4385*20000000000000^3361 ≤ 2540543895073^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028318803 5000000000 2540543895073 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673702567/5000000000 : ℝ), (5246839723/10000000000 : ℝ), (-1028318803/5000000000 : ℝ)] ![(44189196975329/100000000000000 : ℝ), (10777020883259/25000000000000 : ℝ), (2540543895073/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673702567/5000000000 : ℝ)|^4385 ≤ (44189196975329/100000000000000 : ℝ)^3361
        have hw : |(2673702567/5000000000 : ℝ)|=(2673702567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246839723/10000000000 : ℝ)|^4385 ≤ (10777020883259/25000000000000 : ℝ)^3361
        have hw : |(5246839723/10000000000 : ℝ)|=(5246839723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028318803/5000000000 : ℝ)|^4385 ≤ (2540543895073/20000000000000 : ℝ)^3361
        have hw : |(-1028318803/5000000000 : ℝ)|=(1028318803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s7_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1974393231/10000000000 : ℝ)*x 0 + (5247422041/10000000000 : ℝ)*x 1 + (5407815727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1974393231/10000000000 : ℝ)^4385 ≤ (3011012562763/25000000000000 : ℝ)^3361 := by
    have hnat : (1974393231 : ℕ)^4385*25000000000000^3361 ≤ 3011012562763^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974393231 10000000000 3011012562763 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247422041/10000000000 : ℝ)^4385 ≤ (2155716280817/5000000000000 : ℝ)^3361 := by
    have hnat : (5247422041 : ℕ)^4385*5000000000000^3361 ≤ 2155716280817^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247422041 10000000000 2155716280817 5000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407815727/10000000000 : ℝ)^4385 ≤ (140130075379/312500000000 : ℝ)^3361 := by
    have hnat : (5407815727 : ℕ)^4385*312500000000^3361 ≤ 140130075379^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407815727 10000000000 140130075379 312500000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1974393231/10000000000 : ℝ), (5247422041/10000000000 : ℝ), (5407815727/10000000000 : ℝ)] ![(3011012562763/25000000000000 : ℝ), (2155716280817/5000000000000 : ℝ), (140130075379/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1974393231/10000000000 : ℝ)|^4385 ≤ (3011012562763/25000000000000 : ℝ)^3361
        have hw : |(-1974393231/10000000000 : ℝ)|=(1974393231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247422041/10000000000 : ℝ)|^4385 ≤ (2155716280817/5000000000000 : ℝ)^3361
        have hw : |(5247422041/10000000000 : ℝ)|=(5247422041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407815727/10000000000 : ℝ)|^4385 ≤ (140130075379/312500000000 : ℝ)^3361
        have hw : |(5407815727/10000000000 : ℝ)|=(5407815727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s7_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331588749/625000000 : ℝ)*x 0 + (-189566163/1000000000 : ℝ)*x 1 + (540781571/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331588749/625000000 : ℝ)^4385 ≤ (1749483270891/4000000000000 : ℝ)^3361 := by
    have hnat : (331588749 : ℕ)^4385*4000000000000^3361 ≤ 1749483270891^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331588749 625000000 1749483270891 4000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189566163/1000000000 : ℝ)^4385 ≤ (11421294264213/100000000000000 : ℝ)^3361 := by
    have hnat : (189566163 : ℕ)^4385*100000000000000^3361 ≤ 11421294264213^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189566163 1000000000 11421294264213 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540781571/1000000000 : ℝ)^4385 ≤ (5605202992171/12500000000000 : ℝ)^3361 := by
    have hnat : (540781571 : ℕ)^4385*12500000000000^3361 ≤ 5605202992171^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540781571 1000000000 5605202992171 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331588749/625000000 : ℝ), (-189566163/1000000000 : ℝ), (540781571/1000000000 : ℝ)] ![(1749483270891/4000000000000 : ℝ), (11421294264213/100000000000000 : ℝ), (5605202992171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331588749/625000000 : ℝ)|^4385 ≤ (1749483270891/4000000000000 : ℝ)^3361
        have hw : |(331588749/625000000 : ℝ)|=(331588749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189566163/1000000000 : ℝ)|^4385 ≤ (11421294264213/100000000000000 : ℝ)^3361
        have hw : |(-189566163/1000000000 : ℝ)|=(189566163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540781571/1000000000 : ℝ)|^4385 ≤ (5605202992171/12500000000000 : ℝ)^3361
        have hw : |(540781571/1000000000 : ℝ)|=(540781571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s7_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652710003/5000000000 : ℝ)*x 0 + (5407815701/10000000000 : ℝ)*x 1 + (-947830807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652710003/5000000000 : ℝ)^4385 ≤ (683391906389/1562500000000 : ℝ)^3361 := by
    have hnat : (2652710003 : ℕ)^4385*1562500000000^3361 ≤ 683391906389^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652710003 5000000000 683391906389 1562500000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407815701/10000000000 : ℝ)^4385 ≤ (44841623840003/100000000000000 : ℝ)^3361 := by
    have hnat : (5407815701 : ℕ)^4385*100000000000000^3361 ≤ 44841623840003^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407815701 10000000000 44841623840003 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947830807/5000000000 : ℝ)^4385 ≤ (11421294138443/100000000000000 : ℝ)^3361 := by
    have hnat : (947830807 : ℕ)^4385*100000000000000^3361 ≤ 11421294138443^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947830807 5000000000 11421294138443 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652710003/5000000000 : ℝ), (5407815701/10000000000 : ℝ), (-947830807/5000000000 : ℝ)] ![(683391906389/1562500000000 : ℝ), (44841623840003/100000000000000 : ℝ), (11421294138443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652710003/5000000000 : ℝ)|^4385 ≤ (683391906389/1562500000000 : ℝ)^3361
        have hw : |(2652710003/5000000000 : ℝ)|=(2652710003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407815701/10000000000 : ℝ)|^4385 ≤ (44841623840003/100000000000000 : ℝ)^3361
        have hw : |(5407815701/10000000000 : ℝ)|=(5407815701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947830807/5000000000 : ℝ)|^4385 ≤ (11421294138443/100000000000000 : ℝ)^3361
        have hw : |(-947830807/5000000000 : ℝ)|=(947830807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_s7_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861080137/2000000000 : ℝ)*x 0 + (280112761/625000000 : ℝ)*x 1 + (82706549/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861080137/2000000000 : ℝ)^4385 ≤ (8326223234757/25000000000000 : ℝ)^3361 := by
    have hnat : (861080137 : ℕ)^4385*25000000000000^3361 ≤ 8326223234757^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861080137 2000000000 8326223234757 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280112761/625000000 : ℝ)^4385 ≤ (35096240435867/100000000000000 : ℝ)^3361 := by
    have hnat : (280112761 : ℕ)^4385*100000000000000^3361 ≤ 35096240435867^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280112761 625000000 35096240435867 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82706549/200000000 : ℝ)^4385 ≤ (31598866605069/100000000000000 : ℝ)^3361 := by
    have hnat : (82706549 : ℕ)^4385*100000000000000^3361 ≤ 31598866605069^3361*200000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82706549 200000000 31598866605069 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861080137/2000000000 : ℝ), (280112761/625000000 : ℝ), (82706549/200000000 : ℝ)] ![(8326223234757/25000000000000 : ℝ), (35096240435867/100000000000000 : ℝ), (31598866605069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861080137/2000000000 : ℝ)|^4385 ≤ (8326223234757/25000000000000 : ℝ)^3361
        have hw : |(861080137/2000000000 : ℝ)|=(861080137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280112761/625000000 : ℝ)|^4385 ≤ (35096240435867/100000000000000 : ℝ)^3361
        have hw : |(280112761/625000000 : ℝ)|=(280112761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82706549/200000000 : ℝ)|^4385 ≤ (31598866605069/100000000000000 : ℝ)^3361
        have hw : |(82706549/200000000 : ℝ)|=(82706549/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2833/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2833/25000 : ℝ) ^ (137/32 : ℝ) ≤ (8938198289487029/100000000000000000000 : ℝ) := by
    have hpowers : (2833/25000 : ℝ)^137 ≤ (8938198289487029/100000000000000000000 : ℝ)^32 := by
      have hnat : (2833 : ℕ)^137*100000000000000000000^32 ≤ 8938198289487029^32*25000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2833 25000 8938198289487029 100000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2833/25000 : ℝ)) (X := (8938198289487029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (137/32 : ℝ) ≤ (13835377504892677/50000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^137 ≤ (13835377504892677/50000000000000000000 : ℝ)^32 := by
      have hnat : (2951 : ℕ)^137*50000000000000000000^32 ≤ 13835377504892677^32*20000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 13835377504892677 50000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (13835377504892677/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008938198289487029/50000000000000000000 : ℝ) ≤ (10000417522267921/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50008938198289487029/50000000000000000000 : ℝ)^32 ≤ (10000417522267921/10000000000000000 : ℝ)^137 := by
      have hnat : (50008938198289487029 : ℕ)^32*10000000000000000^137 ≤ 10000417522267921^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008938198289487029 50000000000000000000 10000417522267921 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417522267921/10000000000000000 : ℝ)) (X := (50008938198289487029/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036608953299272383/100000000000000000000 : ℝ) ≤ (2000170995940643/2000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (100036608953299272383/100000000000000000000 : ℝ)^32 ≤ (2000170995940643/2000000000000000 : ℝ)^137 := by
      have hnat : (100036608953299272383 : ℕ)^32*2000000000000000^137 ≤ 2000170995940643^137*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036608953299272383 100000000000000000000 2000170995940643 2000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000170995940643/2000000000000000 : ℝ)) (X := (100036608953299272383/100000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013835377504892677/25000000000000000000 : ℝ) ≤ (10001292437138509/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (25013835377504892677/25000000000000000000 : ℝ)^32 ≤ (10001292437138509/10000000000000000 : ℝ)^137 := by
      have hnat : (25013835377504892677 : ℕ)^32*10000000000000000^137 ≤ 10001292437138509^137*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013835377504892677 25000000000000000000 10001292437138509 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001292437138509/10000000000000000 : ℝ)) (X := (25013835377504892677/25000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8938198289487029/100000000000000000000 : ℝ) ≤ ((11407171547803196789/11410000000000000000 : ℝ)+2*(72909572549/57050000000000 : ℝ)*(2833/25000 : ℝ))^(137/32 : ℝ) := by
    rw [show (11407171547803196789/11410000000000000000 : ℝ)+2*(72909572549/57050000000000 : ℝ)*(2833/25000 : ℝ)=(10000417522267921/10000000000000000 : ℝ) by norm_num, show 1+2*(8938198289487029/100000000000000000000 : ℝ)=(50008938198289487029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13835377504892677/50000000000000000000 : ℝ)+(8938198289487029/100000000000000000000 : ℝ) ≤ ((11407171547803196789/11410000000000000000 : ℝ)+(72909572549/57050000000000 : ℝ)*((2951/20000 : ℝ)+(2833/25000 : ℝ)))^(137/32 : ℝ) := by
    rw [show (11407171547803196789/11410000000000000000 : ℝ)+(72909572549/57050000000000 : ℝ)*((2951/20000 : ℝ)+(2833/25000 : ℝ))=(2000170995940643/2000000000000000 : ℝ) by norm_num, show 1+(13835377504892677/50000000000000000000 : ℝ)+(8938198289487029/100000000000000000000 : ℝ)=(100036608953299272383/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13835377504892677/50000000000000000000 : ℝ) ≤ ((11407171547803196789/11410000000000000000 : ℝ)+2*(72909572549/57050000000000 : ℝ)*(2951/20000 : ℝ))^(137/32 : ℝ) := by
    rw [show (11407171547803196789/11410000000000000000 : ℝ)+2*(72909572549/57050000000000 : ℝ)*(2951/20000 : ℝ)=(10001292437138509/10000000000000000 : ℝ) by norm_num, show 1+2*(13835377504892677/50000000000000000000 : ℝ)=(25013835377504892677/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11407171547803196789/11410000000000000000 : ℝ)*(X 1 0+X 2 0)+(72909572549/57050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (11407171547803196789/11410000000000000000 : ℝ)) (alpha := (72909572549/57050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11407171547803196789/11410000000000000000 : ℝ)*(X 0 1+X 2 1)+(72909572549/57050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (11407171547803196789/11410000000000000000 : ℝ)) (alpha := (72909572549/57050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11407171547803196789/11410000000000000000 : ℝ)*(X 0 2+X 1 2)+(72909572549/57050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (11407171547803196789/11410000000000000000 : ℝ)) (alpha := (72909572549/57050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2673702567/5000000000 : ℝ)*X 2 0+(5246839723/10000000000 : ℝ)*X 2 1+(-1028318803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1974393231/10000000000 : ℝ)*X 0 0+(5247422041/10000000000 : ℝ)*X 0 1+(5407815727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((331588749/625000000 : ℝ)*X 1 0+(-189566163/1000000000 : ℝ)*X 1 1+(540781571/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652710003/5000000000 : ℝ)*X 2 0+(5407815701/10000000000 : ℝ)*X 2 1+(-947830807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((861080137/2000000000 : ℝ)*X 0 0+(280112761/625000000 : ℝ)*X 0 1+(82706549/200000000 : ℝ)*X 0 2+(861080137/2000000000 : ℝ)*X 1 0+(280112761/625000000 : ℝ)*X 1 1+(82706549/200000000 : ℝ)*X 1 2+(861080137/2000000000 : ℝ)*X 2 0+(280112761/625000000 : ℝ)*X 2 1+(82706549/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1871333625387949141281/815000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381738519/100000000000000 : ℝ)*(base19) + (444342653/100000000000000 : ℝ)*(base23) + (30199167/25000000000000 : ℝ)*(lower1) + (21952897/50000000000000 : ℝ)*(upper3) + (13998941/100000000000000 : ℝ)*(lower4) + (45345683/100000000000000 : ℝ)*(upper5) + (4560422568075423/100000000000000 : ℝ)*(major0) + (4560422568075423/100000000000000 : ℝ)*(major1) + (4560422568075423/100000000000000 : ℝ)*(major2) + (654865569/50000000000000 : ℝ)*(sp0) + (48708217321987/781250000000 : ℝ)*(sp1) + (779331429434477/12500000000000 : ℝ)*(sp2) + (1246930012628109/20000000000000 : ℝ)*(sp3) + (1443096621199651/50000000000000 : ℝ)*(sp4) + (1443096621199651/50000000000000 : ℝ)*(f.failure) + (48708217321987/781250000000 : ℝ)*(f.sum) + (475671409511/101875000000000000000000000 : ℝ)*base66 + (12132826645077026179/163000000000000000000000000000000 : ℝ)*base68 + (127521984150973821/163000000000000000000000000000000 : ℝ)*base69 + (39507594958495026179/163000000000000000000000000000000 : ℝ)*base72 + (61797363621/407500000000000000000000000 : ℝ)*base73 + (12590631228806973821/163000000000000000000000000000000 : ℝ)*base75 + (1017709734170973821/163000000000000000000000000000000 : ℝ)*base77 + (1045813108086026179/163000000000000000000000000000000 : ℝ)*base80 + (180793405577/203750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1543439/250000000000000000000 : ℝ)*base90 + (1543439/250000000000000000000 : ℝ)*base92 + (1543439/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1425_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1425_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1425_box_0 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813434681/10000000000 : ℝ)*x 0 + (269321321/500000000 : ℝ)*x 1 + (33665171/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813434681/10000000000 : ℝ)^4385 ≤ (10779255970807/100000000000000 : ℝ)^3361 := by
    have hnat : (1813434681 : ℕ)^4385*100000000000000^3361 ≤ 10779255970807^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813434681 10000000000 10779255970807 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269321321/500000000 : ℝ)^4385 ≤ (4461036692537/10000000000000 : ℝ)^3361 := by
    have hnat : (269321321 : ℕ)^4385*10000000000000^3361 ≤ 4461036692537^3361*500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269321321 500000000 4461036692537 10000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33665171/62500000 : ℝ)^4385 ≤ (44610377082337/100000000000000 : ℝ)^3361 := by
    have hnat : (33665171 : ℕ)^4385*100000000000000^3361 ≤ 44610377082337^3361*62500000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33665171 62500000 44610377082337 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813434681/10000000000 : ℝ), (269321321/500000000 : ℝ), (33665171/62500000 : ℝ)] ![(10779255970807/100000000000000 : ℝ), (4461036692537/10000000000000 : ℝ), (44610377082337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813434681/10000000000 : ℝ)|^4385 ≤ (10779255970807/100000000000000 : ℝ)^3361
        have hw : |(-1813434681/10000000000 : ℝ)|=(1813434681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269321321/500000000 : ℝ)|^4385 ≤ (4461036692537/10000000000000 : ℝ)^3361
        have hw : |(269321321/500000000 : ℝ)|=(269321321/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33665171/62500000 : ℝ)|^4385 ≤ (44610377082337/100000000000000 : ℝ)^3361
        have hw : |(33665171/62500000 : ℝ)|=(33665171/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_1 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286034791/10000000000 : ℝ)*x 0 + (-487835747/2500000000 : ℝ)*x 1 + (5386426837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286034791/10000000000 : ℝ)^4385 ≤ (43528700232577/100000000000000 : ℝ)^3361 := by
    have hnat : (5286034791 : ℕ)^4385*100000000000000^3361 ≤ 43528700232577^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286034791 10000000000 43528700232577 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487835747/2500000000 : ℝ)^4385 ≤ (11860928331081/100000000000000 : ℝ)^3361 := by
    have hnat : (487835747 : ℕ)^4385*100000000000000^3361 ≤ 11860928331081^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487835747 2500000000 11860928331081 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386426837/10000000000 : ℝ)^4385 ≤ (44610371431173/100000000000000 : ℝ)^3361 := by
    have hnat : (5386426837 : ℕ)^4385*100000000000000^3361 ≤ 44610371431173^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386426837 10000000000 44610371431173 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286034791/10000000000 : ℝ), (-487835747/2500000000 : ℝ), (5386426837/10000000000 : ℝ)] ![(43528700232577/100000000000000 : ℝ), (11860928331081/100000000000000 : ℝ), (44610371431173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286034791/10000000000 : ℝ)|^4385 ≤ (43528700232577/100000000000000 : ℝ)^3361
        have hw : |(5286034791/10000000000 : ℝ)|=(5286034791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487835747/2500000000 : ℝ)|^4385 ≤ (11860928331081/100000000000000 : ℝ)^3361
        have hw : |(-487835747/2500000000 : ℝ)|=(487835747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386426837/10000000000 : ℝ)|^4385 ≤ (44610371431173/100000000000000 : ℝ)^3361
        have hw : |(5386426837/10000000000 : ℝ)|=(5386426837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_2 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528603521/1000000000 : ℝ)*x 0 + (1346606669/2500000000 : ℝ)*x 1 + (-975671319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528603521/1000000000 : ℝ)^4385 ≤ (21764352367057/50000000000000 : ℝ)^3361 := by
    have hnat : (528603521 : ℕ)^4385*50000000000000^3361 ≤ 21764352367057^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528603521 1000000000 21764352367057 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346606669/2500000000 : ℝ)^4385 ≤ (44610369691523/100000000000000 : ℝ)^3361 := by
    have hnat : (1346606669 : ℕ)^4385*100000000000000^3361 ≤ 44610369691523^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346606669 2500000000 44610369691523 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975671319/5000000000 : ℝ)^4385 ≤ (5930462777749/50000000000000 : ℝ)^3361 := by
    have hnat : (975671319 : ℕ)^4385*50000000000000^3361 ≤ 5930462777749^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975671319 5000000000 5930462777749 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528603521/1000000000 : ℝ), (1346606669/2500000000 : ℝ), (-975671319/5000000000 : ℝ)] ![(21764352367057/50000000000000 : ℝ), (44610369691523/100000000000000 : ℝ), (5930462777749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528603521/1000000000 : ℝ)|^4385 ≤ (21764352367057/50000000000000 : ℝ)^3361
        have hw : |(528603521/1000000000 : ℝ)|=(528603521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346606669/2500000000 : ℝ)|^4385 ≤ (44610369691523/100000000000000 : ℝ)^3361
        have hw : |(1346606669/2500000000 : ℝ)|=(1346606669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975671319/5000000000 : ℝ)|^4385 ≤ (5930462777749/50000000000000 : ℝ)^3361
        have hw : |(-975671319/5000000000 : ℝ)|=(975671319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_3 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4451753021/10000000000 : ℝ)*x 0 + (4235904137/10000000000 : ℝ)*x 1 + (26474399/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4451753021/10000000000 : ℝ)^4385 ≤ (34789532190023/100000000000000 : ℝ)^3361 := by
    have hnat : (4451753021 : ℕ)^4385*100000000000000^3361 ≤ 34789532190023^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4451753021 10000000000 34789532190023 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235904137/10000000000 : ℝ)^4385 ≤ (32605235389337/100000000000000 : ℝ)^3361 := by
    have hnat : (4235904137 : ℕ)^4385*100000000000000^3361 ≤ 32605235389337^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235904137 10000000000 32605235389337 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26474399/62500000 : ℝ)^4385 ≤ (32605232406711/100000000000000 : ℝ)^3361 := by
    have hnat : (26474399 : ℕ)^4385*100000000000000^3361 ≤ 32605232406711^3361*62500000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26474399 62500000 32605232406711 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4451753021/10000000000 : ℝ), (4235904137/10000000000 : ℝ), (26474399/62500000 : ℝ)] ![(34789532190023/100000000000000 : ℝ), (32605235389337/100000000000000 : ℝ), (32605232406711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4451753021/10000000000 : ℝ)|^4385 ≤ (34789532190023/100000000000000 : ℝ)^3361
        have hw : |(4451753021/10000000000 : ℝ)|=(4451753021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235904137/10000000000 : ℝ)|^4385 ≤ (32605235389337/100000000000000 : ℝ)^3361
        have hw : |(4235904137/10000000000 : ℝ)|=(4235904137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26474399/62500000 : ℝ)|^4385 ≤ (32605232406711/100000000000000 : ℝ)^3361
        have hw : |(26474399/62500000 : ℝ)|=(26474399/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_4 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213806913/1000000000 : ℝ)*x 0 + (5266465999/10000000000 : ℝ)*x 1 + (1316616537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213806913/1000000000 : ℝ)^4385 ≤ (6681418090683/50000000000000 : ℝ)^3361 := by
    have hnat : (213806913 : ℕ)^4385*50000000000000^3361 ≤ 6681418090683^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213806913 1000000000 6681418090683 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266465999/10000000000 : ℝ)^4385 ≤ (43318581105797/100000000000000 : ℝ)^3361 := by
    have hnat : (5266465999 : ℕ)^4385*100000000000000^3361 ≤ 43318581105797^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266465999 10000000000 43318581105797 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316616537/2500000000 : ℝ)^4385 ≤ (21659291352387/50000000000000 : ℝ)^3361 := by
    have hnat : (1316616537 : ℕ)^4385*50000000000000^3361 ≤ 21659291352387^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316616537 2500000000 21659291352387 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213806913/1000000000 : ℝ), (5266465999/10000000000 : ℝ), (1316616537/2500000000 : ℝ)] ![(6681418090683/50000000000000 : ℝ), (43318581105797/100000000000000 : ℝ), (21659291352387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213806913/1000000000 : ℝ)|^4385 ≤ (6681418090683/50000000000000 : ℝ)^3361
        have hw : |(-213806913/1000000000 : ℝ)|=(213806913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266465999/10000000000 : ℝ)|^4385 ≤ (43318581105797/100000000000000 : ℝ)^3361
        have hw : |(5266465999/10000000000 : ℝ)|=(5266465999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316616537/2500000000 : ℝ)|^4385 ≤ (21659291352387/50000000000000 : ℝ)^3361
        have hw : |(1316616537/2500000000 : ℝ)|=(1316616537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_5 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685001791/5000000000 : ℝ)*x 0 + (-125001407/625000000 : ℝ)*x 1 + (5266465603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685001791/5000000000 : ℝ)^4385 ≤ (44432995990323/100000000000000 : ℝ)^3361 := by
    have hnat : (2685001791 : ℕ)^4385*100000000000000^3361 ≤ 44432995990323^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685001791 5000000000 44432995990323 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125001407/625000000 : ℝ)^4385 ≤ (12248427144631/100000000000000 : ℝ)^3361 := by
    have hnat : (125001407 : ℕ)^4385*100000000000000^3361 ≤ 12248427144631^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125001407 625000000 12248427144631 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266465603/10000000000 : ℝ)^4385 ≤ (21659288428083/50000000000000 : ℝ)^3361 := by
    have hnat : (5266465603 : ℕ)^4385*50000000000000^3361 ≤ 21659288428083^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266465603 10000000000 21659288428083 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685001791/5000000000 : ℝ), (-125001407/625000000 : ℝ), (5266465603/10000000000 : ℝ)] ![(44432995990323/100000000000000 : ℝ), (12248427144631/100000000000000 : ℝ), (21659288428083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685001791/5000000000 : ℝ)|^4385 ≤ (44432995990323/100000000000000 : ℝ)^3361
        have hw : |(2685001791/5000000000 : ℝ)|=(2685001791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125001407/625000000 : ℝ)|^4385 ≤ (12248427144631/100000000000000 : ℝ)^3361
        have hw : |(-125001407/625000000 : ℝ)|=(125001407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266465603/10000000000 : ℝ)|^4385 ≤ (21659288428083/50000000000000 : ℝ)^3361
        have hw : |(5266465603/10000000000 : ℝ)|=(5266465603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_6 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671250369/1250000000 : ℝ)*x 0 + (2633233383/5000000000 : ℝ)*x 1 + (-10000109/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671250369/1250000000 : ℝ)^4385 ≤ (1777319567573/4000000000000 : ℝ)^3361 := by
    have hnat : (671250369 : ℕ)^4385*4000000000000^3361 ≤ 1777319567573^3361*1250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671250369 1250000000 1777319567573 4000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633233383/5000000000 : ℝ)^4385 ≤ (21659294668387/50000000000000 : ℝ)^3361 := by
    have hnat : (2633233383 : ℕ)^4385*50000000000000^3361 ≤ 21659294668387^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633233383 5000000000 21659294668387 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10000109/50000000 : ℝ)^4385 ≤ (2449684291151/20000000000000 : ℝ)^3361 := by
    have hnat : (10000109 : ℕ)^4385*20000000000000^3361 ≤ 2449684291151^3361*50000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10000109 50000000 2449684291151 20000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671250369/1250000000 : ℝ), (2633233383/5000000000 : ℝ), (-10000109/50000000 : ℝ)] ![(1777319567573/4000000000000 : ℝ), (21659294668387/50000000000000 : ℝ), (2449684291151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671250369/1250000000 : ℝ)|^4385 ≤ (1777319567573/4000000000000 : ℝ)^3361
        have hw : |(671250369/1250000000 : ℝ)|=(671250369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633233383/5000000000 : ℝ)|^4385 ≤ (21659294668387/50000000000000 : ℝ)^3361
        have hw : |(2633233383/5000000000 : ℝ)|=(2633233383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10000109/50000000 : ℝ)|^4385 ≤ (2449684291151/20000000000000 : ℝ)^3361
        have hw : |(-10000109/50000000 : ℝ)|=(10000109/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_7 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2078977977/5000000000 : ℝ)*x 0 + (4382751209/10000000000 : ℝ)*x 1 + (4382751817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078977977/5000000000 : ℝ)^4385 ≤ (31824643731061/100000000000000 : ℝ)^3361 := by
    have hnat : (2078977977 : ℕ)^4385*100000000000000^3361 ≤ 31824643731061^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078977977 5000000000 31824643731061 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4382751209/10000000000 : ℝ)^4385 ≤ (34087675043787/100000000000000 : ℝ)^3361 := by
    have hnat : (4382751209 : ℕ)^4385*100000000000000^3361 ≤ 34087675043787^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382751209 10000000000 34087675043787 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4382751817/10000000000 : ℝ)^4385 ≤ (17043840606681/50000000000000 : ℝ)^3361 := by
    have hnat : (4382751817 : ℕ)^4385*50000000000000^3361 ≤ 17043840606681^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382751817 10000000000 17043840606681 50000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078977977/5000000000 : ℝ), (4382751209/10000000000 : ℝ), (4382751817/10000000000 : ℝ)] ![(31824643731061/100000000000000 : ℝ), (34087675043787/100000000000000 : ℝ), (17043840606681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078977977/5000000000 : ℝ)|^4385 ≤ (31824643731061/100000000000000 : ℝ)^3361
        have hw : |(2078977977/5000000000 : ℝ)|=(2078977977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4382751209/10000000000 : ℝ)|^4385 ≤ (34087675043787/100000000000000 : ℝ)^3361
        have hw : |(4382751209/10000000000 : ℝ)|=(4382751209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4382751817/10000000000 : ℝ)|^4385 ≤ (17043840606681/50000000000000 : ℝ)^3361
        have hw : |(4382751817/10000000000 : ℝ)|=(4382751817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_8 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413939961/2000000000 : ℝ)*x 0 + (5183507973/10000000000 : ℝ)*x 1 + (5400403263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413939961/2000000000 : ℝ)^4385 ≤ (12808079456671/100000000000000 : ℝ)^3361 := by
    have hnat : (413939961 : ℕ)^4385*100000000000000^3361 ≤ 12808079456671^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413939961 2000000000 12808079456671 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183507973/10000000000 : ℝ)^4385 ≤ (42430470198837/100000000000000 : ℝ)^3361 := by
    have hnat : (5183507973 : ℕ)^4385*100000000000000^3361 ≤ 42430470198837^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183507973 10000000000 42430470198837 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400403263/10000000000 : ℝ)^4385 ≤ (44761450331973/100000000000000 : ℝ)^3361 := by
    have hnat : (5400403263 : ℕ)^4385*100000000000000^3361 ≤ 44761450331973^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400403263 10000000000 44761450331973 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413939961/2000000000 : ℝ), (5183507973/10000000000 : ℝ), (5400403263/10000000000 : ℝ)] ![(12808079456671/100000000000000 : ℝ), (42430470198837/100000000000000 : ℝ), (44761450331973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413939961/2000000000 : ℝ)|^4385 ≤ (12808079456671/100000000000000 : ℝ)^3361
        have hw : |(-413939961/2000000000 : ℝ)|=(413939961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183507973/10000000000 : ℝ)|^4385 ≤ (42430470198837/100000000000000 : ℝ)^3361
        have hw : |(5183507973/10000000000 : ℝ)|=(5183507973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400403263/10000000000 : ℝ)|^4385 ≤ (44761450331973/100000000000000 : ℝ)^3361
        have hw : |(5400403263/10000000000 : ℝ)|=(5400403263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_9 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638123861/5000000000 : ℝ)*x 0 + (-972772377/5000000000 : ℝ)*x 1 + (5400403223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638123861/5000000000 : ℝ)^4385 ≤ (43423582289187/100000000000000 : ℝ)^3361 := by
    have hnat : (2638123861 : ℕ)^4385*100000000000000^3361 ≤ 43423582289187^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638123861 5000000000 43423582289187 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972772377/5000000000 : ℝ)^4385 ≤ (2953741947601/25000000000000 : ℝ)^3361 := by
    have hnat : (972772377 : ℕ)^4385*25000000000000^3361 ≤ 2953741947601^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972772377 5000000000 2953741947601 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400403223/10000000000 : ℝ)^4385 ≤ (2238072494971/5000000000000 : ℝ)^3361 := by
    have hnat : (5400403223 : ℕ)^4385*5000000000000^3361 ≤ 2238072494971^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400403223 10000000000 2238072494971 5000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638123861/5000000000 : ℝ), (-972772377/5000000000 : ℝ), (5400403223/10000000000 : ℝ)] ![(43423582289187/100000000000000 : ℝ), (2953741947601/25000000000000 : ℝ), (2238072494971/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638123861/5000000000 : ℝ)|^4385 ≤ (43423582289187/100000000000000 : ℝ)^3361
        have hw : |(2638123861/5000000000 : ℝ)|=(2638123861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972772377/5000000000 : ℝ)|^4385 ≤ (2953741947601/25000000000000 : ℝ)^3361
        have hw : |(-972772377/5000000000 : ℝ)|=(972772377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400403223/10000000000 : ℝ)|^4385 ≤ (2238072494971/5000000000000 : ℝ)^3361
        have hw : |(5400403223/10000000000 : ℝ)|=(5400403223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_10 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211049903/400000000 : ℝ)*x 0 + (5400403511/10000000000 : ℝ)*x 1 + (-1945544561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211049903/400000000 : ℝ)^4385 ≤ (2171179035539/5000000000000 : ℝ)^3361 := by
    have hnat : (211049903 : ℕ)^4385*5000000000000^3361 ≤ 2171179035539^3361*400000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211049903 400000000 2171179035539 5000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400403511/10000000000 : ℝ)^4385 ≤ (44761453013799/100000000000000 : ℝ)^3361 := by
    have hnat : (5400403511 : ℕ)^4385*100000000000000^3361 ≤ 44761453013799^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400403511 10000000000 44761453013799 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1945544561/10000000000 : ℝ)^4385 ≤ (1476870782657/12500000000000 : ℝ)^3361 := by
    have hnat : (1945544561 : ℕ)^4385*12500000000000^3361 ≤ 1476870782657^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945544561 10000000000 1476870782657 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211049903/400000000 : ℝ), (5400403511/10000000000 : ℝ), (-1945544561/10000000000 : ℝ)] ![(2171179035539/5000000000000 : ℝ), (44761453013799/100000000000000 : ℝ), (1476870782657/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211049903/400000000 : ℝ)|^4385 ≤ (2171179035539/5000000000000 : ℝ)^3361
        have hw : |(211049903/400000000 : ℝ)|=(211049903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400403511/10000000000 : ℝ)|^4385 ≤ (44761453013799/100000000000000 : ℝ)^3361
        have hw : |(5400403511/10000000000 : ℝ)|=(5400403511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1945544561/10000000000 : ℝ)|^4385 ≤ (1476870782657/12500000000000 : ℝ)^3361
        have hw : |(-1945544561/10000000000 : ℝ)|=(1945544561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_11 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4485426223/10000000000 : ℝ)*x 0 + (263673767/625000000 : ℝ)*x 1 + (1054695073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485426223/10000000000 : ℝ)^4385 ≤ (8783312550489/25000000000000 : ℝ)^3361 := by
    have hnat : (4485426223 : ℕ)^4385*25000000000000^3361 ≤ 8783312550489^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485426223 10000000000 8783312550489 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263673767/625000000 : ℝ)^4385 ≤ (32433374792929/100000000000000 : ℝ)^3361 := by
    have hnat : (263673767 : ℕ)^4385*100000000000000^3361 ≤ 32433374792929^3361*625000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263673767 625000000 32433374792929 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054695073/2500000000 : ℝ)^4385 ≤ (32433374993531/100000000000000 : ℝ)^3361 := by
    have hnat : (1054695073 : ℕ)^4385*100000000000000^3361 ≤ 32433374993531^3361*2500000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054695073 2500000000 32433374993531 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485426223/10000000000 : ℝ), (263673767/625000000 : ℝ), (1054695073/2500000000 : ℝ)] ![(8783312550489/25000000000000 : ℝ), (32433374792929/100000000000000 : ℝ), (32433374993531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485426223/10000000000 : ℝ)|^4385 ≤ (8783312550489/25000000000000 : ℝ)^3361
        have hw : |(4485426223/10000000000 : ℝ)|=(4485426223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263673767/625000000 : ℝ)|^4385 ≤ (32433374792929/100000000000000 : ℝ)^3361
        have hw : |(263673767/625000000 : ℝ)|=(263673767/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054695073/2500000000 : ℝ)|^4385 ≤ (32433374993531/100000000000000 : ℝ)^3361
        have hw : |(1054695073/2500000000 : ℝ)|=(1054695073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_12 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1881990809/10000000000 : ℝ)*x 0 + (683419243/1250000000 : ℝ)*x 1 + (2627670933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1881990809/10000000000 : ℝ)^4385 ≤ (11313951689179/100000000000000 : ℝ)^3361 := by
    have hnat : (1881990809 : ℕ)^4385*100000000000000^3361 ≤ 11313951689179^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881990809 10000000000 11313951689179 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683419243/1250000000 : ℝ)^4385 ≤ (45486806184599/100000000000000 : ℝ)^3361 := by
    have hnat : (683419243 : ℕ)^4385*100000000000000^3361 ≤ 45486806184599^3361*1250000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683419243 1250000000 45486806184599 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627670933/5000000000 : ℝ)^4385 ≤ (345593936919/800000000000 : ℝ)^3361 := by
    have hnat : (2627670933 : ℕ)^4385*800000000000^3361 ≤ 345593936919^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627670933 5000000000 345593936919 800000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1881990809/10000000000 : ℝ), (683419243/1250000000 : ℝ), (2627670933/5000000000 : ℝ)] ![(11313951689179/100000000000000 : ℝ), (45486806184599/100000000000000 : ℝ), (345593936919/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1881990809/10000000000 : ℝ)|^4385 ≤ (11313951689179/100000000000000 : ℝ)^3361
        have hw : |(-1881990809/10000000000 : ℝ)|=(1881990809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683419243/1250000000 : ℝ)|^4385 ≤ (45486806184599/100000000000000 : ℝ)^3361
        have hw : |(683419243/1250000000 : ℝ)|=(683419243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627670933/5000000000 : ℝ)|^4385 ≤ (345593936919/800000000000 : ℝ)^3361
        have hw : |(2627670933/5000000000 : ℝ)|=(2627670933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_13 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377787607/10000000000 : ℝ)*x 0 + (-2004436649/10000000000 : ℝ)*x 1 + (2627671167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377787607/10000000000 : ℝ)^4385 ≤ (5564630614967/12500000000000 : ℝ)^3361 := by
    have hnat : (5377787607 : ℕ)^4385*12500000000000^3361 ≤ 5564630614967^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377787607 10000000000 5564630614967 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004436649/10000000000 : ℝ)^4385 ≤ (12283707930321/100000000000000 : ℝ)^3361 := by
    have hnat : (2004436649 : ℕ)^4385*100000000000000^3361 ≤ 12283707930321^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004436649 10000000000 12283707930321 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627671167/5000000000 : ℝ)^4385 ≤ (43199247133931/100000000000000 : ℝ)^3361 := by
    have hnat : (2627671167 : ℕ)^4385*100000000000000^3361 ≤ 43199247133931^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627671167 5000000000 43199247133931 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377787607/10000000000 : ℝ), (-2004436649/10000000000 : ℝ), (2627671167/5000000000 : ℝ)] ![(5564630614967/12500000000000 : ℝ), (12283707930321/100000000000000 : ℝ), (43199247133931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377787607/10000000000 : ℝ)|^4385 ≤ (5564630614967/12500000000000 : ℝ)^3361
        have hw : |(5377787607/10000000000 : ℝ)|=(5377787607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2004436649/10000000000 : ℝ)|^4385 ≤ (12283707930321/100000000000000 : ℝ)^3361
        have hw : |(-2004436649/10000000000 : ℝ)|=(2004436649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627671167/5000000000 : ℝ)|^4385 ≤ (43199247133931/100000000000000 : ℝ)^3361
        have hw : |(2627671167/5000000000 : ℝ)|=(2627671167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_14 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075557521/2000000000 : ℝ)*x 0 + (2627671207/5000000000 : ℝ)*x 1 + (-400887309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075557521/2000000000 : ℝ)^4385 ≤ (5564630612267/12500000000000 : ℝ)^3361 := by
    have hnat : (1075557521 : ℕ)^4385*12500000000000^3361 ≤ 5564630612267^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075557521 2000000000 5564630612267 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627671207/5000000000 : ℝ)^4385 ≤ (4319924799189/10000000000000 : ℝ)^3361 := by
    have hnat : (2627671207 : ℕ)^4385*10000000000000^3361 ≤ 4319924799189^3361*5000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627671207 5000000000 4319924799189 10000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400887309/2000000000 : ℝ)^4385 ≤ (3070926774701/25000000000000 : ℝ)^3361 := by
    have hnat : (400887309 : ℕ)^4385*25000000000000^3361 ≤ 3070926774701^3361*2000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400887309 2000000000 3070926774701 25000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075557521/2000000000 : ℝ), (2627671207/5000000000 : ℝ), (-400887309/2000000000 : ℝ)] ![(5564630612267/12500000000000 : ℝ), (4319924799189/10000000000000 : ℝ), (3070926774701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075557521/2000000000 : ℝ)|^4385 ≤ (5564630612267/12500000000000 : ℝ)^3361
        have hw : |(1075557521/2000000000 : ℝ)|=(1075557521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627671207/5000000000 : ℝ)|^4385 ≤ (4319924799189/10000000000000 : ℝ)^3361
        have hw : |(2627671207/5000000000 : ℝ)|=(2627671207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-400887309/2000000000 : ℝ)|^4385 ≤ (3070926774701/25000000000000 : ℝ)^3361
        have hw : |(-400887309/2000000000 : ℝ)|=(400887309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1425_box_15 (p : ℝ) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (413026237/1000000000 : ℝ)*x 0 + (87927149/200000000 : ℝ)*x 1 + (4396357893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413026237/1000000000 : ℝ)^4385 ≤ (31548380957403/100000000000000 : ℝ)^3361 := by
    have hnat : (413026237 : ℕ)^4385*100000000000000^3361 ≤ 31548380957403^3361*1000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413026237 1000000000 31548380957403 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87927149/200000000 : ℝ)^4385 ≤ (34225807266479/100000000000000 : ℝ)^3361 := by
    have hnat : (87927149 : ℕ)^4385*100000000000000^3361 ≤ 34225807266479^3361*200000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87927149 200000000 34225807266479 100000000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4396357893/10000000000 : ℝ)^4385 ≤ (4278226470749/12500000000000 : ℝ)^3361 := by
    have hnat : (4396357893 : ℕ)^4385*12500000000000^3361 ≤ 4278226470749^3361*10000000000^4385 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4396357893 10000000000 4278226470749 12500000000000 4385 3361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4385/1024 : ℝ)) 4385 3361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(413026237/1000000000 : ℝ), (87927149/200000000 : ℝ), (4396357893/10000000000 : ℝ)] ![(31548380957403/100000000000000 : ℝ), (34225807266479/100000000000000 : ℝ), (4278226470749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(413026237/1000000000 : ℝ)|^4385 ≤ (31548380957403/100000000000000 : ℝ)^3361
        have hw : |(413026237/1000000000 : ℝ)|=(413026237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(87927149/200000000 : ℝ)|^4385 ≤ (34225807266479/100000000000000 : ℝ)^3361
        have hw : |(87927149/200000000 : ℝ)|=(87927149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4396357893/10000000000 : ℝ)|^4385 ≤ (4278226470749/12500000000000 : ℝ)^3361
        have hw : |(4396357893/10000000000 : ℝ)|=(4396357893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1425_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62897/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11821/20000 : ℝ) ∧ (40213/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8467/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2833/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2833/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2833/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2833/25000 : ℝ) ^ (137/32 : ℝ) ≤ (8938198289487029/100000000000000000000 : ℝ) := by
    have hpowers : (2833/25000 : ℝ)^137 ≤ (8938198289487029/100000000000000000000 : ℝ)^32 := by
      have hnat : (2833 : ℕ)^137*100000000000000000000^32 ≤ 8938198289487029^32*25000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2833 25000 8938198289487029 100000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2833/25000 : ℝ)) (X := (8938198289487029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (137/32 : ℝ) ≤ (2766272707022171/10000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^137 ≤ (2766272707022171/10000000000000000000 : ℝ)^32 := by
      have hnat : (7377 : ℕ)^137*10000000000000000000^32 ≤ 2766272707022171^32*50000^137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 2766272707022171 10000000000000000000 137 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (2766272707022171/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008938198289487029/50000000000000000000 : ℝ) ≤ (10000417522267921/10000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (50008938198289487029/50000000000000000000 : ℝ)^32 ≤ (10000417522267921/10000000000000000 : ℝ)^137 := by
      have hnat : (50008938198289487029 : ℕ)^32*10000000000000000^137 ≤ 10000417522267921^137*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008938198289487029 50000000000000000000 10000417522267921 10000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000417522267921/10000000000000000 : ℝ)) (X := (50008938198289487029/50000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036600925359708739/100000000000000000000 : ℝ) ≤ (312526712257559/312500000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (100036600925359708739/100000000000000000000 : ℝ)^32 ≤ (312526712257559/312500000000000 : ℝ)^137 := by
      have hnat : (100036600925359708739 : ℕ)^32*312500000000000^137 ≤ 312526712257559^137*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036600925359708739 100000000000000000000 312526712257559 312500000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312526712257559/312500000000000 : ℝ)) (X := (100036600925359708739/100000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002766272707022171/5000000000000000000 : ℝ) ≤ (2000258412443171/2000000000000000 : ℝ) ^ (137/32 : ℝ) := by
    have hpowers : (5002766272707022171/5000000000000000000 : ℝ)^32 ≤ (2000258412443171/2000000000000000 : ℝ)^137 := by
      have hnat : (5002766272707022171 : ℕ)^32*2000000000000000^137 ≤ 2000258412443171^137*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002766272707022171 5000000000000000000 2000258412443171 2000000000000000 32 137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000258412443171/2000000000000000 : ℝ)) (X := (5002766272707022171/5000000000000000000 : ℝ)) (by norm_num) 137 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8938198289487029/100000000000000000000 : ℝ) ≤ ((17105759237255418787/17110000000000000000 : ℝ)+2*(437269973967/342200000000000 : ℝ)*(2833/25000 : ℝ))^(137/32 : ℝ) := by
    rw [show (17105759237255418787/17110000000000000000 : ℝ)+2*(437269973967/342200000000000 : ℝ)*(2833/25000 : ℝ)=(10000417522267921/10000000000000000 : ℝ) by norm_num, show 1+2*(8938198289487029/100000000000000000000 : ℝ)=(50008938198289487029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2766272707022171/10000000000000000000 : ℝ)+(8938198289487029/100000000000000000000 : ℝ) ≤ ((17105759237255418787/17110000000000000000 : ℝ)+(437269973967/342200000000000 : ℝ)*((7377/50000 : ℝ)+(2833/25000 : ℝ)))^(137/32 : ℝ) := by
    rw [show (17105759237255418787/17110000000000000000 : ℝ)+(437269973967/342200000000000 : ℝ)*((7377/50000 : ℝ)+(2833/25000 : ℝ))=(312526712257559/312500000000000 : ℝ) by norm_num, show 1+(2766272707022171/10000000000000000000 : ℝ)+(8938198289487029/100000000000000000000 : ℝ)=(100036600925359708739/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2766272707022171/10000000000000000000 : ℝ) ≤ ((17105759237255418787/17110000000000000000 : ℝ)+2*(437269973967/342200000000000 : ℝ)*(7377/50000 : ℝ))^(137/32 : ℝ) := by
    rw [show (17105759237255418787/17110000000000000000 : ℝ)+2*(437269973967/342200000000000 : ℝ)*(7377/50000 : ℝ)=(2000258412443171/2000000000000000 : ℝ) by norm_num, show 1+2*(2766272707022171/10000000000000000000 : ℝ)=(5002766272707022171/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17105759237255418787/17110000000000000000 : ℝ)*(X 1 0+X 2 0)+(437269973967/342200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (17105759237255418787/17110000000000000000 : ℝ)) (alpha := (437269973967/342200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17105759237255418787/17110000000000000000 : ℝ)*(X 0 1+X 2 1)+(437269973967/342200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (17105759237255418787/17110000000000000000 : ℝ)) (alpha := (437269973967/342200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17105759237255418787/17110000000000000000 : ℝ)*(X 0 2+X 1 2)+(437269973967/342200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (137/32 : ℝ)) (lo := (2833/25000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (17105759237255418787/17110000000000000000 : ℝ)) (alpha := (437269973967/342200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1813434681/10000000000 : ℝ)*X 0 0+(269321321/500000000 : ℝ)*X 0 1+(33665171/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286034791/10000000000 : ℝ)*X 1 0+(-487835747/2500000000 : ℝ)*X 1 1+(5386426837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((528603521/1000000000 : ℝ)*X 2 0+(1346606669/2500000000 : ℝ)*X 2 1+(-975671319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4451753021/10000000000 : ℝ)*X 0 0+(4235904137/10000000000 : ℝ)*X 0 1+(26474399/62500000 : ℝ)*X 0 2+(4451753021/10000000000 : ℝ)*X 1 0+(4235904137/10000000000 : ℝ)*X 1 1+(26474399/62500000 : ℝ)*X 1 2+(4451753021/10000000000 : ℝ)*X 2 0+(4235904137/10000000000 : ℝ)*X 2 1+(26474399/62500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213806913/1000000000 : ℝ)*X 0 0+(5266465999/10000000000 : ℝ)*X 0 1+(1316616537/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685001791/5000000000 : ℝ)*X 1 0+(-125001407/625000000 : ℝ)*X 1 1+(5266465603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671250369/1250000000 : ℝ)*X 2 0+(2633233383/5000000000 : ℝ)*X 2 1+(-10000109/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2078977977/5000000000 : ℝ)*X 0 0+(4382751209/10000000000 : ℝ)*X 0 1+(4382751817/10000000000 : ℝ)*X 0 2+(2078977977/5000000000 : ℝ)*X 1 0+(4382751209/10000000000 : ℝ)*X 1 1+(4382751817/10000000000 : ℝ)*X 1 2+(2078977977/5000000000 : ℝ)*X 2 0+(4382751209/10000000000 : ℝ)*X 2 1+(4382751817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-413939961/2000000000 : ℝ)*X 0 0+(5183507973/10000000000 : ℝ)*X 0 1+(5400403263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638123861/5000000000 : ℝ)*X 1 0+(-972772377/5000000000 : ℝ)*X 1 1+(5400403223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((211049903/400000000 : ℝ)*X 2 0+(5400403511/10000000000 : ℝ)*X 2 1+(-1945544561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4485426223/10000000000 : ℝ)*X 0 0+(263673767/625000000 : ℝ)*X 0 1+(1054695073/2500000000 : ℝ)*X 0 2+(4485426223/10000000000 : ℝ)*X 1 0+(263673767/625000000 : ℝ)*X 1 1+(1054695073/2500000000 : ℝ)*X 1 2+(4485426223/10000000000 : ℝ)*X 2 0+(263673767/625000000 : ℝ)*X 2 1+(1054695073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1881990809/10000000000 : ℝ)*X 0 0+(683419243/1250000000 : ℝ)*X 0 1+(2627670933/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377787607/10000000000 : ℝ)*X 1 0+(-2004436649/10000000000 : ℝ)*X 1 1+(2627671167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075557521/2000000000 : ℝ)*X 2 0+(2627671207/5000000000 : ℝ)*X 2 1+(-400887309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((413026237/1000000000 : ℝ)*X 0 0+(87927149/200000000 : ℝ)*X 0 1+(4396357893/10000000000 : ℝ)*X 0 2+(413026237/1000000000 : ℝ)*X 1 0+(87927149/200000000 : ℝ)*X 1 1+(4396357893/10000000000 : ℝ)*X 1 2+(413026237/1000000000 : ℝ)*X 2 0+(87927149/200000000 : ℝ)*X 2 1+(4396357893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1425_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62897/100000 : ℝ) ≤ (-1345156048696929262751742124821/2138750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36321053/50000000000000 : ℝ)*(lower1) + (85150237/100000000000000 : ℝ)*(lower2) + (153104627/100000000000000 : ℝ)*(lower3) + (22168597/100000000000000 : ℝ)*(lower4) + (7531111206139/250000000000 : ℝ)*(major0) + (7531111206139/250000000000 : ℝ)*(major1) + (7531111206139/250000000000 : ℝ)*(major2) + (2419642471/20000000000000 : ℝ)*(sp1) + (4139342552069647/100000000000000 : ℝ)*(sp4) + (1034832613464323/25000000000000 : ℝ)*(sp5) + (827811430671423/20000000000000 : ℝ)*(sp6) + (119154809465819/6250000000000 : ℝ)*(sp7) + (71349678133/25000000000000 : ℝ)*(sp14) + (34293629969/100000000000000 : ℝ)*(sp15) + (29789238204423/1562500000000 : ℝ)*(f.failure) + (4139342552069647/100000000000000 : ℝ)*(f.sum) + (3343921025419/427750000000000000000000000 : ℝ)*base66 + (25514183778589107/4277500000000000000000000000000 : ℝ)*base68 + (12745740013105893/4277500000000000000000000000000 : ℝ)*base69 + (15231742591379107/4277500000000000000000000000000 : ℝ)*base72 + (2912346803921/855500000000000000000000000 : ℝ)*base74 + (2386112146843393/4277500000000000000000000000000 : ℝ)*base75 + (17862861034381607/4277500000000000000000000000000 : ℝ)*base78 + (20743231314426607/4277500000000000000000000000000 : ℝ)*base80 + (602955607609/68440000000000000000000000 : ℝ)*base81 + (32147/7812500000000000000 : ℝ)*base90 + (32147/7812500000000000000 : ℝ)*base92 + (32147/7812500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (11821/20000 : ℝ) ≤ (505665979896971954706991901749497/855500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53920987/100000000000000 : ℝ)*(lower3) + (49004811/25000000000000 : ℝ)*(upper4) + (23024313/100000000000000 : ℝ)*(upper5) + (3083920146179259/100000000000000 : ℝ)*(major0) + (3083920146179259/100000000000000 : ℝ)*(major1) + (3083920146179259/100000000000000 : ℝ)*(major2) + (104909516447539/2500000000000 : ℝ)*(sp0) + (4196370457248127/100000000000000 : ℝ)*(sp1) + (262274442936063/6250000000000 : ℝ)*(sp2) + (975872847109739/50000000000000 : ℝ)*(sp3) + (239831893/25000000000000 : ℝ)*(sp7) + (1289389553/6250000000000 : ℝ)*(sp9) + (503967/100000000000000 : ℝ)*(sp10) + (2085915883/20000000000000 : ℝ)*(sp12) + (1951746653547049/100000000000000 : ℝ)*(f.failure) + (167855643499239/4000000000000 : ℝ)*(f.sum) + (57104992215957/17110000000000000000000000000 : ℝ)*base66 + (13771940693193011167/1711000000000000000000000000000000 : ℝ)*base68 + (13103060900433011167/1711000000000000000000000000000000 : ℝ)*base70 + (2751684746588011167/1711000000000000000000000000000000 : ℝ)*base72 + (148302054209807/17110000000000000000000000000 : ℝ)*base74 + (10756396020076011167/1711000000000000000000000000000000 : ℝ)*base76 + (11955021985900011167/1711000000000000000000000000000000 : ℝ)*base78 + (3234602759128011167/1711000000000000000000000000000000 : ℝ)*base80 + (100712318808377/17110000000000000000000000000 : ℝ)*base82 + (62861/500000000000000000000 : ℝ)*base90 + (62861/500000000000000000000 : ℝ)*base92 + (62861/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40213/50000 : ℝ) ≤ (688069507562927660218926663685749/855500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27439609/25000000000000 : ℝ)*(upper0) + (83463097/100000000000000 : ℝ)*(upper1) + (22650563/50000000000000 : ℝ)*(upper4) + (3392042660818509/100000000000000 : ℝ)*(major0) + (3392042660818509/100000000000000 : ℝ)*(major1) + (3392042660818509/100000000000000 : ℝ)*(major2) + (47906217137/50000000000000 : ℝ)*(sp1) + (42267234787/20000000000000 : ℝ)*(sp2) + (39377177399/100000000000000 : ℝ)*(sp3) + (514347047/10000000000000 : ℝ)*(sp4) + (4610519776220039/100000000000000 : ℝ)*(sp8) + (922085821451247/20000000000000 : ℝ)*(sp9) + (2305156791758287/50000000000000 : ℝ)*(sp10) + (1073355690495537/50000000000000 : ℝ)*(sp11) + (2146750758168473/100000000000000 : ℝ)*(f.failure) + (4610524919690509/100000000000000 : ℝ)*(f.sum) + (98720281730743/17110000000000000000000000000 : ℝ)*base65 + (4364435453791921417/1711000000000000000000000000000000 : ℝ)*base68 + (1177784046178921417/1711000000000000000000000000000000 : ℝ)*base70 + (18931399280121078583/1711000000000000000000000000000000 : ℝ)*base71 + (779309439145587/17110000000000000000000000000 : ℝ)*base74 + (8088204939564921417/1711000000000000000000000000000000 : ℝ)*base76 + (11608001040965078583/1711000000000000000000000000000000 : ℝ)*base77 + (90156988348558921417/1711000000000000000000000000000000 : ℝ)*base80 + (39612508487437/17110000000000000000000000000 : ℝ)*base82 + (1057597/500000000000000000000 : ℝ)*base90 + (1057597/500000000000000000000 : ℝ)*base92 + (1057597/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-8467/10000 : ℝ) ≤ (-72432836606812753016480674840791/85550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10880541/25000000000000 : ℝ)*(lower1) + (47341597/100000000000000 : ℝ)*(upper3) + (471673/50000000000000 : ℝ)*(lower4) + (149024853/100000000000000 : ℝ)*(upper5) + (685894589667369/20000000000000 : ℝ)*(major0) + (685894589667369/20000000000000 : ℝ)*(major1) + (685894589667369/20000000000000 : ℝ)*(major2) + (50030203/5000000000000 : ℝ)*(sp0) + (14673795021/25000000000000 : ℝ)*(sp7) + (4024595049/50000000000000 : ℝ)*(sp8) + (294794980253359/6250000000000 : ℝ)*(sp12) + (2358364366923951/50000000000000 : ℝ)*(sp13) + (2358364366923951/50000000000000 : ℝ)*(sp14) + (217038088596123/10000000000000 : ℝ)*(sp15) + (2170439581141313/100000000000000 : ℝ)*(f.failure) + (2358364366923951/50000000000000 : ℝ)*(f.sum) + (5806077756157/3422000000000000000000000000 : ℝ)*base66 + (469778913143411403/342200000000000000000000000000000 : ℝ)*base67 + (1701360573506588597/342200000000000000000000000000000 : ℝ)*base70 + (743120859385388597/342200000000000000000000000000000 : ℝ)*base72 + (1965749403147/3422000000000000000000000000 : ℝ)*base73 + (1565461178404588597/342200000000000000000000000000000 : ℝ)*base76 + (1609675355256588597/342200000000000000000000000000000 : ℝ)*base78 + (118884661360188597/342200000000000000000000000000000 : ℝ)*base80 + (23598293965793/3422000000000000000000000000 : ℝ)*base82 + (3220357/500000000000000000000 : ℝ)*base90 + (3220357/500000000000000000000 : ℝ)*base92 + (3220357/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1425_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2833/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62897/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11821/20000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8467/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1425_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1425_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62897/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11821/20000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8467/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1425_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1425_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1425_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (137/32 : ℝ) ≤ p) (hpb : p ≤ (4385/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7900411/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62897/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11821/20000 : ℝ) else (40213/50000 : ℝ) ≤ X j i ∧ X j i ≤ (8467/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1425_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

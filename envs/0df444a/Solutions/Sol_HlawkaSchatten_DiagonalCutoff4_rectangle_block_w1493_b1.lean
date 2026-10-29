-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1493_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:46.184233+00:00
-- url     : https://prove2.me/submissions/2aad8831-1d18-41e4-92b7-cfee81f42c8f

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
theorem support_rectangle_w1493_s3_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1895832081/10000000000 : ℝ)*x 0 + (5439782579/10000000000 : ℝ)*x 1 + (5212962717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1895832081/10000000000 : ℝ)^4483 ≤ (5793889899157/50000000000000 : ℝ)^3459 := by
    have hnat : (1895832081 : ℕ)^4483*50000000000000^3459 ≤ 5793889899157^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895832081 10000000000 5793889899157 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439782579/10000000000 : ℝ)^4483 ≤ (11356468237897/25000000000000 : ℝ)^3459 := by
    have hnat : (5439782579 : ℕ)^4483*25000000000000^3459 ≤ 11356468237897^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439782579 10000000000 11356468237897 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212962717/10000000000 : ℝ)^4483 ≤ (42986347231183/100000000000000 : ℝ)^3459 := by
    have hnat : (5212962717 : ℕ)^4483*100000000000000^3459 ≤ 42986347231183^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212962717 10000000000 42986347231183 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1895832081/10000000000 : ℝ), (5439782579/10000000000 : ℝ), (5212962717/10000000000 : ℝ)] ![(5793889899157/50000000000000 : ℝ), (11356468237897/25000000000000 : ℝ), (42986347231183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1895832081/10000000000 : ℝ)|^4483 ≤ (5793889899157/50000000000000 : ℝ)^3459
        have hw : |(-1895832081/10000000000 : ℝ)|=(1895832081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439782579/10000000000 : ℝ)|^4483 ≤ (11356468237897/25000000000000 : ℝ)^3459
        have hw : |(5439782579/10000000000 : ℝ)|=(5439782579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212962717/10000000000 : ℝ)|^4483 ≤ (42986347231183/100000000000000 : ℝ)^3459
        have hw : |(5212962717/10000000000 : ℝ)|=(5212962717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338421333/2500000000 : ℝ)*x 0 + (-503035421/2500000000 : ℝ)*x 1 + (5212963001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338421333/2500000000 : ℝ)^4483 ≤ (44496250233169/100000000000000 : ℝ)^3459 := by
    have hnat : (1338421333 : ℕ)^4483*100000000000000^3459 ≤ 44496250233169^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338421333 2500000000 44496250233169 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503035421/2500000000 : ℝ)^4483 ≤ (6258699743193/50000000000000 : ℝ)^3459 := by
    have hnat : (503035421 : ℕ)^4483*50000000000000^3459 ≤ 6258699743193^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503035421 2500000000 6258699743193 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212963001/10000000000 : ℝ)^4483 ≤ (42986350266349/100000000000000 : ℝ)^3459 := by
    have hnat : (5212963001 : ℕ)^4483*100000000000000^3459 ≤ 42986350266349^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212963001 10000000000 42986350266349 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338421333/2500000000 : ℝ), (-503035421/2500000000 : ℝ), (5212963001/10000000000 : ℝ)] ![(44496250233169/100000000000000 : ℝ), (6258699743193/50000000000000 : ℝ), (42986350266349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338421333/2500000000 : ℝ)|^4483 ≤ (44496250233169/100000000000000 : ℝ)^3459
        have hw : |(1338421333/2500000000 : ℝ)|=(1338421333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-503035421/2500000000 : ℝ)|^4483 ≤ (6258699743193/50000000000000 : ℝ)^3459
        have hw : |(-503035421/2500000000 : ℝ)|=(503035421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212963001/10000000000 : ℝ)|^4483 ≤ (42986350266349/100000000000000 : ℝ)^3459
        have hw : |(5212963001/10000000000 : ℝ)|=(5212963001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353685497/10000000000 : ℝ)*x 0 + (208518509/400000000 : ℝ)*x 1 + (-2012141829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353685497/10000000000 : ℝ)^4483 ≤ (22248126005259/50000000000000 : ℝ)^3459 := by
    have hnat : (5353685497 : ℕ)^4483*50000000000000^3459 ≤ 22248126005259^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353685497 10000000000 22248126005259 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208518509/400000000 : ℝ)^4483 ≤ (42986347316681/100000000000000 : ℝ)^3459 := by
    have hnat : (208518509 : ℕ)^4483*100000000000000^3459 ≤ 42986347316681^3459*400000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208518509 400000000 42986347316681 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012141829/10000000000 : ℝ)^4483 ≤ (12517400655459/100000000000000 : ℝ)^3459 := by
    have hnat : (2012141829 : ℕ)^4483*100000000000000^3459 ≤ 12517400655459^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012141829 10000000000 12517400655459 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353685497/10000000000 : ℝ), (208518509/400000000 : ℝ), (-2012141829/10000000000 : ℝ)] ![(22248126005259/50000000000000 : ℝ), (42986347316681/100000000000000 : ℝ), (12517400655459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353685497/10000000000 : ℝ)|^4483 ≤ (22248126005259/50000000000000 : ℝ)^3459
        have hw : |(5353685497/10000000000 : ℝ)|=(5353685497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208518509/400000000 : ℝ)|^4483 ≤ (42986347316681/100000000000000 : ℝ)^3459
        have hw : |(208518509/400000000 : ℝ)|=(208518509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2012141829/10000000000 : ℝ)|^4483 ≤ (12517400655459/100000000000000 : ℝ)^3459
        have hw : |(-2012141829/10000000000 : ℝ)|=(2012141829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213915757/500000000 : ℝ)*x 0 + (4031077379/10000000000 : ℝ)*x 1 + (4538529261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213915757/500000000 : ℝ)^4483 ≤ (2079672895461/6250000000000 : ℝ)^3459 := by
    have hnat : (213915757 : ℕ)^4483*6250000000000^3459 ≤ 2079672895461^3459*500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213915757 500000000 2079672895461 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4031077379/10000000000 : ℝ)^4483 ≤ (30804224278913/100000000000000 : ℝ)^3459 := by
    have hnat : (4031077379 : ℕ)^4483*100000000000000^3459 ≤ 30804224278913^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031077379 10000000000 30804224278913 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4538529261/10000000000 : ℝ)^4483 ≤ (35921009381537/100000000000000 : ℝ)^3459 := by
    have hnat : (4538529261 : ℕ)^4483*100000000000000^3459 ≤ 35921009381537^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538529261 10000000000 35921009381537 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213915757/500000000 : ℝ), (4031077379/10000000000 : ℝ), (4538529261/10000000000 : ℝ)] ![(2079672895461/6250000000000 : ℝ), (30804224278913/100000000000000 : ℝ), (35921009381537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213915757/500000000 : ℝ)|^4483 ≤ (2079672895461/6250000000000 : ℝ)^3459
        have hw : |(213915757/500000000 : ℝ)|=(213915757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4031077379/10000000000 : ℝ)|^4483 ≤ (30804224278913/100000000000000 : ℝ)^3459
        have hw : |(4031077379/10000000000 : ℝ)|=(4031077379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4538529261/10000000000 : ℝ)|^4483 ≤ (35921009381537/100000000000000 : ℝ)^3459
        have hw : |(4538529261/10000000000 : ℝ)|=(4538529261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-947932241/5000000000 : ℝ)*x 0 + (2607083487/5000000000 : ℝ)*x 1 + (2719284807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947932241/5000000000 : ℝ)^4483 ≤ (5794018235027/50000000000000 : ℝ)^3459 := by
    have hnat : (947932241 : ℕ)^4483*50000000000000^3459 ≤ 5794018235027^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947932241 5000000000 5794018235027 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607083487/5000000000 : ℝ)^4483 ≤ (2687451113219/6250000000000 : ℝ)^3459 := by
    have hnat : (2607083487 : ℕ)^4483*6250000000000^3459 ≤ 2687451113219^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607083487 5000000000 2687451113219 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719284807/5000000000 : ℝ)^4483 ≤ (5676593212339/12500000000000 : ℝ)^3459 := by
    have hnat : (2719284807 : ℕ)^4483*12500000000000^3459 ≤ 5676593212339^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719284807 5000000000 5676593212339 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947932241/5000000000 : ℝ), (2607083487/5000000000 : ℝ), (2719284807/5000000000 : ℝ)] ![(5794018235027/50000000000000 : ℝ), (2687451113219/6250000000000 : ℝ), (5676593212339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947932241/5000000000 : ℝ)|^4483 ≤ (5794018235027/50000000000000 : ℝ)^3459
        have hw : |(-947932241/5000000000 : ℝ)|=(947932241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607083487/5000000000 : ℝ)|^4483 ≤ (2687451113219/6250000000000 : ℝ)^3459
        have hw : |(2607083487/5000000000 : ℝ)|=(2607083487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719284807/5000000000 : ℝ)|^4483 ≤ (5676593212339/12500000000000 : ℝ)^3459
        have hw : |(2719284807/5000000000 : ℝ)|=(2719284807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294316531/10000000000 : ℝ)*x 0 + (-1786535407/10000000000 : ℝ)*x 1 + (2719285093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294316531/10000000000 : ℝ)^4483 ≤ (1370556036067/3125000000000 : ℝ)^3459 := by
    have hnat : (5294316531 : ℕ)^4483*3125000000000^3459 ≤ 1370556036067^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294316531 10000000000 1370556036067 3125000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1786535407/10000000000 : ℝ)^4483 ≤ (2145890989193/20000000000000 : ℝ)^3459 := by
    have hnat : (1786535407 : ℕ)^4483*20000000000000^3459 ≤ 2145890989193^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786535407 10000000000 2145890989193 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719285093/5000000000 : ℝ)^4483 ≤ (45412751888949/100000000000000 : ℝ)^3459 := by
    have hnat : (2719285093 : ℕ)^4483*100000000000000^3459 ≤ 45412751888949^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719285093 5000000000 45412751888949 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294316531/10000000000 : ℝ), (-1786535407/10000000000 : ℝ), (2719285093/5000000000 : ℝ)] ![(1370556036067/3125000000000 : ℝ), (2145890989193/20000000000000 : ℝ), (45412751888949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294316531/10000000000 : ℝ)|^4483 ≤ (1370556036067/3125000000000 : ℝ)^3459
        have hw : |(5294316531/10000000000 : ℝ)|=(5294316531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1786535407/10000000000 : ℝ)|^4483 ≤ (2145890989193/20000000000000 : ℝ)^3459
        have hw : |(-1786535407/10000000000 : ℝ)|=(1786535407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719285093/5000000000 : ℝ)|^4483 ≤ (45412751888949/100000000000000 : ℝ)^3459
        have hw : |(2719285093/5000000000 : ℝ)|=(2719285093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647158977/5000000000 : ℝ)*x 0 + (2719284531/5000000000 : ℝ)*x 1 + (-893267503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647158977/5000000000 : ℝ)^4483 ≤ (21928904215957/50000000000000 : ℝ)^3459 := by
    have hnat : (2647158977 : ℕ)^4483*50000000000000^3459 ≤ 21928904215957^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647158977 5000000000 21928904215957 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2719284531/5000000000 : ℝ)^4483 ≤ (45412739724917/100000000000000 : ℝ)^3459 := by
    have hnat : (2719284531 : ℕ)^4483*100000000000000^3459 ≤ 45412739724917^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719284531 5000000000 45412739724917 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893267503/5000000000 : ℝ)^4483 ≤ (2145890364943/20000000000000 : ℝ)^3459 := by
    have hnat : (893267503 : ℕ)^4483*20000000000000^3459 ≤ 2145890364943^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893267503 5000000000 2145890364943 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647158977/5000000000 : ℝ), (2719284531/5000000000 : ℝ), (-893267503/5000000000 : ℝ)] ![(21928904215957/50000000000000 : ℝ), (45412739724917/100000000000000 : ℝ), (2145890364943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647158977/5000000000 : ℝ)|^4483 ≤ (21928904215957/50000000000000 : ℝ)^3459
        have hw : |(2647158977/5000000000 : ℝ)|=(2647158977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2719284531/5000000000 : ℝ)|^4483 ≤ (45412739724917/100000000000000 : ℝ)^3459
        have hw : |(2719284531/5000000000 : ℝ)|=(2719284531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893267503/5000000000 : ℝ)|^4483 ≤ (2145890364943/20000000000000 : ℝ)^3459
        have hw : |(-893267503/5000000000 : ℝ)|=(893267503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s3_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278387781/10000000000 : ℝ)*x 0 + (4535835833/10000000000 : ℝ)*x 1 + (201689629/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278387781/10000000000 : ℝ)^4483 ≤ (33275498550307/100000000000000 : ℝ)^3459 := by
    have hnat : (4278387781 : ℕ)^4483*100000000000000^3459 ≤ 33275498550307^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278387781 10000000000 33275498550307 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535835833/10000000000 : ℝ)^4483 ≤ (4486672916529/12500000000000 : ℝ)^3459 := by
    have hnat : (4535835833 : ℕ)^4483*12500000000000^3459 ≤ 4486672916529^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535835833 10000000000 4486672916529 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201689629/500000000 : ℝ)^4483 ≤ (30831118105141/100000000000000 : ℝ)^3459 := by
    have hnat : (201689629 : ℕ)^4483*100000000000000^3459 ≤ 30831118105141^3459*500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201689629 500000000 30831118105141 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278387781/10000000000 : ℝ), (4535835833/10000000000 : ℝ), (201689629/500000000 : ℝ)] ![(33275498550307/100000000000000 : ℝ), (4486672916529/12500000000000 : ℝ), (30831118105141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278387781/10000000000 : ℝ)|^4483 ≤ (33275498550307/100000000000000 : ℝ)^3459
        have hw : |(4278387781/10000000000 : ℝ)|=(4278387781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535835833/10000000000 : ℝ)|^4483 ≤ (4486672916529/12500000000000 : ℝ)^3459
        have hw : |(4535835833/10000000000 : ℝ)|=(4535835833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201689629/500000000 : ℝ)|^4483 ≤ (30831118105141/100000000000000 : ℝ)^3459
        have hw : |(201689629/500000000 : ℝ)|=(201689629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5381/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15563/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5147/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16073/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5147/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5147/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16073/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5147/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5147/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16073/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5147/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5147/50000 : ℝ) ^ (4481/1024 : ℝ) ≤ (191051932595707/4000000000000000000 : ℝ) := by
    have hpowers : (5147/50000 : ℝ)^4481 ≤ (191051932595707/4000000000000000000 : ℝ)^1024 := by
      have hnat : (5147 : ℕ)^4481*4000000000000000000^1024 ≤ 191051932595707^1024*50000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5147 50000 191051932595707 4000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5147/50000 : ℝ)) (X := (191051932595707/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16073/100000 : ℝ) ^ (4481/1024 : ℝ) ≤ (33565941794147693/100000000000000000000 : ℝ) := by
    have hpowers : (16073/100000 : ℝ)^4481 ≤ (33565941794147693/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16073 : ℕ)^4481*100000000000000000000^1024 ≤ 33565941794147693^1024*100000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16073 100000 33565941794147693 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16073/100000 : ℝ)) (X := (33565941794147693/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000191051932595707/2000000000000000000 : ℝ) ≤ (10000218288295597/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (2000191051932595707/2000000000000000000 : ℝ)^1024 ≤ (10000218288295597/10000000000000000 : ℝ)^4481 := by
      have hnat : (2000191051932595707 : ℕ)^1024*10000000000000000^4481 ≤ 10000218288295597^4481*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000191051932595707 2000000000000000000 10000218288295597 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000218288295597/10000000000000000 : ℝ)) (X := (2000191051932595707/2000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252396390006815023/6250000000000000000 : ℝ) ≤ (10000876068918077/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (6252396390006815023/6250000000000000000 : ℝ)^1024 ≤ (10000876068918077/10000000000000000 : ℝ)^4481 := by
      have hnat : (6252396390006815023 : ℕ)^1024*10000000000000000^4481 ≤ 10000876068918077^4481*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252396390006815023 6250000000000000000 10000876068918077 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000876068918077/10000000000000000 : ℝ)) (X := (6252396390006815023/6250000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033565941794147693/50000000000000000000 : ℝ) ≤ (10001533849540557/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50033565941794147693/50000000000000000000 : ℝ)^1024 ≤ (10001533849540557/10000000000000000 : ℝ)^4481 := by
      have hnat : (50033565941794147693 : ℕ)^1024*10000000000000000^4481 ≤ 10001533849540557^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033565941794147693 50000000000000000000 10001533849540557 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001533849540557/10000000000000000 : ℝ)) (X := (50033565941794147693/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(191051932595707/4000000000000000000 : ℝ) ≤ ((57777719100604636823/57790000000000000000 : ℝ)+2*(8222257781/7223750000000 : ℝ)*(5147/50000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (57777719100604636823/57790000000000000000 : ℝ)+2*(8222257781/7223750000000 : ℝ)*(5147/50000 : ℝ)=(10000218288295597/10000000000000000 : ℝ) by norm_num, show 1+2*(191051932595707/4000000000000000000 : ℝ)=(2000191051932595707/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33565941794147693/100000000000000000000 : ℝ)+(191051932595707/4000000000000000000 : ℝ) ≤ ((57777719100604636823/57790000000000000000 : ℝ)+(8222257781/7223750000000 : ℝ)*((16073/100000 : ℝ)+(5147/50000 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (57777719100604636823/57790000000000000000 : ℝ)+(8222257781/7223750000000 : ℝ)*((16073/100000 : ℝ)+(5147/50000 : ℝ))=(10000876068918077/10000000000000000 : ℝ) by norm_num, show 1+(33565941794147693/100000000000000000000 : ℝ)+(191051932595707/4000000000000000000 : ℝ)=(6252396390006815023/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33565941794147693/100000000000000000000 : ℝ) ≤ ((57777719100604636823/57790000000000000000 : ℝ)+2*(8222257781/7223750000000 : ℝ)*(16073/100000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (57777719100604636823/57790000000000000000 : ℝ)+2*(8222257781/7223750000000 : ℝ)*(16073/100000 : ℝ)=(10001533849540557/10000000000000000 : ℝ) by norm_num, show 1+2*(33565941794147693/100000000000000000000 : ℝ)=(50033565941794147693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57777719100604636823/57790000000000000000 : ℝ)*(X 1 0+X 2 0)+(8222257781/7223750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (5147/50000 : ℝ)) (hi := (16073/100000 : ℝ)) (c := (57777719100604636823/57790000000000000000 : ℝ)) (alpha := (8222257781/7223750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57777719100604636823/57790000000000000000 : ℝ)*(X 0 1+X 2 1)+(8222257781/7223750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (5147/50000 : ℝ)) (hi := (16073/100000 : ℝ)) (c := (57777719100604636823/57790000000000000000 : ℝ)) (alpha := (8222257781/7223750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57777719100604636823/57790000000000000000 : ℝ)*(X 0 2+X 1 2)+(8222257781/7223750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (5147/50000 : ℝ)) (hi := (16073/100000 : ℝ)) (c := (57777719100604636823/57790000000000000000 : ℝ)) (alpha := (8222257781/7223750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1895832081/10000000000 : ℝ)*X 0 0+(5439782579/10000000000 : ℝ)*X 0 1+(5212962717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338421333/2500000000 : ℝ)*X 1 0+(-503035421/2500000000 : ℝ)*X 1 1+(5212963001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353685497/10000000000 : ℝ)*X 2 0+(208518509/400000000 : ℝ)*X 2 1+(-2012141829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213915757/500000000 : ℝ)*X 0 0+(4031077379/10000000000 : ℝ)*X 0 1+(4538529261/10000000000 : ℝ)*X 0 2+(213915757/500000000 : ℝ)*X 1 0+(4031077379/10000000000 : ℝ)*X 1 1+(4538529261/10000000000 : ℝ)*X 1 2+(213915757/500000000 : ℝ)*X 2 0+(4031077379/10000000000 : ℝ)*X 2 1+(4538529261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-947932241/5000000000 : ℝ)*X 0 0+(2607083487/5000000000 : ℝ)*X 0 1+(2719284807/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294316531/10000000000 : ℝ)*X 1 0+(-1786535407/10000000000 : ℝ)*X 1 1+(2719285093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647158977/5000000000 : ℝ)*X 2 0+(2719284531/5000000000 : ℝ)*X 2 1+(-893267503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278387781/10000000000 : ℝ)*X 0 0+(4535835833/10000000000 : ℝ)*X 0 1+(201689629/500000000 : ℝ)*X 0 2+(4278387781/10000000000 : ℝ)*X 1 0+(4535835833/10000000000 : ℝ)*X 1 1+(201689629/500000000 : ℝ)*X 1 2+(4278387781/10000000000 : ℝ)*X 2 0+(4535835833/10000000000 : ℝ)*X 2 1+(201689629/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15923334858214455871323/2889500000000000000000000000 : ℝ) := by norm_num
    linear_combination (185276403/10000000000000 : ℝ)*(base19) + (239474609/12500000000000 : ℝ)*(base23) + (9750057/25000000000000 : ℝ)*(lower2) + (143886947/50000000000000 : ℝ)*(upper3) + (122462667/100000000000000 : ℝ)*(upper5) + (1594875281609709/50000000000000 : ℝ)*(major0) + (1594875281609709/50000000000000 : ℝ)*(major1) + (1594875281609709/50000000000000 : ℝ)*(major2) + (4408819995533627/100000000000000 : ℝ)*(sp0) + (440885025005499/10000000000000 : ℝ)*(sp1) + (4408850187022147/100000000000000 : ℝ)*(sp2) + (985319168208803/50000000000000 : ℝ)*(sp3) + (2006705337/6250000000000 : ℝ)*(sp4) + (420140411/4000000000000 : ℝ)*(sp7) + (1970648839927881/100000000000000 : ℝ)*(f.failure) + (220442605140951/5000000000000 : ℝ)*(f.sum) + (1504884975923/1444750000000000000000000000 : ℝ)*base65 + (12983750881197285493/2889500000000000000000000000000000 : ℝ)*base68 + (2381612307994214507/2889500000000000000000000000000000 : ℝ)*base69 + (23862038496294785493/2889500000000000000000000000000000 : ℝ)*base72 + (5724808025503/5779000000000000000000000000 : ℝ)*base74 + (13773865551595714507/2889500000000000000000000000000000 : ℝ)*base75 + (6106914493915285493/2889500000000000000000000000000000 : ℝ)*base78 + (35160685688909714507/2889500000000000000000000000000000 : ℝ)*base79 + (9572617716209/5779000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (45115641/10000000000000000000000 : ℝ)*base89 + (45115641/10000000000000000000000 : ℝ)*base91 + (45115641/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7196176012981840518608325849/1444750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (742314407/100000000000000 : ℝ)*(base23) + (157032819/100000000000000 : ℝ)*(lower2) + (35316407/25000000000000 : ℝ)*(lower3) + (9107977/10000000000000 : ℝ)*(upper4) + (3224088607824021/100000000000000 : ℝ)*(major0) + (3224088607824021/100000000000000 : ℝ)*(major1) + (3224088607824021/100000000000000 : ℝ)*(major2) + (11772053121/100000000000000 : ℝ)*(sp0) + (29332063303/100000000000000 : ℝ)*(sp1) + (30509079307/100000000000000 : ℝ)*(sp2) + (222815108411851/5000000000000 : ℝ)*(sp4) + (2228142304113419/50000000000000 : ℝ)*(sp5) + (1114070672224107/25000000000000 : ℝ)*(sp6) + (398372621865483/20000000000000 : ℝ)*(sp7) + (398372621865483/20000000000000 : ℝ)*(f.failure) + (2228156970145071/50000000000000 : ℝ)*(f.sum) + (1216453001963/577900000000000000000000000 : ℝ)*base66 + (29437324806077474717/5779000000000000000000000000000000 : ℝ)*base68 + (37183279710914474717/5779000000000000000000000000000000 : ℝ)*base70 + (4904218252477525283/5779000000000000000000000000000000 : ℝ)*base71 + (1949124645733/5779000000000000000000000000 : ℝ)*base73 + (24251635301300474717/5779000000000000000000000000000000 : ℝ)*base76 + (43221839271465474717/5779000000000000000000000000000000 : ℝ)*base78 + (72990097026665474717/5779000000000000000000000000000000 : ℝ)*base80 + (1193172538097/231160000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2075163/2000000000000000000000 : ℝ)*base89 + (2075163/2000000000000000000000 : ℝ)*base91 + (2075163/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15563/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1493_s4_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-23704707/125000000 : ℝ)*x 0 + (5436239113/10000000000 : ℝ)*x 1 + (1304036727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23704707/125000000 : ℝ)^4483 ≤ (1449011647807/12500000000000 : ℝ)^3459 := by
    have hnat : (23704707 : ℕ)^4483*12500000000000^3459 ≤ 1449011647807^3459*125000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23704707 125000000 1449011647807 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436239113/10000000000 : ℝ)^4483 ≤ (22693763200489/50000000000000 : ℝ)^3459 := by
    have hnat : (5436239113 : ℕ)^4483*50000000000000^3459 ≤ 22693763200489^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436239113 10000000000 22693763200489 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304036727/2500000000 : ℝ)^4483 ≤ (21510190203201/50000000000000 : ℝ)^3459 := by
    have hnat : (1304036727 : ℕ)^4483*50000000000000^3459 ≤ 21510190203201^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304036727 2500000000 21510190203201 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23704707/125000000 : ℝ), (5436239113/10000000000 : ℝ), (1304036727/2500000000 : ℝ)] ![(1449011647807/12500000000000 : ℝ), (22693763200489/50000000000000 : ℝ), (21510190203201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23704707/125000000 : ℝ)|^4483 ≤ (1449011647807/12500000000000 : ℝ)^3459
        have hw : |(-23704707/125000000 : ℝ)|=(23704707/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436239113/10000000000 : ℝ)|^4483 ≤ (22693763200489/50000000000000 : ℝ)^3459
        have hw : |(5436239113/10000000000 : ℝ)|=(5436239113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304036727/2500000000 : ℝ)|^4483 ≤ (21510190203201/50000000000000 : ℝ)^3459
        have hw : |(1304036727/2500000000 : ℝ)|=(1304036727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338190523/2500000000 : ℝ)*x 0 + (-1004576857/5000000000 : ℝ)*x 1 + (5216146909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338190523/2500000000 : ℝ)^4483 ≤ (22243152759843/50000000000000 : ℝ)^3459 := by
    have hnat : (1338190523 : ℕ)^4483*50000000000000^3459 ≤ 22243152759843^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338190523 2500000000 22243152759843 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004576857/5000000000 : ℝ)^4483 ≤ (3123328513317/25000000000000 : ℝ)^3459 := by
    have hnat : (1004576857 : ℕ)^4483*25000000000000^3459 ≤ 3123328513317^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004576857 5000000000 3123328513317 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216146909/10000000000 : ℝ)^4483 ≤ (43020380417091/100000000000000 : ℝ)^3459 := by
    have hnat : (5216146909 : ℕ)^4483*100000000000000^3459 ≤ 43020380417091^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216146909 10000000000 43020380417091 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338190523/2500000000 : ℝ), (-1004576857/5000000000 : ℝ), (5216146909/10000000000 : ℝ)] ![(22243152759843/50000000000000 : ℝ), (3123328513317/25000000000000 : ℝ), (43020380417091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338190523/2500000000 : ℝ)|^4483 ≤ (22243152759843/50000000000000 : ℝ)^3459
        have hw : |(1338190523/2500000000 : ℝ)|=(1338190523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1004576857/5000000000 : ℝ)|^4483 ≤ (3123328513317/25000000000000 : ℝ)^3459
        have hw : |(-1004576857/5000000000 : ℝ)|=(1004576857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216146909/10000000000 : ℝ)|^4483 ≤ (43020380417091/100000000000000 : ℝ)^3459
        have hw : |(5216146909/10000000000 : ℝ)|=(5216146909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352762093/10000000000 : ℝ)*x 0 + (5216146909/10000000000 : ℝ)*x 1 + (-125572107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352762093/10000000000 : ℝ)^4483 ≤ (22243152765229/50000000000000 : ℝ)^3459 := by
    have hnat : (5352762093 : ℕ)^4483*50000000000000^3459 ≤ 22243152765229^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352762093 10000000000 22243152765229 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216146909/10000000000 : ℝ)^4483 ≤ (43020380417091/100000000000000 : ℝ)^3459 := by
    have hnat : (5216146909 : ℕ)^4483*100000000000000^3459 ≤ 43020380417091^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216146909 10000000000 43020380417091 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125572107/625000000 : ℝ)^4483 ≤ (249866280743/2000000000000 : ℝ)^3459 := by
    have hnat : (125572107 : ℕ)^4483*2000000000000^3459 ≤ 249866280743^3459*625000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125572107 625000000 249866280743 2000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352762093/10000000000 : ℝ), (5216146909/10000000000 : ℝ), (-125572107/625000000 : ℝ)] ![(22243152765229/50000000000000 : ℝ), (43020380417091/100000000000000 : ℝ), (249866280743/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352762093/10000000000 : ℝ)|^4483 ≤ (22243152765229/50000000000000 : ℝ)^3459
        have hw : |(5352762093/10000000000 : ℝ)|=(5352762093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216146909/10000000000 : ℝ)|^4483 ≤ (43020380417091/100000000000000 : ℝ)^3459
        have hw : |(5216146909/10000000000 : ℝ)|=(5216146909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125572107/625000000 : ℝ)|^4483 ≤ (249866280743/2000000000000 : ℝ)^3459
        have hw : |(-125572107/625000000 : ℝ)|=(125572107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855730789/2000000000 : ℝ)*x 0 + (807712471/2000000000 : ℝ)*x 1 + (4530965669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855730789/2000000000 : ℝ)^4483 ≤ (8319545380231/25000000000000 : ℝ)^3459 := by
    have hnat : (855730789 : ℕ)^4483*25000000000000^3459 ≤ 8319545380231^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855730789 2000000000 8319545380231 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (807712471/2000000000 : ℝ)^4483 ≤ (15439187640669/50000000000000 : ℝ)^3459 := by
    have hnat : (807712471 : ℕ)^4483*50000000000000^3459 ≤ 15439187640669^3459*2000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807712471 2000000000 15439187640669 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530965669/10000000000 : ℝ)^4483 ≤ (35843443188589/100000000000000 : ℝ)^3459 := by
    have hnat : (4530965669 : ℕ)^4483*100000000000000^3459 ≤ 35843443188589^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530965669 10000000000 35843443188589 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855730789/2000000000 : ℝ), (807712471/2000000000 : ℝ), (4530965669/10000000000 : ℝ)] ![(8319545380231/25000000000000 : ℝ), (15439187640669/50000000000000 : ℝ), (35843443188589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855730789/2000000000 : ℝ)|^4483 ≤ (8319545380231/25000000000000 : ℝ)^3459
        have hw : |(855730789/2000000000 : ℝ)|=(855730789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(807712471/2000000000 : ℝ)|^4483 ≤ (15439187640669/50000000000000 : ℝ)^3459
        have hw : |(807712471/2000000000 : ℝ)|=(807712471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530965669/10000000000 : ℝ)|^4483 ≤ (35843443188589/100000000000000 : ℝ)^3459
        have hw : |(4530965669/10000000000 : ℝ)|=(4530965669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1896406013/10000000000 : ℝ)*x 0 + (521728129/1000000000 : ℝ)*x 1 + (5435096889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896406013/10000000000 : ℝ)^4483 ≤ (5796163260369/50000000000000 : ℝ)^3459 := by
    have hnat : (1896406013 : ℕ)^4483*50000000000000^3459 ≤ 5796163260369^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896406013 10000000000 5796163260369 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521728129/1000000000 : ℝ)^4483 ≤ (21516253180177/50000000000000 : ℝ)^3459 := by
    have hnat : (521728129 : ℕ)^4483*50000000000000^3459 ≤ 21516253180177^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521728129 1000000000 21516253180177 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435096889/10000000000 : ℝ)^4483 ≤ (45375167099847/100000000000000 : ℝ)^3459 := by
    have hnat : (5435096889 : ℕ)^4483*100000000000000^3459 ≤ 45375167099847^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435096889 10000000000 45375167099847 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1896406013/10000000000 : ℝ), (521728129/1000000000 : ℝ), (5435096889/10000000000 : ℝ)] ![(5796163260369/50000000000000 : ℝ), (21516253180177/50000000000000 : ℝ), (45375167099847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1896406013/10000000000 : ℝ)|^4483 ≤ (5796163260369/50000000000000 : ℝ)^3459
        have hw : |(-1896406013/10000000000 : ℝ)|=(1896406013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521728129/1000000000 : ℝ)|^4483 ≤ (21516253180177/50000000000000 : ℝ)^3459
        have hw : |(521728129/1000000000 : ℝ)|=(521728129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435096889/10000000000 : ℝ)|^4483 ≤ (45375167099847/100000000000000 : ℝ)^3459
        have hw : |(5435096889/10000000000 : ℝ)|=(5435096889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647578243/5000000000 : ℝ)*x 0 + (-1790203877/10000000000 : ℝ)*x 1 + (2717548617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647578243/5000000000 : ℝ)^4483 ≤ (8773362276661/20000000000000 : ℝ)^3459 := by
    have hnat : (2647578243 : ℕ)^4483*20000000000000^3459 ≤ 8773362276661^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647578243 5000000000 8773362276661 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1790203877/10000000000 : ℝ)^4483 ≤ (5379008883499/50000000000000 : ℝ)^3459 := by
    have hnat : (1790203877 : ℕ)^4483*50000000000000^3459 ≤ 5379008883499^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790203877 10000000000 5379008883499 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717548617/5000000000 : ℝ)^4483 ≤ (45375170832763/100000000000000 : ℝ)^3459 := by
    have hnat : (2717548617 : ℕ)^4483*100000000000000^3459 ≤ 45375170832763^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717548617 5000000000 45375170832763 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647578243/5000000000 : ℝ), (-1790203877/10000000000 : ℝ), (2717548617/5000000000 : ℝ)] ![(8773362276661/20000000000000 : ℝ), (5379008883499/50000000000000 : ℝ), (45375170832763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647578243/5000000000 : ℝ)|^4483 ≤ (8773362276661/20000000000000 : ℝ)^3459
        have hw : |(2647578243/5000000000 : ℝ)|=(2647578243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1790203877/10000000000 : ℝ)|^4483 ≤ (5379008883499/50000000000000 : ℝ)^3459
        have hw : |(-1790203877/10000000000 : ℝ)|=(1790203877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717548617/5000000000 : ℝ)|^4483 ≤ (45375170832763/100000000000000 : ℝ)^3459
        have hw : |(2717548617/5000000000 : ℝ)|=(2717548617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647578031/5000000000 : ℝ)*x 0 + (2717548901/5000000000 : ℝ)*x 1 + (-1790203673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647578031/5000000000 : ℝ)^4483 ≤ (2741675426931/6250000000000 : ℝ)^3459 := by
    have hnat : (2647578031 : ℕ)^4483*6250000000000^3459 ≤ 2741675426931^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647578031 5000000000 2741675426931 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717548901/5000000000 : ℝ)^4483 ≤ (907503539571/2000000000000 : ℝ)^3459 := by
    have hnat : (2717548901 : ℕ)^4483*2000000000000^3459 ≤ 907503539571^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717548901 5000000000 907503539571 2000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790203673/10000000000 : ℝ)^4483 ≤ (2151603235633/20000000000000 : ℝ)^3459 := by
    have hnat : (1790203673 : ℕ)^4483*20000000000000^3459 ≤ 2151603235633^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790203673 10000000000 2151603235633 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647578031/5000000000 : ℝ), (2717548901/5000000000 : ℝ), (-1790203673/10000000000 : ℝ)] ![(2741675426931/6250000000000 : ℝ), (907503539571/2000000000000 : ℝ), (2151603235633/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647578031/5000000000 : ℝ)|^4483 ≤ (2741675426931/6250000000000 : ℝ)^3459
        have hw : |(2647578031/5000000000 : ℝ)|=(2647578031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717548901/5000000000 : ℝ)|^4483 ≤ (907503539571/2000000000000 : ℝ)^3459
        have hw : |(2717548901/5000000000 : ℝ)|=(2717548901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790203673/10000000000 : ℝ)|^4483 ≤ (2151603235633/20000000000000 : ℝ)^3459
        have hw : |(-1790203673/10000000000 : ℝ)|=(1790203673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s4_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278721789/10000000000 : ℝ)*x 0 + (4528428761/10000000000 : ℝ)*x 1 + (4041117683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278721789/10000000000 : ℝ)^4483 ≤ (2079929087869/6250000000000 : ℝ)^3459 := by
    have hnat : (4278721789 : ℕ)^4483*6250000000000^3459 ≤ 2079929087869^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278721789 10000000000 2079929087869 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4528428761/10000000000 : ℝ)^4483 ≤ (35817435255077/100000000000000 : ℝ)^3459 := by
    have hnat : (4528428761 : ℕ)^4483*100000000000000^3459 ≤ 35817435255077^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4528428761 10000000000 35817435255077 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4041117683/10000000000 : ℝ)^4483 ≤ (482870302037/1562500000000 : ℝ)^3459 := by
    have hnat : (4041117683 : ℕ)^4483*1562500000000^3459 ≤ 482870302037^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041117683 10000000000 482870302037 1562500000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278721789/10000000000 : ℝ), (4528428761/10000000000 : ℝ), (4041117683/10000000000 : ℝ)] ![(2079929087869/6250000000000 : ℝ), (35817435255077/100000000000000 : ℝ), (482870302037/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278721789/10000000000 : ℝ)|^4483 ≤ (2079929087869/6250000000000 : ℝ)^3459
        have hw : |(4278721789/10000000000 : ℝ)|=(4278721789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4528428761/10000000000 : ℝ)|^4483 ≤ (35817435255077/100000000000000 : ℝ)^3459
        have hw : |(4528428761/10000000000 : ℝ)|=(4528428761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4041117683/10000000000 : ℝ)|^4483 ≤ (482870302037/1562500000000 : ℝ)^3459
        have hw : |(4041117683/10000000000 : ℝ)|=(4041117683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1083/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5381/50000 : ℝ) ^ (4481/1024 : ℝ) ≤ (1450528989825647/25000000000000000000 : ℝ) := by
    have hpowers : (5381/50000 : ℝ)^4481 ≤ (1450528989825647/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5381 : ℕ)^4481*25000000000000000000^1024 ≤ 1450528989825647^1024*50000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5381 50000 1450528989825647 25000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5381/50000 : ℝ)) (X := (1450528989825647/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15563/100000 : ℝ) ^ (4481/1024 : ℝ) ≤ (14574353423417209/50000000000000000000 : ℝ) := by
    have hpowers : (15563/100000 : ℝ)^4481 ≤ (14574353423417209/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15563 : ℕ)^4481*50000000000000000000^1024 ≤ 14574353423417209^1024*100000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15563 100000 14574353423417209 50000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15563/100000 : ℝ)) (X := (14574353423417209/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501450528989825647/12500000000000000000 : ℝ) ≤ (1000026516852543/1000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (12501450528989825647/12500000000000000000 : ℝ)^1024 ≤ (1000026516852543/1000000000000000 : ℝ)^4481 := by
      have hnat : (12501450528989825647 : ℕ)^1024*1000000000000000^4481 ≤ 1000026516852543^4481*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501450528989825647 12500000000000000000 1000026516852543 1000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000026516852543/1000000000000000 : ℝ)) (X := (12501450528989825647/12500000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017475411403068503/50000000000000000000 : ℝ) ≤ (5000399295005769/5000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50017475411403068503/50000000000000000000 : ℝ)^1024 ≤ (5000399295005769/5000000000000000 : ℝ)^4481 := by
      have hnat : (50017475411403068503 : ℕ)^1024*5000000000000000^4481 ≤ 5000399295005769^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017475411403068503 50000000000000000000 5000399295005769 5000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000399295005769/5000000000000000 : ℝ)) (X := (50017475411403068503/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014574353423417209/25000000000000000000 : ℝ) ≤ (5000666005748823/5000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (25014574353423417209/25000000000000000000 : ℝ)^1024 ≤ (5000666005748823/5000000000000000 : ℝ)^4481 := by
      have hnat : (25014574353423417209 : ℕ)^1024*5000000000000000^4481 ≤ 5000666005748823^4481*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014574353423417209 25000000000000000000 5000666005748823 5000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000666005748823/5000000000000000 : ℝ)) (X := (25014574353423417209/25000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1450528989825647/25000000000000000000 : ℝ) ≤ ((23999895855011800419/24005000000000000000 : ℝ)+2*(133355371527/120025000000000 : ℝ)*(5381/50000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (23999895855011800419/24005000000000000000 : ℝ)+2*(133355371527/120025000000000 : ℝ)*(5381/50000 : ℝ)=(1000026516852543/1000000000000000 : ℝ) by norm_num, show 1+2*(1450528989825647/25000000000000000000 : ℝ)=(12501450528989825647/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14574353423417209/50000000000000000000 : ℝ)+(1450528989825647/25000000000000000000 : ℝ) ≤ ((23999895855011800419/24005000000000000000 : ℝ)+(133355371527/120025000000000 : ℝ)*((15563/100000 : ℝ)+(5381/50000 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (23999895855011800419/24005000000000000000 : ℝ)+(133355371527/120025000000000 : ℝ)*((15563/100000 : ℝ)+(5381/50000 : ℝ))=(5000399295005769/5000000000000000 : ℝ) by norm_num, show 1+(14574353423417209/50000000000000000000 : ℝ)+(1450528989825647/25000000000000000000 : ℝ)=(50017475411403068503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14574353423417209/50000000000000000000 : ℝ) ≤ ((23999895855011800419/24005000000000000000 : ℝ)+2*(133355371527/120025000000000 : ℝ)*(15563/100000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (23999895855011800419/24005000000000000000 : ℝ)+2*(133355371527/120025000000000 : ℝ)*(15563/100000 : ℝ)=(5000666005748823/5000000000000000 : ℝ) by norm_num, show 1+2*(14574353423417209/50000000000000000000 : ℝ)=(25014574353423417209/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23999895855011800419/24005000000000000000 : ℝ)*(X 1 0+X 2 0)+(133355371527/120025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (15563/100000 : ℝ)) (c := (23999895855011800419/24005000000000000000 : ℝ)) (alpha := (133355371527/120025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23999895855011800419/24005000000000000000 : ℝ)*(X 0 1+X 2 1)+(133355371527/120025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (15563/100000 : ℝ)) (c := (23999895855011800419/24005000000000000000 : ℝ)) (alpha := (133355371527/120025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23999895855011800419/24005000000000000000 : ℝ)*(X 0 2+X 1 2)+(133355371527/120025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (15563/100000 : ℝ)) (c := (23999895855011800419/24005000000000000000 : ℝ)) (alpha := (133355371527/120025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-23704707/125000000 : ℝ)*X 0 0+(5436239113/10000000000 : ℝ)*X 0 1+(1304036727/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338190523/2500000000 : ℝ)*X 1 0+(-1004576857/5000000000 : ℝ)*X 1 1+(5216146909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352762093/10000000000 : ℝ)*X 2 0+(5216146909/10000000000 : ℝ)*X 2 1+(-125572107/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855730789/2000000000 : ℝ)*X 0 0+(807712471/2000000000 : ℝ)*X 0 1+(4530965669/10000000000 : ℝ)*X 0 2+(855730789/2000000000 : ℝ)*X 1 0+(807712471/2000000000 : ℝ)*X 1 1+(4530965669/10000000000 : ℝ)*X 1 2+(855730789/2000000000 : ℝ)*X 2 0+(807712471/2000000000 : ℝ)*X 2 1+(4530965669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1896406013/10000000000 : ℝ)*X 0 0+(521728129/1000000000 : ℝ)*X 0 1+(5435096889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647578243/5000000000 : ℝ)*X 1 0+(-1790203877/10000000000 : ℝ)*X 1 1+(2717548617/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647578031/5000000000 : ℝ)*X 2 0+(2717548901/5000000000 : ℝ)*X 2 1+(-1790203673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278721789/10000000000 : ℝ)*X 0 0+(4528428761/10000000000 : ℝ)*X 0 1+(4041117683/10000000000 : ℝ)*X 0 2+(4278721789/10000000000 : ℝ)*X 1 0+(4528428761/10000000000 : ℝ)*X 1 1+(4041117683/10000000000 : ℝ)*X 1 2+(4278721789/10000000000 : ℝ)*X 2 0+(4528428761/10000000000 : ℝ)*X 2 1+(4041117683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5608827936390873425897063889/600125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414648449/25000000000000 : ℝ)*(base19) + (1548025687/100000000000000 : ℝ)*(base23) + (29819419/50000000000000 : ℝ)*(lower2) + (233034127/100000000000000 : ℝ)*(upper3) + (38189741/25000000000000 : ℝ)*(upper5) + (1643620455320377/50000000000000 : ℝ)*(major0) + (1643620455320377/50000000000000 : ℝ)*(major1) + (1643620455320377/50000000000000 : ℝ)*(major2) + (1135894219223779/25000000000000 : ℝ)*(sp0) + (4543600834523681/100000000000000 : ℝ)*(sp1) + (4543600945091789/100000000000000 : ℝ)*(sp2) + (2030866617288359/100000000000000 : ℝ)*(sp3) + (25616222361/100000000000000 : ℝ)*(sp4) + (6199669509/50000000000000 : ℝ)*(sp7) + (2030879016627377/100000000000000 : ℝ)*(f.failure) + (1135900623279369/25000000000000 : ℝ)*(f.sum) + (10595179022603/6001250000000000000000000000 : ℝ)*base65 + (2451993631821612037/1200250000000000000000000000000000 : ℝ)*base68 + (3750326598716862037/1200250000000000000000000000000000 : ℝ)*base70 + (4155592675963612037/1200250000000000000000000000000000 : ℝ)*base72 + (43789290775113/24005000000000000000000000000 : ℝ)*base74 + (7089832370940137963/1200250000000000000000000000000000 : ℝ)*base75 + (1793085059394862037/1200250000000000000000000000000000 : ℝ)*base78 + (17003059776477637963/1200250000000000000000000000000000 : ℝ)*base79 + (76633190741053/24005000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (74883297/10000000000000000000000 : ℝ)*base89 + (74883297/10000000000000000000000 : ℝ)*base91 + (74883297/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3223882662458407734555896919/1200250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40462727/25000000000000 : ℝ)*(base8) + (30019513/10000000000000 : ℝ)*(base15) + (2396737/1562500000000 : ℝ)*(base29) + (143257607/50000000000000 : ℝ)*(lower4) + (68250661/100000000000000 : ℝ)*(upper5) + (415194395560147/12500000000000 : ℝ)*(major0) + (3321555317872343/100000000000000 : ℝ)*(major1) + (3321555317872343/100000000000000 : ℝ)*(major2) + (8572304057/100000000000000 : ℝ)*(sp2) + (289396749/10000000000000 : ℝ)*(sp3) + (2295515850828727/50000000000000 : ℝ)*(sp4) + (286939463120129/6250000000000 : ℝ)*(sp5) + (2295511568906569/50000000000000 : ℝ)*(sp6) + (128254736795949/6250000000000 : ℝ)*(sp7) + (1026039341351337/50000000000000 : ℝ)*(f.failure) + (2295515931754181/50000000000000 : ℝ)*(f.sum) + (35511148796447/3000625000000000000000000000 : ℝ)*base66 + (7914036859971111717/2400500000000000000000000000000000 : ℝ)*base67 + (9227977938855888283/2400500000000000000000000000000000 : ℝ)*base70 + (2916582391960201593/300062500000000000000000000000000 : ℝ)*base71 + (25214875570949/6001250000000000000000000000 : ℝ)*base73 + (6278723302442688283/2400500000000000000000000000000000 : ℝ)*base76 + (1974522144388139093/300062500000000000000000000000000 : ℝ)*base77 + (5443512548445188283/2400500000000000000000000000000000 : ℝ)*base80 + (4773799330453/12002500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (51871143/5000000000000000000000 : ℝ)*base90 + (1871143/5000000000000000000000 : ℝ)*base92 + (1871143/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1493_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1493_s5_0 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-474112027/2500000000 : ℝ)*x 0 + (5435774303/10000000000 : ℝ)*x 1 + (5216564399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474112027/2500000000 : ℝ)^4483 ≤ (5796330007897/50000000000000 : ℝ)^3459 := by
    have hnat : (474112027 : ℕ)^4483*50000000000000^3459 ≤ 5796330007897^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474112027 2500000000 5796330007897 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435774303/10000000000 : ℝ)^4483 ≤ (11345624221497/25000000000000 : ℝ)^3459 := by
    have hnat : (5435774303 : ℕ)^4483*25000000000000^3459 ≤ 11345624221497^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435774303 10000000000 11345624221497 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216564399/10000000000 : ℝ)^4483 ≤ (43024843077411/100000000000000 : ℝ)^3459 := by
    have hnat : (5216564399 : ℕ)^4483*100000000000000^3459 ≤ 43024843077411^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216564399 10000000000 43024843077411 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474112027/2500000000 : ℝ), (5435774303/10000000000 : ℝ), (5216564399/10000000000 : ℝ)] ![(5796330007897/50000000000000 : ℝ), (11345624221497/25000000000000 : ℝ), (43024843077411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474112027/2500000000 : ℝ)|^4483 ≤ (5796330007897/50000000000000 : ℝ)^3459
        have hw : |(-474112027/2500000000 : ℝ)|=(474112027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435774303/10000000000 : ℝ)|^4483 ≤ (11345624221497/25000000000000 : ℝ)^3459
        have hw : |(5435774303/10000000000 : ℝ)|=(5435774303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216564399/10000000000 : ℝ)|^4483 ≤ (43024843077411/100000000000000 : ℝ)^3459
        have hw : |(5216564399/10000000000 : ℝ)|=(5216564399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_1 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352640643/10000000000 : ℝ)*x 0 + (-2008762243/10000000000 : ℝ)*x 1 + (652070553/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352640643/10000000000 : ℝ)^4483 ≤ (44484997365123/100000000000000 : ℝ)^3459 := by
    have hnat : (5352640643 : ℕ)^4483*100000000000000^3459 ≤ 44484997365123^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352640643 10000000000 44484997365123 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008762243/10000000000 : ℝ)^4483 ≤ (499606370739/4000000000000 : ℝ)^3459 := by
    have hnat : (2008762243 : ℕ)^4483*4000000000000^3459 ≤ 499606370739^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008762243 10000000000 499606370739 4000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652070553/1250000000 : ℝ)^4483 ≤ (8604968668929/20000000000000 : ℝ)^3459 := by
    have hnat : (652070553 : ℕ)^4483*20000000000000^3459 ≤ 8604968668929^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652070553 1250000000 8604968668929 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352640643/10000000000 : ℝ), (-2008762243/10000000000 : ℝ), (652070553/1250000000 : ℝ)] ![(44484997365123/100000000000000 : ℝ), (499606370739/4000000000000 : ℝ), (8604968668929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352640643/10000000000 : ℝ)|^4483 ≤ (44484997365123/100000000000000 : ℝ)^3459
        have hw : |(5352640643/10000000000 : ℝ)|=(5352640643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2008762243/10000000000 : ℝ)|^4483 ≤ (499606370739/4000000000000 : ℝ)^3459
        have hw : |(-2008762243/10000000000 : ℝ)|=(2008762243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652070553/1250000000 : ℝ)|^4483 ≤ (8604968668929/20000000000000 : ℝ)^3459
        have hw : |(652070553/1250000000 : ℝ)|=(652070553/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_2 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535264063/1000000000 : ℝ)*x 0 + (5216564441/10000000000 : ℝ)*x 1 + (-3138691/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535264063/1000000000 : ℝ)^4483 ≤ (22242498612549/50000000000000 : ℝ)^3459 := by
    have hnat : (535264063 : ℕ)^4483*50000000000000^3459 ≤ 22242498612549^3459*1000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535264063 1000000000 22242498612549 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216564441/10000000000 : ℝ)^4483 ≤ (8604968705273/20000000000000 : ℝ)^3459 := by
    have hnat : (5216564441 : ℕ)^4483*20000000000000^3459 ≤ 8604968705273^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216564441 10000000000 8604968705273 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138691/15625000 : ℝ)^4483 ≤ (12490159244299/100000000000000 : ℝ)^3459 := by
    have hnat : (3138691 : ℕ)^4483*100000000000000^3459 ≤ 12490159244299^3459*15625000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138691 15625000 12490159244299 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535264063/1000000000 : ℝ), (5216564441/10000000000 : ℝ), (-3138691/15625000 : ℝ)] ![(22242498612549/50000000000000 : ℝ), (8604968705273/20000000000000 : ℝ), (12490159244299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535264063/1000000000 : ℝ)|^4483 ≤ (22242498612549/50000000000000 : ℝ)^3459
        have hw : |(535264063/1000000000 : ℝ)|=(535264063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216564441/10000000000 : ℝ)|^4483 ≤ (8604968705273/20000000000000 : ℝ)^3459
        have hw : |(5216564441/10000000000 : ℝ)|=(5216564441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3138691/15625000 : ℝ)|^4483 ≤ (12490159244299/100000000000000 : ℝ)^3459
        have hw : |(-3138691/15625000 : ℝ)|=(3138691/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_3 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278697697/10000000000 : ℝ)*x 0 + (1009886067/2500000000 : ℝ)*x 1 + (283123347/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278697697/10000000000 : ℝ)^4483 ≤ (4159827818997/12500000000000 : ℝ)^3459 := by
    have hnat : (4278697697 : ℕ)^4483*12500000000000^3459 ≤ 4159827818997^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278697697 10000000000 4159827818997 12500000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009886067/2500000000 : ℝ)^4483 ≤ (30888105765803/100000000000000 : ℝ)^3459 := by
    have hnat : (1009886067 : ℕ)^4483*100000000000000^3459 ≤ 30888105765803^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009886067 2500000000 30888105765803 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283123347/625000000 : ℝ)^4483 ≤ (2239579479163/6250000000000 : ℝ)^3459 := by
    have hnat : (283123347 : ℕ)^4483*6250000000000^3459 ≤ 2239579479163^3459*625000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283123347 625000000 2239579479163 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278697697/10000000000 : ℝ), (1009886067/2500000000 : ℝ), (283123347/625000000 : ℝ)] ![(4159827818997/12500000000000 : ℝ), (30888105765803/100000000000000 : ℝ), (2239579479163/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278697697/10000000000 : ℝ)|^4483 ≤ (4159827818997/12500000000000 : ℝ)^3459
        have hw : |(4278697697/10000000000 : ℝ)|=(4278697697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1009886067/2500000000 : ℝ)|^4483 ≤ (30888105765803/100000000000000 : ℝ)^3459
        have hw : |(1009886067/2500000000 : ℝ)|=(1009886067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283123347/625000000 : ℝ)|^4483 ≤ (2239579479163/6250000000000 : ℝ)^3459
        have hw : |(283123347/625000000 : ℝ)|=(283123347/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_4 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1896477947/10000000000 : ℝ)*x 0 + (1304422293/2500000000 : ℝ)*x 1 + (1358660309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896477947/10000000000 : ℝ)^4483 ≤ (724556025923/6250000000000 : ℝ)^3459 := by
    have hnat : (1896477947 : ℕ)^4483*6250000000000^3459 ≤ 724556025923^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896477947 10000000000 724556025923 6250000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304422293/2500000000 : ℝ)^4483 ≤ (21518433298857/50000000000000 : ℝ)^3459 := by
    have hnat : (1304422293 : ℕ)^4483*50000000000000^3459 ≤ 21518433298857^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304422293 2500000000 21518433298857 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358660309/2500000000 : ℝ)^4483 ≤ (45370236974419/100000000000000 : ℝ)^3459 := by
    have hnat : (1358660309 : ℕ)^4483*100000000000000^3459 ≤ 45370236974419^3459*2500000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358660309 2500000000 45370236974419 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1896477947/10000000000 : ℝ), (1304422293/2500000000 : ℝ), (1358660309/2500000000 : ℝ)] ![(724556025923/6250000000000 : ℝ), (21518433298857/50000000000000 : ℝ), (45370236974419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1896477947/10000000000 : ℝ)|^4483 ≤ (724556025923/6250000000000 : ℝ)^3459
        have hw : |(-1896477947/10000000000 : ℝ)|=(1896477947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304422293/2500000000 : ℝ)|^4483 ≤ (21518433298857/50000000000000 : ℝ)^3459
        have hw : |(1304422293/2500000000 : ℝ)|=(1304422293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358660309/2500000000 : ℝ)|^4483 ≤ (45370236974419/100000000000000 : ℝ)^3459
        have hw : |(1358660309/2500000000 : ℝ)|=(1358660309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_5 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295266659/10000000000 : ℝ)*x 0 + (-223835681/1250000000 : ℝ)*x 1 + (5434641249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295266659/10000000000 : ℝ)^4483 ≤ (43867994293999/100000000000000 : ℝ)^3459 := by
    have hnat : (5295266659 : ℕ)^4483*100000000000000^3459 ≤ 43867994293999^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295266659 10000000000 43867994293999 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223835681/1250000000 : ℝ)^4483 ≤ (10761768581253/100000000000000 : ℝ)^3459 := by
    have hnat : (223835681 : ℕ)^4483*100000000000000^3459 ≤ 10761768581253^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223835681 1250000000 10761768581253 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434641249/10000000000 : ℝ)^4483 ≤ (11342559278769/25000000000000 : ℝ)^3459 := by
    have hnat : (5434641249 : ℕ)^4483*25000000000000^3459 ≤ 11342559278769^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434641249 10000000000 11342559278769 25000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295266659/10000000000 : ℝ), (-223835681/1250000000 : ℝ), (5434641249/10000000000 : ℝ)] ![(43867994293999/100000000000000 : ℝ), (10761768581253/100000000000000 : ℝ), (11342559278769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295266659/10000000000 : ℝ)|^4483 ≤ (43867994293999/100000000000000 : ℝ)^3459
        have hw : |(5295266659/10000000000 : ℝ)|=(5295266659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223835681/1250000000 : ℝ)|^4483 ≤ (10761768581253/100000000000000 : ℝ)^3459
        have hw : |(-223835681/1250000000 : ℝ)|=(223835681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434641249/10000000000 : ℝ)|^4483 ≤ (11342559278769/25000000000000 : ℝ)^3459
        have hw : |(5434641249/10000000000 : ℝ)|=(5434641249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_6 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661908333/1250000000 : ℝ)*x 0 + (2717320621/5000000000 : ℝ)*x 1 + (-35813709/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661908333/1250000000 : ℝ)^4483 ≤ (43867994347683/100000000000000 : ℝ)^3459 := by
    have hnat : (661908333 : ℕ)^4483*100000000000000^3459 ≤ 43867994347683^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661908333 1250000000 43867994347683 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717320621/5000000000 : ℝ)^4483 ≤ (22685118519669/50000000000000 : ℝ)^3459 := by
    have hnat : (2717320621 : ℕ)^4483*50000000000000^3459 ≤ 22685118519669^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717320621 5000000000 22685118519669 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35813709/200000000 : ℝ)^4483 ≤ (10761768596831/100000000000000 : ℝ)^3459 := by
    have hnat : (35813709 : ℕ)^4483*100000000000000^3459 ≤ 10761768596831^3459*200000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35813709 200000000 10761768596831 100000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661908333/1250000000 : ℝ), (2717320621/5000000000 : ℝ), (-35813709/200000000 : ℝ)] ![(43867994347683/100000000000000 : ℝ), (22685118519669/50000000000000 : ℝ), (10761768596831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661908333/1250000000 : ℝ)|^4483 ≤ (43867994347683/100000000000000 : ℝ)^3459
        have hw : |(661908333/1250000000 : ℝ)|=(661908333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717320621/5000000000 : ℝ)|^4483 ≤ (22685118519669/50000000000000 : ℝ)^3459
        have hw : |(2717320621/5000000000 : ℝ)|=(2717320621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35813709/200000000 : ℝ)|^4483 ≤ (10761768596831/100000000000000 : ℝ)^3459
        have hw : |(-35813709/200000000 : ℝ)|=(35813709/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1493_s5_7 (p : ℝ) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4278764421/10000000000 : ℝ)*x 0 + (2263728567/5000000000 : ℝ)*x 1 + (505259899/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4278764421/10000000000 : ℝ)^4483 ≤ (16639647574539/50000000000000 : ℝ)^3459 := by
    have hnat : (4278764421 : ℕ)^4483*50000000000000^3459 ≤ 16639647574539^3459*10000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4278764421 10000000000 16639647574539 50000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263728567/5000000000 : ℝ)^4483 ≤ (716149508971/2000000000000 : ℝ)^3459 := by
    have hnat : (2263728567 : ℕ)^4483*2000000000000^3459 ≤ 716149508971^3459*5000000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263728567 5000000000 716149508971 2000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505259899/1250000000 : ℝ)^4483 ≤ (6182645878783/20000000000000 : ℝ)^3459 := by
    have hnat : (505259899 : ℕ)^4483*20000000000000^3459 ≤ 6182645878783^3459*1250000000^4483 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505259899 1250000000 6182645878783 20000000000000 4483 3459 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4483/1024 : ℝ)) 4483 3459 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4278764421/10000000000 : ℝ), (2263728567/5000000000 : ℝ), (505259899/1250000000 : ℝ)] ![(16639647574539/50000000000000 : ℝ), (716149508971/2000000000000 : ℝ), (6182645878783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4278764421/10000000000 : ℝ)|^4483 ≤ (16639647574539/50000000000000 : ℝ)^3459
        have hw : |(4278764421/10000000000 : ℝ)|=(4278764421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263728567/5000000000 : ℝ)|^4483 ≤ (716149508971/2000000000000 : ℝ)^3459
        have hw : |(2263728567/5000000000 : ℝ)|=(2263728567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505259899/1250000000 : ℝ)|^4483 ≤ (6182645878783/20000000000000 : ℝ)^3459
        have hw : |(505259899/1250000000 : ℝ)|=(505259899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1493_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10839/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1083/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1083/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1083/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1083/10000 : ℝ) ^ (4481/1024 : ℝ) ≤ (5964262536442743/100000000000000000000 : ℝ) := by
    have hpowers : (1083/10000 : ℝ)^4481 ≤ (5964262536442743/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1083 : ℕ)^4481*100000000000000000000^1024 ≤ 5964262536442743^1024*10000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1083 10000 5964262536442743 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1083/10000 : ℝ)) (X := (5964262536442743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4481/1024 : ℝ) ≤ (28547053811456781/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4481 ≤ (28547053811456781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4481*100000000000000000000^1024 ≤ 28547053811456781^1024*100000^4481 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 28547053811456781 100000000000000000000 4481 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (28547053811456781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005964262536442743/50000000000000000000 : ℝ) ≤ (2000054515722711/2000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50005964262536442743/50000000000000000000 : ℝ)^1024 ≤ (2000054515722711/2000000000000000 : ℝ)^4481 := by
      have hnat : (50005964262536442743 : ℕ)^1024*2000000000000000^4481 ≤ 2000054515722711^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005964262536442743 50000000000000000000 2000054515722711 2000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000054515722711/2000000000000000 : ℝ)) (X := (50005964262536442743/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008627829086974881/25000000000000000000 : ℝ) ≤ (5000394274540903/5000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (25008627829086974881/25000000000000000000 : ℝ)^1024 ≤ (5000394274540903/5000000000000000 : ℝ)^4481 := by
      have hnat : (25008627829086974881 : ℕ)^1024*5000000000000000^4481 ≤ 5000394274540903^4481*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008627829086974881 25000000000000000000 5000394274540903 5000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000394274540903/5000000000000000 : ℝ)) (X := (25008627829086974881/25000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028547053811456781/50000000000000000000 : ℝ) ≤ (10001304519550057/10000000000000000 : ℝ) ^ (4481/1024 : ℝ) := by
    have hpowers : (50028547053811456781/50000000000000000000 : ℝ)^1024 ≤ (10001304519550057/10000000000000000 : ℝ)^4481 := by
      have hnat : (50028547053811456781 : ℕ)^1024*10000000000000000^4481 ≤ 10001304519550057^4481*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028547053811456781 50000000000000000000 10001304519550057 10000000000000000 1024 4481 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001304519550057/10000000000000000 : ℝ)) (X := (50028547053811456781/50000000000000000000 : ℝ)) (by norm_num) 4481 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5964262536442743/100000000000000000000 : ℝ) ≤ ((3105339601561215739/3106000000000000000 : ℝ)+2*(515970468251/465900000000000 : ℝ)*(1083/10000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (3105339601561215739/3106000000000000000 : ℝ)+2*(515970468251/465900000000000 : ℝ)*(1083/10000 : ℝ)=(2000054515722711/2000000000000000 : ℝ) by norm_num, show 1+2*(5964262536442743/100000000000000000000 : ℝ)=(50005964262536442743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28547053811456781/100000000000000000000 : ℝ)+(5964262536442743/100000000000000000000 : ℝ) ≤ ((3105339601561215739/3106000000000000000 : ℝ)+(515970468251/465900000000000 : ℝ)*((15489/100000 : ℝ)+(1083/10000 : ℝ)))^(4481/1024 : ℝ) := by
    rw [show (3105339601561215739/3106000000000000000 : ℝ)+(515970468251/465900000000000 : ℝ)*((15489/100000 : ℝ)+(1083/10000 : ℝ))=(5000394274540903/5000000000000000 : ℝ) by norm_num, show 1+(28547053811456781/100000000000000000000 : ℝ)+(5964262536442743/100000000000000000000 : ℝ)=(25008627829086974881/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28547053811456781/100000000000000000000 : ℝ) ≤ ((3105339601561215739/3106000000000000000 : ℝ)+2*(515970468251/465900000000000 : ℝ)*(15489/100000 : ℝ))^(4481/1024 : ℝ) := by
    rw [show (3105339601561215739/3106000000000000000 : ℝ)+2*(515970468251/465900000000000 : ℝ)*(15489/100000 : ℝ)=(10001304519550057/10000000000000000 : ℝ) by norm_num, show 1+2*(28547053811456781/100000000000000000000 : ℝ)=(50028547053811456781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3105339601561215739/3106000000000000000 : ℝ)*(X 1 0+X 2 0)+(515970468251/465900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (3105339601561215739/3106000000000000000 : ℝ)) (alpha := (515970468251/465900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3105339601561215739/3106000000000000000 : ℝ)*(X 0 1+X 2 1)+(515970468251/465900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (3105339601561215739/3106000000000000000 : ℝ)) (alpha := (515970468251/465900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3105339601561215739/3106000000000000000 : ℝ)*(X 0 2+X 1 2)+(515970468251/465900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4481/1024 : ℝ)) (lo := (1083/10000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (3105339601561215739/3106000000000000000 : ℝ)) (alpha := (515970468251/465900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-474112027/2500000000 : ℝ)*X 0 0+(5435774303/10000000000 : ℝ)*X 0 1+(5216564399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352640643/10000000000 : ℝ)*X 1 0+(-2008762243/10000000000 : ℝ)*X 1 1+(652070553/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535264063/1000000000 : ℝ)*X 2 0+(5216564441/10000000000 : ℝ)*X 2 1+(-3138691/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4278697697/10000000000 : ℝ)*X 0 0+(1009886067/2500000000 : ℝ)*X 0 1+(283123347/625000000 : ℝ)*X 0 2+(4278697697/10000000000 : ℝ)*X 1 0+(1009886067/2500000000 : ℝ)*X 1 1+(283123347/625000000 : ℝ)*X 1 2+(4278697697/10000000000 : ℝ)*X 2 0+(1009886067/2500000000 : ℝ)*X 2 1+(283123347/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1896477947/10000000000 : ℝ)*X 0 0+(1304422293/2500000000 : ℝ)*X 0 1+(1358660309/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295266659/10000000000 : ℝ)*X 1 0+(-223835681/1250000000 : ℝ)*X 1 1+(5434641249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661908333/1250000000 : ℝ)*X 2 0+(2717320621/5000000000 : ℝ)*X 2 1+(-35813709/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4278764421/10000000000 : ℝ)*X 0 0+(2263728567/5000000000 : ℝ)*X 0 1+(505259899/1250000000 : ℝ)*X 0 2+(4278764421/10000000000 : ℝ)*X 1 0+(2263728567/5000000000 : ℝ)*X 1 1+(505259899/1250000000 : ℝ)*X 1 2+(4278764421/10000000000 : ℝ)*X 2 0+(2263728567/5000000000 : ℝ)*X 2 1+(505259899/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1493_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (676904000299600297308594431/77650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1564400509/100000000000000 : ℝ)*(base19) + (1452693589/100000000000000 : ℝ)*(base23) + (26931123/50000000000000 : ℝ)*(lower2) + (13668021/6250000000000 : ℝ)*(upper3) + (18325899/12500000000000 : ℝ)*(upper5) + (1650235207562657/50000000000000 : ℝ)*(major0) + (1650235207562657/50000000000000 : ℝ)*(major1) + (1650235207562657/50000000000000 : ℝ)*(major2) + (4561863438836777/100000000000000 : ℝ)*(sp0) + (912377336783233/20000000000000 : ℝ)*(sp1) + (1140471698905771/25000000000000 : ℝ)*(sp2) + (1019520270853041/50000000000000 : ℝ)*(sp3) + (24809479897/100000000000000 : ℝ)*(sp4) + (2937412193/25000000000000 : ℝ)*(sp7) + (1019526145677427/50000000000000 : ℝ)*(f.failure) + (2280944124158337/50000000000000 : ℝ)*(f.sum) + (9256599949469/23295000000000000000000000000 : ℝ)*base65 + (2458661990509215569/465900000000000000000000000000000 : ℝ)*base67 + (1242417821708384431/465900000000000000000000000000000 : ℝ)*base70 + (1827724313069415569/465900000000000000000000000000000 : ℝ)*base71 + (104328514136759/23295000000000000000000000000 : ℝ)*base73 + (2243362468046115569/465900000000000000000000000000000 : ℝ)*base75 + (1154319338498084431/465900000000000000000000000000000 : ℝ)*base78 + (3261575727128115569/465900000000000000000000000000000 : ℝ)*base79 + (5785875799973/11647500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (14918653/5000000000000000000000 : ℝ)*base90 + (14918653/5000000000000000000000 : ℝ)*base92 + (14918653/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (776368350252778286379023511/77650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66442429/4000000000000 : ℝ)*(base19) + (5575303/312500000000 : ℝ)*(base23) + (52618949/25000000000000 : ℝ)*(upper3) + (55025411/100000000000000 : ℝ)*(lower4) + (110349911/50000000000000 : ℝ)*(upper5) + (1667390671238583/50000000000000 : ℝ)*(major0) + (1667390671238583/50000000000000 : ℝ)*(major1) + (1667390671238583/50000000000000 : ℝ)*(major2) + (12698509391/50000000000000 : ℝ)*(sp1) + (26760171383/100000000000000 : ℝ)*(sp2) + (2304656272069951/50000000000000 : ℝ)*(sp4) + (921857097212079/20000000000000 : ℝ)*(sp5) + (115232099996789/2500000000000 : ℝ)*(sp6) + (515062451884401/25000000000000 : ℝ)*(sp7) + (515062451884401/25000000000000 : ℝ)*(f.failure) + (2304656272069951/50000000000000 : ℝ)*(f.sum) + (1372455565843/1941250000000000000000000000 : ℝ)*base65 + (127027487101877837/155300000000000000000000000000000 : ℝ)*base67 + (1545262598726122163/155300000000000000000000000000000 : ℝ)*base70 + (190854803276377837/155300000000000000000000000000000 : ℝ)*base71 + (458121672329/242656250000000000000000000 : ℝ)*base74 + (1460010050446422163/155300000000000000000000000000000 : ℝ)*base76 + (1344649098568322163/155300000000000000000000000000000 : ℝ)*base78 + (2293156574626822163/155300000000000000000000000000000 : ℝ)*base80 + (2600831719751/3882500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (25571361/2500000000000000000000 : ℝ)*base89 + (25571361/2500000000000000000000 : ℝ)*base91 + (25571361/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1493_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1083/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1493_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1493_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1493_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1493_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1493_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4481/1024 : ℝ) ≤ p) (hpb : p ≤ (4483/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161862961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16073/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5147/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10839/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1493_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

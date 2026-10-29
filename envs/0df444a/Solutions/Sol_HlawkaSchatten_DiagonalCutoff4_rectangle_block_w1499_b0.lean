-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1499_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:15.759509+00:00
-- url     : https://prove2.me/submissions/d0c43700-0215-4173-8bb7-fbebb633d370

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
theorem support_rectangle_w1499_s0_0 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1699709037/10000000000 : ℝ)*x 0 + (5922908143/10000000000 : ℝ)*x 1 + (4849717681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1699709037/10000000000 : ℝ)^4495 ≤ (1007680583503/10000000000000 : ℝ)^3471 := by
    have hnat : (1699709037 : ℕ)^4495*10000000000000^3471 ≤ 1007680583503^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699709037 10000000000 1007680583503 10000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5922908143/10000000000 : ℝ)^4495 ≤ (50749201952283/100000000000000 : ℝ)^3471 := by
    have hnat : (5922908143 : ℕ)^4495*100000000000000^3471 ≤ 50749201952283^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5922908143 10000000000 50749201952283 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4849717681/10000000000 : ℝ)^4495 ≤ (19586996099769/50000000000000 : ℝ)^3471 := by
    have hnat : (4849717681 : ℕ)^4495*50000000000000^3471 ≤ 19586996099769^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4849717681 10000000000 19586996099769 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1699709037/10000000000 : ℝ), (5922908143/10000000000 : ℝ), (4849717681/10000000000 : ℝ)] ![(1007680583503/10000000000000 : ℝ), (50749201952283/100000000000000 : ℝ), (19586996099769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1699709037/10000000000 : ℝ)|^4495 ≤ (1007680583503/10000000000000 : ℝ)^3471
        have hw : |(-1699709037/10000000000 : ℝ)|=(1699709037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5922908143/10000000000 : ℝ)|^4495 ≤ (50749201952283/100000000000000 : ℝ)^3471
        have hw : |(5922908143/10000000000 : ℝ)|=(5922908143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4849717681/10000000000 : ℝ)|^4495 ≤ (19586996099769/50000000000000 : ℝ)^3471
        have hw : |(4849717681/10000000000 : ℝ)|=(4849717681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_1 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2740407279/5000000000 : ℝ)*x 0 + (-2302268309/10000000000 : ℝ)*x 1 + (1212429413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2740407279/5000000000 : ℝ)^4495 ≤ (2868668034793/6250000000000 : ℝ)^3471 := by
    have hnat : (2740407279 : ℕ)^4495*6250000000000^3471 ≤ 2868668034793^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740407279 5000000000 2868668034793 6250000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2302268309/10000000000 : ℝ)^4495 ≤ (14927319532109/100000000000000 : ℝ)^3471 := by
    have hnat : (2302268309 : ℕ)^4495*100000000000000^3471 ≤ 14927319532109^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302268309 10000000000 14927319532109 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1212429413/2500000000 : ℝ)^4495 ≤ (39173991896181/100000000000000 : ℝ)^3471 := by
    have hnat : (1212429413 : ℕ)^4495*100000000000000^3471 ≤ 39173991896181^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1212429413 2500000000 39173991896181 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2740407279/5000000000 : ℝ), (-2302268309/10000000000 : ℝ), (1212429413/2500000000 : ℝ)] ![(2868668034793/6250000000000 : ℝ), (14927319532109/100000000000000 : ℝ), (39173991896181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2740407279/5000000000 : ℝ)|^4495 ≤ (2868668034793/6250000000000 : ℝ)^3471
        have hw : |(2740407279/5000000000 : ℝ)|=(2740407279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2302268309/10000000000 : ℝ)|^4495 ≤ (14927319532109/100000000000000 : ℝ)^3471
        have hw : |(-2302268309/10000000000 : ℝ)|=(2302268309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1212429413/2500000000 : ℝ)|^4495 ≤ (39173991896181/100000000000000 : ℝ)^3471
        have hw : |(1212429413/2500000000 : ℝ)|=(1212429413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_2 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5480814597/10000000000 : ℝ)*x 0 + (2424858829/5000000000 : ℝ)*x 1 + (-2302268251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5480814597/10000000000 : ℝ)^4495 ≤ (11474672244911/25000000000000 : ℝ)^3471 := by
    have hnat : (5480814597 : ℕ)^4495*25000000000000^3471 ≤ 11474672244911^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480814597 10000000000 11474672244911 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2424858829/5000000000 : ℝ)^4495 ≤ (1224187248717/3125000000000 : ℝ)^3471 := by
    have hnat : (2424858829 : ℕ)^4495*3125000000000^3471 ≤ 1224187248717^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424858829 5000000000 1224187248717 3125000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2302268251/10000000000 : ℝ)^4495 ≤ (14927319045109/100000000000000 : ℝ)^3471 := by
    have hnat : (2302268251 : ℕ)^4495*100000000000000^3471 ≤ 14927319045109^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302268251 10000000000 14927319045109 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5480814597/10000000000 : ℝ), (2424858829/5000000000 : ℝ), (-2302268251/10000000000 : ℝ)] ![(11474672244911/25000000000000 : ℝ), (1224187248717/3125000000000 : ℝ), (14927319045109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5480814597/10000000000 : ℝ)|^4495 ≤ (11474672244911/25000000000000 : ℝ)^3471
        have hw : |(5480814597/10000000000 : ℝ)|=(5480814597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2424858829/5000000000 : ℝ)|^4495 ≤ (1224187248717/3125000000000 : ℝ)^3471
        have hw : |(2424858829/5000000000 : ℝ)|=(2424858829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2302268251/10000000000 : ℝ)|^4495 ≤ (14927319045109/100000000000000 : ℝ)^3471
        have hw : |(-2302268251/10000000000 : ℝ)|=(2302268251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_3 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4148667671/10000000000 : ℝ)*x 0 + (3091240021/10000000000 : ℝ)*x 1 + (5502515059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4148667671/10000000000 : ℝ)^4495 ≤ (32002628014857/100000000000000 : ℝ)^3471 := by
    have hnat : (4148667671 : ℕ)^4495*100000000000000^3471 ≤ 32002628014857^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148667671 10000000000 32002628014857 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091240021/10000000000 : ℝ)^4495 ≤ (10931601893123/50000000000000 : ℝ)^3471 := by
    have hnat : (3091240021 : ℕ)^4495*50000000000000^3471 ≤ 10931601893123^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091240021 10000000000 10931601893123 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5502515059/10000000000 : ℝ)^4495 ≤ (23067084093681/50000000000000 : ℝ)^3471 := by
    have hnat : (5502515059 : ℕ)^4495*50000000000000^3471 ≤ 23067084093681^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502515059 10000000000 23067084093681 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4148667671/10000000000 : ℝ), (3091240021/10000000000 : ℝ), (5502515059/10000000000 : ℝ)] ![(32002628014857/100000000000000 : ℝ), (10931601893123/50000000000000 : ℝ), (23067084093681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4148667671/10000000000 : ℝ)|^4495 ≤ (32002628014857/100000000000000 : ℝ)^3471
        have hw : |(4148667671/10000000000 : ℝ)|=(4148667671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091240021/10000000000 : ℝ)|^4495 ≤ (10931601893123/50000000000000 : ℝ)^3471
        have hw : |(3091240021/10000000000 : ℝ)|=(3091240021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5502515059/10000000000 : ℝ)|^4495 ≤ (23067084093681/50000000000000 : ℝ)^3471
        have hw : |(5502515059/10000000000 : ℝ)|=(5502515059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_4 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-212917763/1250000000 : ℝ)*x 0 + (975431643/2000000000 : ℝ)*x 1 + (5894482857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212917763/1250000000 : ℝ)^4495 ≤ (10104707725923/100000000000000 : ℝ)^3471 := by
    have hnat : (212917763 : ℕ)^4495*100000000000000^3471 ≤ 10104707725923^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212917763 1250000000 10104707725923 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975431643/2000000000 : ℝ)^4495 ≤ (39461275814819/100000000000000 : ℝ)^3471 := by
    have hnat : (975431643 : ℕ)^4495*100000000000000^3471 ≤ 39461275814819^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975431643 2000000000 39461275814819 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5894482857/10000000000 : ℝ)^4495 ≤ (50434016443159/100000000000000 : ℝ)^3471 := by
    have hnat : (5894482857 : ℕ)^4495*100000000000000^3471 ≤ 50434016443159^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5894482857 10000000000 50434016443159 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212917763/1250000000 : ℝ), (975431643/2000000000 : ℝ), (5894482857/10000000000 : ℝ)] ![(10104707725923/100000000000000 : ℝ), (39461275814819/100000000000000 : ℝ), (50434016443159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212917763/1250000000 : ℝ)|^4495 ≤ (10104707725923/100000000000000 : ℝ)^3471
        have hw : |(-212917763/1250000000 : ℝ)|=(212917763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(975431643/2000000000 : ℝ)|^4495 ≤ (39461275814819/100000000000000 : ℝ)^3471
        have hw : |(975431643/2000000000 : ℝ)|=(975431643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5894482857/10000000000 : ℝ)|^4495 ≤ (50434016443159/100000000000000 : ℝ)^3471
        have hw : |(5894482857/10000000000 : ℝ)|=(5894482857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_5 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (518767167/1000000000 : ℝ)*x 0 + (-628751513/5000000000 : ℝ)*x 1 + (5894482909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518767167/1000000000 : ℝ)^4495 ≤ (10686238332393/25000000000000 : ℝ)^3471 := by
    have hnat : (518767167 : ℕ)^4495*25000000000000^3471 ≤ 10686238332393^3471*1000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518767167 1000000000 10686238332393 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628751513/5000000000 : ℝ)^4495 ≤ (3410514817879/50000000000000 : ℝ)^3471 := by
    have hnat : (628751513 : ℕ)^4495*50000000000000^3471 ≤ 3410514817879^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628751513 5000000000 3410514817879 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5894482909/10000000000 : ℝ)^4495 ≤ (50434017019337/100000000000000 : ℝ)^3471 := by
    have hnat : (5894482909 : ℕ)^4495*100000000000000^3471 ≤ 50434017019337^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5894482909 10000000000 50434017019337 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518767167/1000000000 : ℝ), (-628751513/5000000000 : ℝ), (5894482909/10000000000 : ℝ)] ![(10686238332393/25000000000000 : ℝ), (3410514817879/50000000000000 : ℝ), (50434017019337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518767167/1000000000 : ℝ)|^4495 ≤ (10686238332393/25000000000000 : ℝ)^3471
        have hw : |(518767167/1000000000 : ℝ)|=(518767167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-628751513/5000000000 : ℝ)|^4495 ≤ (3410514817879/50000000000000 : ℝ)^3471
        have hw : |(-628751513/5000000000 : ℝ)|=(628751513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5894482909/10000000000 : ℝ)|^4495 ≤ (50434017019337/100000000000000 : ℝ)^3471
        have hw : |(5894482909/10000000000 : ℝ)|=(5894482909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_6 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2593835851/5000000000 : ℝ)*x 0 + (5894482833/10000000000 : ℝ)*x 1 + (-1257503097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2593835851/5000000000 : ℝ)^4495 ≤ (4274495367103/10000000000000 : ℝ)^3471 := by
    have hnat : (2593835851 : ℕ)^4495*10000000000000^3471 ≤ 4274495367103^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593835851 5000000000 4274495367103 10000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5894482833/10000000000 : ℝ)^4495 ≤ (50434016177231/100000000000000 : ℝ)^3471 := by
    have hnat : (5894482833 : ℕ)^4495*100000000000000^3471 ≤ 50434016177231^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5894482833 10000000000 50434016177231 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257503097/10000000000 : ℝ)^4495 ≤ (3410515067249/50000000000000 : ℝ)^3471 := by
    have hnat : (1257503097 : ℕ)^4495*50000000000000^3471 ≤ 3410515067249^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257503097 10000000000 3410515067249 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2593835851/5000000000 : ℝ), (5894482833/10000000000 : ℝ), (-1257503097/10000000000 : ℝ)] ![(4274495367103/10000000000000 : ℝ), (50434016177231/100000000000000 : ℝ), (3410515067249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2593835851/5000000000 : ℝ)|^4495 ≤ (4274495367103/10000000000000 : ℝ)^3471
        have hw : |(2593835851/5000000000 : ℝ)|=(2593835851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5894482833/10000000000 : ℝ)|^4495 ≤ (50434016177231/100000000000000 : ℝ)^3471
        have hw : |(5894482833/10000000000 : ℝ)|=(5894482833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1257503097/10000000000 : ℝ)|^4495 ≤ (3410515067249/50000000000000 : ℝ)^3471
        have hw : |(-1257503097/10000000000 : ℝ)|=(1257503097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s0_7 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207841539/500000000 : ℝ)*x 0 + (2720430397/5000000000 : ℝ)*x 1 + (394388359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207841539/500000000 : ℝ)^4495 ≤ (6416839722677/20000000000000 : ℝ)^3471 := by
    have hnat : (207841539 : ℕ)^4495*20000000000000^3471 ≤ 6416839722677^3471*500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207841539 500000000 6416839722677 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720430397/5000000000 : ℝ)^4495 ≤ (22200125009/48828125000 : ℝ)^3471 := by
    have hnat : (2720430397 : ℕ)^4495*48828125000^3471 ≤ 22200125009^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720430397 5000000000 22200125009 48828125000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394388359/1250000000 : ℝ)^4495 ≤ (22449945350259/100000000000000 : ℝ)^3471 := by
    have hnat : (394388359 : ℕ)^4495*100000000000000^3471 ≤ 22449945350259^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394388359 1250000000 22449945350259 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207841539/500000000 : ℝ), (2720430397/5000000000 : ℝ), (394388359/1250000000 : ℝ)] ![(6416839722677/20000000000000 : ℝ), (22200125009/48828125000 : ℝ), (22449945350259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207841539/500000000 : ℝ)|^4495 ≤ (6416839722677/20000000000000 : ℝ)^3471
        have hw : |(207841539/500000000 : ℝ)|=(207841539/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720430397/5000000000 : ℝ)|^4495 ≤ (22200125009/48828125000 : ℝ)^3471
        have hw : |(2720430397/5000000000 : ℝ)|=(2720430397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394388359/1250000000 : ℝ)|^4495 ≤ (22449945350259/100000000000000 : ℝ)^3471
        have hw : |(394388359/1250000000 : ℝ)|=(394388359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1499_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1329/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25653/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4493/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4493 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4493*1^1024 ≤ 0^1024*1^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4493/1024 : ℝ) ≤ (358914071040462379/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4493 ≤ (358914071040462379/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4493*20000000000000000000^1024 ≤ 358914071040462379^1024*5^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 358914071040462379 20000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (358914071040462379/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4493 := by
      have hnat : (1 : ℕ)^1024*1^4493 ≤ 1^4493*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20358914071040462379/20000000000000000000 : ℝ) ≤ (10040619685055037/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (20358914071040462379/20000000000000000000 : ℝ)^1024 ≤ (10040619685055037/10000000000000000 : ℝ)^4493 := by
      have hnat : (20358914071040462379 : ℕ)^1024*10000000000000000^4493 ≤ 10040619685055037^4493*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20358914071040462379 20000000000000000000 10040619685055037 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10040619685055037/10000000000000000 : ℝ)) (X := (20358914071040462379/20000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10358914071040462379/10000000000000000000 : ℝ) ≤ (5040619685055037/5000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (10358914071040462379/10000000000000000000 : ℝ)^1024 ≤ (5040619685055037/5000000000000000 : ℝ)^4493 := by
      have hnat : (10358914071040462379 : ℕ)^1024*5000000000000000^4493 ≤ 5040619685055037^4493*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10358914071040462379 10000000000000000000 5040619685055037 5000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5040619685055037/5000000000000000 : ℝ)) (X := (10358914071040462379/10000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(40619685055037/4000000000000000 : ℝ)*(0 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40619685055037/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(358914071040462379/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(40619685055037/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4493/1024 : ℝ) := by
    rw [show (1 : ℝ)+(40619685055037/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10040619685055037/10000000000000000 : ℝ) by norm_num, show 1+(358914071040462379/20000000000000000000 : ℝ)+(0 : ℝ)=(20358914071040462379/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(358914071040462379/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(40619685055037/4000000000000000 : ℝ)*(2/5 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(40619685055037/4000000000000000 : ℝ)*(2/5 : ℝ)=(5040619685055037/5000000000000000 : ℝ) by norm_num, show 1+2*(358914071040462379/20000000000000000000 : ℝ)=(10358914071040462379/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(40619685055037/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40619685055037/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(40619685055037/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40619685055037/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(40619685055037/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (40619685055037/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1699709037/10000000000 : ℝ)*X 0 0+(5922908143/10000000000 : ℝ)*X 0 1+(4849717681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2740407279/5000000000 : ℝ)*X 1 0+(-2302268309/10000000000 : ℝ)*X 1 1+(1212429413/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5480814597/10000000000 : ℝ)*X 2 0+(2424858829/5000000000 : ℝ)*X 2 1+(-2302268251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4148667671/10000000000 : ℝ)*X 0 0+(3091240021/10000000000 : ℝ)*X 0 1+(5502515059/10000000000 : ℝ)*X 0 2+(4148667671/10000000000 : ℝ)*X 1 0+(3091240021/10000000000 : ℝ)*X 1 1+(5502515059/10000000000 : ℝ)*X 1 2+(4148667671/10000000000 : ℝ)*X 2 0+(3091240021/10000000000 : ℝ)*X 2 1+(5502515059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-212917763/1250000000 : ℝ)*X 0 0+(975431643/2000000000 : ℝ)*X 0 1+(5894482857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518767167/1000000000 : ℝ)*X 1 0+(-628751513/5000000000 : ℝ)*X 1 1+(5894482909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2593835851/5000000000 : ℝ)*X 2 0+(5894482833/10000000000 : ℝ)*X 2 1+(-1257503097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((207841539/500000000 : ℝ)*X 0 0+(2720430397/5000000000 : ℝ)*X 0 1+(394388359/1250000000 : ℝ)*X 0 2+(207841539/500000000 : ℝ)*X 1 0+(2720430397/5000000000 : ℝ)*X 1 1+(394388359/1250000000 : ℝ)*X 1 2+(207841539/500000000 : ℝ)*X 2 0+(2720430397/5000000000 : ℝ)*X 2 1+(394388359/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50592748593295813652121/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1201231/1562500000000 : ℝ)*(base1) + (908477813/50000000000000 : ℝ)*(base19) + (911793073/50000000000000 : ℝ)*(base23) + (44089027/20000000000000 : ℝ)*(upper3) + (238620173/100000000000000 : ℝ)*(upper5) + (42079302876911/6250000000000 : ℝ)*(major0) + (42079302876911/6250000000000 : ℝ)*(major1) + (42079302876911/6250000000000 : ℝ)*(major2) + (465903522971269/50000000000000 : ℝ)*(sp0) + (93181161625941/10000000000000 : ℝ)*(sp1) + (93181160962889/10000000000000 : ℝ)*(sp2) + (51840134948831/12500000000000 : ℝ)*(sp3) + (6464151283/100000000000000 : ℝ)*(sp4) + (1416274343/50000000000000 : ℝ)*(sp7) + (207361994509059/50000000000000 : ℝ)*(f.failure) + (931813433215037/100000000000000 : ℝ)*(f.sum) + (10884714675707/12500000000000000000000000000 : ℝ)*base65 + (24441205224293/25000000000000000000000000000 : ℝ)*base68 + (92699736774293/25000000000000000000000000000 : ℝ)*base70 + (35749195149293/25000000000000000000000000000 : ℝ)*base72 + (5095810974293/12500000000000000000000000000 : ℝ)*base74 + (98764377950707/25000000000000000000000000000 : ℝ)*base75 + (91559608899293/25000000000000000000000000000 : ℝ)*base78 + (116973473750707/25000000000000000000000000000 : ℝ)*base79 + (29181616374293/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (750937/1250000000000000000000 : ℝ)*base90 + (750937/1250000000000000000000 : ℝ)*base92 + (750937/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21236481582716862441033/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381914513/100000000000000 : ℝ)*(base19) + (194563913/50000000000000 : ℝ)*(base23) + (22624439/50000000000000 : ℝ)*(base32) + (58600403/100000000000000 : ℝ)*(upper3) + (6775689/20000000000000 : ℝ)*(upper5) + (88778912613703/12500000000000 : ℝ)*(major0) + (88778912613703/12500000000000 : ℝ)*(major1) + (88778912613703/12500000000000 : ℝ)*(major2) + (123600371/12500000000000 : ℝ)*(sp1) + (1009152297/100000000000000 : ℝ)*(sp2) + (982970212110453/100000000000000 : ℝ)*(sp4) + (245742210348243/25000000000000 : ℝ)*(sp5) + (98296881383033/10000000000000 : ℝ)*(sp6) + (27343267989331/6250000000000 : ℝ)*(sp7) + (218746166539087/50000000000000 : ℝ)*(f.failure) + (982970212110453/100000000000000 : ℝ)*(f.sum) + (25070868827989/25000000000000000000000000000 : ℝ)*base66 + (47810045577989/50000000000000000000000000000 : ℝ)*base68 + (128980758722011/50000000000000000000000000000 : ℝ)*base69 + (108154962172011/50000000000000000000000000000 : ℝ)*base71 + (146301590627989/25000000000000000000000000000 : ℝ)*base74 + (405615635572011/50000000000000000000000000000 : ℝ)*base75 + (40569517077989/50000000000000000000000000000 : ℝ)*base78 + (492411758372011/50000000000000000000000000000 : ℝ)*base79 + (71397113502989/25000000000000000000000000000 : ℝ)*base82 + (349059/1250000000000000000000 : ℝ)*base89 + (349059/1250000000000000000000 : ℝ)*base91 + (349059/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1499_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1329/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25653/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1499_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1499_s1_0 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-116058071/625000000 : ℝ)*x 0 + (5579303961/10000000000 : ℝ)*x 1 + (5092330091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116058071/625000000 : ℝ)^4495 ≤ (282499950047/2500000000000 : ℝ)^3471 := by
    have hnat : (116058071 : ℕ)^4495*2500000000000^3471 ≤ 282499950047^3471*625000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116058071 625000000 282499950047 2500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5579303961/10000000000 : ℝ)^4495 ≤ (23484813617071/50000000000000 : ℝ)^3471 := by
    have hnat : (5579303961 : ℕ)^4495*50000000000000^3471 ≤ 23484813617071^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5579303961 10000000000 23484813617071 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5092330091/10000000000 : ℝ)^4495 ≤ (10432593687027/25000000000000 : ℝ)^3471 := by
    have hnat : (5092330091 : ℕ)^4495*25000000000000^3471 ≤ 10432593687027^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092330091 10000000000 10432593687027 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116058071/625000000 : ℝ), (5579303961/10000000000 : ℝ), (5092330091/10000000000 : ℝ)] ![(282499950047/2500000000000 : ℝ), (23484813617071/50000000000000 : ℝ), (10432593687027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116058071/625000000 : ℝ)|^4495 ≤ (282499950047/2500000000000 : ℝ)^3471
        have hw : |(-116058071/625000000 : ℝ)|=(116058071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5579303961/10000000000 : ℝ)|^4495 ≤ (23484813617071/50000000000000 : ℝ)^3471
        have hw : |(5579303961/10000000000 : ℝ)|=(5579303961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5092330091/10000000000 : ℝ)|^4495 ≤ (10432593687027/25000000000000 : ℝ)^3471
        have hw : |(5092330091/10000000000 : ℝ)|=(5092330091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_1 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389006379/10000000000 : ℝ)*x 0 + (-264221881/1250000000 : ℝ)*x 1 + (5092330729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389006379/10000000000 : ℝ)^4495 ≤ (44905497175769/100000000000000 : ℝ)^3471 := by
    have hnat : (5389006379 : ℕ)^4495*100000000000000^3471 ≤ 44905497175769^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389006379 10000000000 44905497175769 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264221881/1250000000 : ℝ)^4495 ≤ (2672824257087/20000000000000 : ℝ)^3471 := by
    have hnat : (264221881 : ℕ)^4495*20000000000000^3471 ≤ 2672824257087^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264221881 1250000000 2672824257087 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5092330729/10000000000 : ℝ)^4495 ≤ (5216297689847/12500000000000 : ℝ)^3471 := by
    have hnat : (5092330729 : ℕ)^4495*12500000000000^3471 ≤ 5216297689847^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092330729 10000000000 5216297689847 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389006379/10000000000 : ℝ), (-264221881/1250000000 : ℝ), (5092330729/10000000000 : ℝ)] ![(44905497175769/100000000000000 : ℝ), (2672824257087/20000000000000 : ℝ), (5216297689847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389006379/10000000000 : ℝ)|^4495 ≤ (44905497175769/100000000000000 : ℝ)^3471
        have hw : |(5389006379/10000000000 : ℝ)|=(5389006379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264221881/1250000000 : ℝ)|^4495 ≤ (2672824257087/20000000000000 : ℝ)^3471
        have hw : |(-264221881/1250000000 : ℝ)|=(264221881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5092330729/10000000000 : ℝ)|^4495 ≤ (5216297689847/12500000000000 : ℝ)^3471
        have hw : |(5092330729/10000000000 : ℝ)|=(5092330729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_2 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077801389/2000000000 : ℝ)*x 0 + (5092330377/10000000000 : ℝ)*x 1 + (-1056887379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077801389/2000000000 : ℝ)^4495 ≤ (22452751641767/50000000000000 : ℝ)^3471 := by
    have hnat : (1077801389 : ℕ)^4495*50000000000000^3471 ≤ 22452751641767^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077801389 2000000000 22452751641767 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5092330377/10000000000 : ℝ)^4495 ≤ (8346075556647/20000000000000 : ℝ)^3471 := by
    have hnat : (5092330377 : ℕ)^4495*20000000000000^3471 ≤ 8346075556647^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092330377 10000000000 8346075556647 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056887379/5000000000 : ℝ)^4495 ≤ (1336411891103/10000000000000 : ℝ)^3471 := by
    have hnat : (1056887379 : ℕ)^4495*10000000000000^3471 ≤ 1336411891103^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056887379 5000000000 1336411891103 10000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077801389/2000000000 : ℝ), (5092330377/10000000000 : ℝ), (-1056887379/5000000000 : ℝ)] ![(22452751641767/50000000000000 : ℝ), (8346075556647/20000000000000 : ℝ), (1336411891103/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077801389/2000000000 : ℝ)|^4495 ≤ (22452751641767/50000000000000 : ℝ)^3471
        have hw : |(1077801389/2000000000 : ℝ)|=(1077801389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5092330377/10000000000 : ℝ)|^4495 ≤ (8346075556647/20000000000000 : ℝ)^3471
        have hw : |(5092330377/10000000000 : ℝ)|=(5092330377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056887379/5000000000 : ℝ)|^4495 ≤ (1336411891103/10000000000000 : ℝ)^3471
        have hw : |(-1056887379/5000000000 : ℝ)|=(1056887379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_3 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127176497/5000000000 : ℝ)*x 0 + (186864843/500000000 : ℝ)*x 1 + (193257717/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127176497/5000000000 : ℝ)^4495 ≤ (1653116776749/5000000000000 : ℝ)^3471 := by
    have hnat : (2127176497 : ℕ)^4495*5000000000000^3471 ≤ 1653116776749^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127176497 5000000000 1653116776749 5000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186864843/500000000 : ℝ)^4495 ≤ (27954730755547/100000000000000 : ℝ)^3471 := by
    have hnat : (186864843 : ℕ)^4495*100000000000000^3471 ≤ 27954730755547^3471*500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186864843 500000000 27954730755547 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193257717/400000000 : ℝ)^4495 ≤ (9745733424807/25000000000000 : ℝ)^3471 := by
    have hnat : (193257717 : ℕ)^4495*25000000000000^3471 ≤ 9745733424807^3471*400000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193257717 400000000 9745733424807 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127176497/5000000000 : ℝ), (186864843/500000000 : ℝ), (193257717/400000000 : ℝ)] ![(1653116776749/5000000000000 : ℝ), (27954730755547/100000000000000 : ℝ), (9745733424807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127176497/5000000000 : ℝ)|^4495 ≤ (1653116776749/5000000000000 : ℝ)^3471
        have hw : |(2127176497/5000000000 : ℝ)|=(2127176497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186864843/500000000 : ℝ)|^4495 ≤ (27954730755547/100000000000000 : ℝ)^3471
        have hw : |(186864843/500000000 : ℝ)|=(186864843/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(193257717/400000000 : ℝ)|^4495 ≤ (9745733424807/25000000000000 : ℝ)^3471
        have hw : |(193257717/400000000 : ℝ)|=(193257717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_4 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-928628219/5000000000 : ℝ)*x 0 + (2548938579/5000000000 : ℝ)*x 1 + (5573666053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928628219/5000000000 : ℝ)^4495 ≤ (2825644349539/25000000000000 : ℝ)^3471 := by
    have hnat : (928628219 : ℕ)^4495*25000000000000^3471 ≤ 2825644349539^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928628219 5000000000 2825644349539 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548938579/5000000000 : ℝ)^4495 ≤ (8357850303999/20000000000000 : ℝ)^3471 := by
    have hnat : (2548938579 : ℕ)^4495*20000000000000^3471 ≤ 8357850303999^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548938579 5000000000 8357850303999 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5573666053/10000000000 : ℝ)^4495 ≤ (2931760692287/6250000000000 : ℝ)^3471 := by
    have hnat : (5573666053 : ℕ)^4495*6250000000000^3471 ≤ 2931760692287^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573666053 10000000000 2931760692287 6250000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928628219/5000000000 : ℝ), (2548938579/5000000000 : ℝ), (5573666053/10000000000 : ℝ)] ![(2825644349539/25000000000000 : ℝ), (8357850303999/20000000000000 : ℝ), (2931760692287/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928628219/5000000000 : ℝ)|^4495 ≤ (2825644349539/25000000000000 : ℝ)^3471
        have hw : |(-928628219/5000000000 : ℝ)|=(928628219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548938579/5000000000 : ℝ)|^4495 ≤ (8357850303999/20000000000000 : ℝ)^3471
        have hw : |(2548938579/5000000000 : ℝ)|=(2548938579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5573666053/10000000000 : ℝ)|^4495 ≤ (2931760692287/6250000000000 : ℝ)^3471
        have hw : |(5573666053/10000000000 : ℝ)|=(5573666053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_5 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260945067/10000000000 : ℝ)*x 0 + (-40810983/250000000 : ℝ)*x 1 + (5573666177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260945067/10000000000 : ℝ)^4495 ≤ (5441055695713/12500000000000 : ℝ)^3471 := by
    have hnat : (5260945067 : ℕ)^4495*12500000000000^3471 ≤ 5441055695713^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260945067 10000000000 5441055695713 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40810983/250000000 : ℝ)^4495 ≤ (4781690990379/50000000000000 : ℝ)^3471 := by
    have hnat : (40810983 : ℕ)^4495*50000000000000^3471 ≤ 4781690990379^3471*250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40810983 250000000 4781690990379 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5573666177/10000000000 : ℝ)^4495 ≤ (9381634485611/20000000000000 : ℝ)^3471 := by
    have hnat : (5573666177 : ℕ)^4495*20000000000000^3471 ≤ 9381634485611^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573666177 10000000000 9381634485611 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260945067/10000000000 : ℝ), (-40810983/250000000 : ℝ), (5573666177/10000000000 : ℝ)] ![(5441055695713/12500000000000 : ℝ), (4781690990379/50000000000000 : ℝ), (9381634485611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260945067/10000000000 : ℝ)|^4495 ≤ (5441055695713/12500000000000 : ℝ)^3471
        have hw : |(5260945067/10000000000 : ℝ)|=(5260945067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40810983/250000000 : ℝ)|^4495 ≤ (4781690990379/50000000000000 : ℝ)^3471
        have hw : |(-40810983/250000000 : ℝ)|=(40810983/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5573666177/10000000000 : ℝ)|^4495 ≤ (9381634485611/20000000000000 : ℝ)^3471
        have hw : |(5573666177/10000000000 : ℝ)|=(5573666177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_6 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630472481/5000000000 : ℝ)*x 0 + (1393416551/2500000000 : ℝ)*x 1 + (-1632439431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630472481/5000000000 : ℝ)^4495 ≤ (43528444440649/100000000000000 : ℝ)^3471 := by
    have hnat : (2630472481 : ℕ)^4495*100000000000000^3471 ≤ 43528444440649^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630472481 5000000000 43528444440649 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393416551/2500000000 : ℝ)^4495 ≤ (23454086361163/50000000000000 : ℝ)^3471 := by
    have hnat : (1393416551 : ℕ)^4495*50000000000000^3471 ≤ 23454086361163^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393416551 2500000000 23454086361163 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1632439431/10000000000 : ℝ)^4495 ≤ (76507062583/800000000000 : ℝ)^3471 := by
    have hnat : (1632439431 : ℕ)^4495*800000000000^3471 ≤ 76507062583^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1632439431 10000000000 76507062583 800000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630472481/5000000000 : ℝ), (1393416551/2500000000 : ℝ), (-1632439431/10000000000 : ℝ)] ![(43528444440649/100000000000000 : ℝ), (23454086361163/50000000000000 : ℝ), (76507062583/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630472481/5000000000 : ℝ)|^4495 ≤ (43528444440649/100000000000000 : ℝ)^3471
        have hw : |(2630472481/5000000000 : ℝ)|=(2630472481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1393416551/2500000000 : ℝ)|^4495 ≤ (23454086361163/50000000000000 : ℝ)^3471
        have hw : |(1393416551/2500000000 : ℝ)|=(1393416551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1632439431/10000000000 : ℝ)|^4495 ≤ (76507062583/800000000000 : ℝ)^3471
        have hw : |(-1632439431/10000000000 : ℝ)|=(1632439431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s1_7 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (425508889/1000000000 : ℝ)*x 0 + (240949041/500000000 : ℝ)*x 1 + (468745459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425508889/1000000000 : ℝ)^4495 ≤ (33069741857373/100000000000000 : ℝ)^3471 := by
    have hnat : (425508889 : ℕ)^4495*100000000000000^3471 ≤ 33069741857373^3471*1000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425508889 1000000000 33069741857373 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240949041/500000000 : ℝ)^4495 ≤ (7770553466491/20000000000000 : ℝ)^3471 := by
    have hnat : (240949041 : ℕ)^4495*20000000000000^3471 ≤ 7770553466491^3471*500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240949041 500000000 7770553466491 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468745459/1250000000 : ℝ)^4495 ≤ (14038745398003/50000000000000 : ℝ)^3471 := by
    have hnat : (468745459 : ℕ)^4495*50000000000000^3471 ≤ 14038745398003^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468745459 1250000000 14038745398003 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425508889/1000000000 : ℝ), (240949041/500000000 : ℝ), (468745459/1250000000 : ℝ)] ![(33069741857373/100000000000000 : ℝ), (7770553466491/20000000000000 : ℝ), (14038745398003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425508889/1000000000 : ℝ)|^4495 ≤ (33069741857373/100000000000000 : ℝ)^3471
        have hw : |(425508889/1000000000 : ℝ)|=(425508889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240949041/500000000 : ℝ)|^4495 ≤ (7770553466491/20000000000000 : ℝ)^3471
        have hw : |(240949041/500000000 : ℝ)|=(240949041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(468745459/1250000000 : ℝ)|^4495 ≤ (14038745398003/50000000000000 : ℝ)^3471
        have hw : |(468745459/1250000000 : ℝ)|=(468745459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1499_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25653/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4089/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4619/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25653/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25653/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25653/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25653/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25653/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25653/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1329/50000 : ℝ) ^ (4493/1024 : ℝ) ≤ (2446004498491/20000000000000000000 : ℝ) := by
    have hpowers : (1329/50000 : ℝ)^4493 ≤ (2446004498491/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1329 : ℕ)^4493*20000000000000000000^1024 ≤ 2446004498491^1024*50000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1329 50000 2446004498491 20000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1329/50000 : ℝ)) (X := (2446004498491/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25653/100000 : ℝ) ^ (4493/1024 : ℝ) ≤ (255551408735079553/100000000000000000000 : ℝ) := by
    have hpowers : (25653/100000 : ℝ)^4493 ≤ (255551408735079553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25653 : ℕ)^4493*100000000000000000000^1024 ≤ 255551408735079553^1024*100000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25653 100000 255551408735079553 100000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25653/100000 : ℝ)) (X := (255551408735079553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000002446004498491/10000000000000000000 : ℝ) ≤ (2000000111493807/2000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (10000002446004498491/10000000000000000000 : ℝ)^1024 ≤ (2000000111493807/2000000000000000 : ℝ)^4493 := by
      have hnat : (10000002446004498491 : ℕ)^1024*2000000000000000^4493 ≤ 2000000111493807^4493*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000002446004498491 10000000000000000000 2000000111493807 2000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000111493807/2000000000000000 : ℝ)) (X := (10000002446004498491/10000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12531945454844696501/12500000000000000000 : ℝ) ≤ (10005818815206129/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (12531945454844696501/12500000000000000000 : ℝ)^1024 ≤ (10005818815206129/10000000000000000 : ℝ)^4493 := by
      have hnat : (12531945454844696501 : ℕ)^1024*10000000000000000^4493 ≤ 10005818815206129^4493*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12531945454844696501 12500000000000000000 10005818815206129 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005818815206129/10000000000000000 : ℝ)) (X := (12531945454844696501/12500000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50255551408735079553/50000000000000000000 : ℝ) ≤ (10011637072943223/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (50255551408735079553/50000000000000000000 : ℝ)^1024 ≤ (10011637072943223/10000000000000000 : ℝ)^4493 := by
      have hnat : (50255551408735079553 : ℕ)^1024*10000000000000000^4493 ≤ 10011637072943223^4493*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50255551408735079553 50000000000000000000 10011637072943223 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011637072943223/10000000000000000 : ℝ)) (X := (50255551408735079553/50000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2446004498491/20000000000000000000 : ℝ) ≤ ((25546564773430007569/25550000000000000000 : ℝ)+2*(969709622849/383250000000000 : ℝ)*(1329/50000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (25546564773430007569/25550000000000000000 : ℝ)+2*(969709622849/383250000000000 : ℝ)*(1329/50000 : ℝ)=(2000000111493807/2000000000000000 : ℝ) by norm_num, show 1+2*(2446004498491/20000000000000000000 : ℝ)=(10000002446004498491/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(255551408735079553/100000000000000000000 : ℝ)+(2446004498491/20000000000000000000 : ℝ) ≤ ((25546564773430007569/25550000000000000000 : ℝ)+(969709622849/383250000000000 : ℝ)*((25653/100000 : ℝ)+(1329/50000 : ℝ)))^(4493/1024 : ℝ) := by
    rw [show (25546564773430007569/25550000000000000000 : ℝ)+(969709622849/383250000000000 : ℝ)*((25653/100000 : ℝ)+(1329/50000 : ℝ))=(10005818815206129/10000000000000000 : ℝ) by norm_num, show 1+(255551408735079553/100000000000000000000 : ℝ)+(2446004498491/20000000000000000000 : ℝ)=(12531945454844696501/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(255551408735079553/100000000000000000000 : ℝ) ≤ ((25546564773430007569/25550000000000000000 : ℝ)+2*(969709622849/383250000000000 : ℝ)*(25653/100000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (25546564773430007569/25550000000000000000 : ℝ)+2*(969709622849/383250000000000 : ℝ)*(25653/100000 : ℝ)=(10011637072943223/10000000000000000 : ℝ) by norm_num, show 1+2*(255551408735079553/100000000000000000000 : ℝ)=(50255551408735079553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25546564773430007569/25550000000000000000 : ℝ)*(X 1 0+X 2 0)+(969709622849/383250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (1329/50000 : ℝ)) (hi := (25653/100000 : ℝ)) (c := (25546564773430007569/25550000000000000000 : ℝ)) (alpha := (969709622849/383250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25546564773430007569/25550000000000000000 : ℝ)*(X 0 1+X 2 1)+(969709622849/383250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (1329/50000 : ℝ)) (hi := (25653/100000 : ℝ)) (c := (25546564773430007569/25550000000000000000 : ℝ)) (alpha := (969709622849/383250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25546564773430007569/25550000000000000000 : ℝ)*(X 0 2+X 1 2)+(969709622849/383250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (1329/50000 : ℝ)) (hi := (25653/100000 : ℝ)) (c := (25546564773430007569/25550000000000000000 : ℝ)) (alpha := (969709622849/383250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-116058071/625000000 : ℝ)*X 0 0+(5579303961/10000000000 : ℝ)*X 0 1+(5092330091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5389006379/10000000000 : ℝ)*X 1 0+(-264221881/1250000000 : ℝ)*X 1 1+(5092330729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1077801389/2000000000 : ℝ)*X 2 0+(5092330377/10000000000 : ℝ)*X 2 1+(-1056887379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2127176497/5000000000 : ℝ)*X 0 0+(186864843/500000000 : ℝ)*X 0 1+(193257717/400000000 : ℝ)*X 0 2+(2127176497/5000000000 : ℝ)*X 1 0+(186864843/500000000 : ℝ)*X 1 1+(193257717/400000000 : ℝ)*X 1 2+(2127176497/5000000000 : ℝ)*X 2 0+(186864843/500000000 : ℝ)*X 2 1+(193257717/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-928628219/5000000000 : ℝ)*X 0 0+(2548938579/5000000000 : ℝ)*X 0 1+(5573666053/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260945067/10000000000 : ℝ)*X 1 0+(-40810983/250000000 : ℝ)*X 1 1+(5573666177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630472481/5000000000 : ℝ)*X 2 0+(1393416551/2500000000 : ℝ)*X 2 1+(-1632439431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((425508889/1000000000 : ℝ)*X 0 0+(240949041/500000000 : ℝ)*X 0 1+(468745459/1250000000 : ℝ)*X 0 2+(425508889/1000000000 : ℝ)*X 1 0+(240949041/500000000 : ℝ)*X 1 1+(468745459/1250000000 : ℝ)*X 1 2+(425508889/1000000000 : ℝ)*X 2 0+(240949041/500000000 : ℝ)*X 2 1+(468745459/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5475115350262198015549579661/638750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1990353/100000000000000 : ℝ)*(base1) + (908295179/50000000000000 : ℝ)*(base19) + (508067441/25000000000000 : ℝ)*(base23) + (67761353/50000000000000 : ℝ)*(upper3) + (322088689/100000000000000 : ℝ)*(upper5) + (741875217962741/50000000000000 : ℝ)*(major0) + (741875217962741/50000000000000 : ℝ)*(major1) + (741875217962741/50000000000000 : ℝ)*(major2) + (513378278330713/25000000000000 : ℝ)*(sp0) + (2053529701875393/100000000000000 : ℝ)*(sp1) + (2053529486195987/100000000000000 : ℝ)*(sp2) + (913962204194603/100000000000000 : ℝ)*(sp3) + (18407133253/100000000000000 : ℝ)*(sp4) + (6861479943/100000000000000 : ℝ)*(sp7) + (456984533832449/50000000000000 : ℝ)*(f.failure) + (2053531518465751/100000000000000 : ℝ)*(f.sum) + (24234937839743/19162500000000000000000000000 : ℝ)*base65 + (50661653760353240113/3832500000000000000000000000000000 : ℝ)*base68 + (43826285865998240113/3832500000000000000000000000000000 : ℝ)*base70 + (36756826422675740113/3832500000000000000000000000000000 : ℝ)*base72 + (46200438113441/9581250000000000000000000000 : ℝ)*base74 + (25322023704368240113/3832500000000000000000000000000000 : ℝ)*base76 + (15425122868535740113/3832500000000000000000000000000000 : ℝ)*base78 + (20037086575725740113/3832500000000000000000000000000000 : ℝ)*base80 + (162141036479189/38325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4150707/1250000000000000000000 : ℝ)*base90 + (4150707/1250000000000000000000 : ℝ)*base92 + (4150707/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3237108528745581933252386257/638750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (986340463/100000000000000 : ℝ)*(base19) + (1007805841/100000000000000 : ℝ)*(base23) + (150192183/100000000000000 : ℝ)*(upper3) + (1280567/5000000000000 : ℝ)*(lower4) + (12933261/20000000000000 : ℝ)*(upper5) + (1518605082027349/100000000000000 : ℝ)*(major0) + (1518605082027349/100000000000000 : ℝ)*(major1) + (1518605082027349/100000000000000 : ℝ)*(major2) + (6491460237/100000000000000 : ℝ)*(sp1) + (3548303361/50000000000000 : ℝ)*(sp2) + (210177096348929/10000000000000 : ℝ)*(sp4) + (210176348568859/10000000000000 : ℝ)*(sp5) + (262720357384591/12500000000000 : ℝ)*(sp6) + (467719515818029/50000000000000 : ℝ)*(sp7) + (467719515818029/50000000000000 : ℝ)*(f.failure) + (210177096348929/10000000000000 : ℝ)*(f.sum) + (10368122175199/19162500000000000000000000000 : ℝ)*base66 + (55981250530565213743/7665000000000000000000000000000000 : ℝ)*base67 + (31900028311175213743/7665000000000000000000000000000000 : ℝ)*base69 + (20303836630220213743/7665000000000000000000000000000000 : ℝ)*base71 + (9682832113901/19162500000000000000000000000 : ℝ)*base73 + (28125239376230213743/7665000000000000000000000000000000 : ℝ)*base75 + (19857800522675213743/7665000000000000000000000000000000 : ℝ)*base77 + (52025167500624786257/7665000000000000000000000000000000 : ℝ)*base80 + (22713626649649/19162500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (8498647/1250000000000000000000 : ℝ)*base90 + (8498647/1250000000000000000000 : ℝ)*base92 + (8498647/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1499_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25653/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4089/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4619/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1499_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1499_s2_0 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-470744903/2500000000 : ℝ)*x 0 + (2731099423/5000000000 : ℝ)*x 1 + (5192584531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470744903/2500000000 : ℝ)^4495 ≤ (460228570567/4000000000000 : ℝ)^3471 := by
    have hnat : (470744903 : ℕ)^4495*4000000000000^3471 ≤ 460228570567^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470744903 2500000000 460228570567 4000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731099423/5000000000 : ℝ)^4495 ≤ (22848451033251/50000000000000 : ℝ)^3471 := by
    have hnat : (2731099423 : ℕ)^4495*50000000000000^3471 ≤ 22848451033251^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731099423 5000000000 22848451033251 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192584531/10000000000 : ℝ)^4495 ≤ (2139869182883/5000000000000 : ℝ)^3471 := by
    have hnat : (5192584531 : ℕ)^4495*5000000000000^3471 ≤ 2139869182883^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192584531 10000000000 2139869182883 5000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-470744903/2500000000 : ℝ), (2731099423/5000000000 : ℝ), (5192584531/10000000000 : ℝ)] ![(460228570567/4000000000000 : ℝ), (22848451033251/50000000000000 : ℝ), (2139869182883/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-470744903/2500000000 : ℝ)|^4495 ≤ (460228570567/4000000000000 : ℝ)^3471
        have hw : |(-470744903/2500000000 : ℝ)|=(470744903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731099423/5000000000 : ℝ)|^4495 ≤ (22848451033251/50000000000000 : ℝ)^3471
        have hw : |(2731099423/5000000000 : ℝ)|=(2731099423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192584531/10000000000 : ℝ)|^4495 ≤ (2139869182883/5000000000000 : ℝ)^3471
        have hw : |(5192584531/10000000000 : ℝ)|=(5192584531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_1 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5359375881/10000000000 : ℝ)*x 0 + (-505470539/2500000000 : ℝ)*x 1 + (324536483/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5359375881/10000000000 : ℝ)^4495 ≤ (4458601104319/10000000000000 : ℝ)^3471 := by
    have hnat : (5359375881 : ℕ)^4495*10000000000000^3471 ≤ 4458601104319^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359375881 10000000000 4458601104319 10000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505470539/2500000000 : ℝ)^4495 ≤ (6308306929829/50000000000000 : ℝ)^3471 := by
    have hnat : (505470539 : ℕ)^4495*50000000000000^3471 ≤ 6308306929829^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505470539 2500000000 6308306929829 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324536483/625000000 : ℝ)^4495 ≤ (21398687543401/50000000000000 : ℝ)^3471 := by
    have hnat : (324536483 : ℕ)^4495*50000000000000^3471 ≤ 21398687543401^3471*625000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324536483 625000000 21398687543401 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5359375881/10000000000 : ℝ), (-505470539/2500000000 : ℝ), (324536483/625000000 : ℝ)] ![(4458601104319/10000000000000 : ℝ), (6308306929829/50000000000000 : ℝ), (21398687543401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5359375881/10000000000 : ℝ)|^4495 ≤ (4458601104319/10000000000000 : ℝ)^3471
        have hw : |(5359375881/10000000000 : ℝ)|=(5359375881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-505470539/2500000000 : ℝ)|^4495 ≤ (6308306929829/50000000000000 : ℝ)^3471
        have hw : |(-505470539/2500000000 : ℝ)|=(505470539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324536483/625000000 : ℝ)|^4495 ≤ (21398687543401/50000000000000 : ℝ)^3471
        have hw : |(324536483/625000000 : ℝ)|=(324536483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_2 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535937559/1000000000 : ℝ)*x 0 + (5192583879/10000000000 : ℝ)*x 1 + (-404376469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535937559/1000000000 : ℝ)^4495 ≤ (44586007908083/100000000000000 : ℝ)^3471 := by
    have hnat : (535937559 : ℕ)^4495*100000000000000^3471 ≤ 44586007908083^3471*1000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535937559 1000000000 44586007908083 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192583879/10000000000 : ℝ)^4495 ≤ (10699344174627/25000000000000 : ℝ)^3471 := by
    have hnat : (5192583879 : ℕ)^4495*25000000000000^3471 ≤ 10699344174627^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192583879 10000000000 10699344174627 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404376469/2000000000 : ℝ)^4495 ≤ (3154153846739/25000000000000 : ℝ)^3471 := by
    have hnat : (404376469 : ℕ)^4495*25000000000000^3471 ≤ 3154153846739^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404376469 2000000000 3154153846739 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535937559/1000000000 : ℝ), (5192583879/10000000000 : ℝ), (-404376469/2000000000 : ℝ)] ![(44586007908083/100000000000000 : ℝ), (10699344174627/25000000000000 : ℝ), (3154153846739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535937559/1000000000 : ℝ)|^4495 ≤ (44586007908083/100000000000000 : ℝ)^3471
        have hw : |(535937559/1000000000 : ℝ)|=(535937559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192583879/10000000000 : ℝ)|^4495 ≤ (10699344174627/25000000000000 : ℝ)^3471
        have hw : |(5192583879/10000000000 : ℝ)|=(5192583879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-404376469/2000000000 : ℝ)|^4495 ≤ (3154153846739/25000000000000 : ℝ)^3471
        have hw : |(-404376469/2000000000 : ℝ)|=(404376469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_3 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273010293/10000000000 : ℝ)*x 0 + (3979325757/10000000000 : ℝ)*x 1 + (917020579/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273010293/10000000000 : ℝ)^4495 ≤ (33250225862163/100000000000000 : ℝ)^3471 := by
    have hnat : (4273010293 : ℕ)^4495*100000000000000^3471 ≤ 33250225862163^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273010293 10000000000 33250225862163 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979325757/10000000000 : ℝ)^4495 ≤ (30321239592953/100000000000000 : ℝ)^3471 := by
    have hnat : (3979325757 : ℕ)^4495*100000000000000^3471 ≤ 30321239592953^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979325757 10000000000 30321239592953 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917020579/2000000000 : ℝ)^4495 ≤ (1138391703979/3125000000000 : ℝ)^3471 := by
    have hnat : (917020579 : ℕ)^4495*3125000000000^3471 ≤ 1138391703979^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917020579 2000000000 1138391703979 3125000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273010293/10000000000 : ℝ), (3979325757/10000000000 : ℝ), (917020579/2000000000 : ℝ)] ![(33250225862163/100000000000000 : ℝ), (30321239592953/100000000000000 : ℝ), (1138391703979/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273010293/10000000000 : ℝ)|^4495 ≤ (33250225862163/100000000000000 : ℝ)^3471
        have hw : |(4273010293/10000000000 : ℝ)|=(4273010293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979325757/10000000000 : ℝ)|^4495 ≤ (30321239592953/100000000000000 : ℝ)^3471
        have hw : |(3979325757/10000000000 : ℝ)|=(3979325757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(917020579/2000000000 : ℝ)|^4495 ≤ (1138391703979/3125000000000 : ℝ)^3471
        have hw : |(917020579/2000000000 : ℝ)|=(917020579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_4 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-376606777/2000000000 : ℝ)*x 0 + (1298573753/2500000000 : ℝ)*x 1 + (1365118479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (376606777/2000000000 : ℝ)^4495 ≤ (179783495783/1562500000000 : ℝ)^3471 := by
    have hnat : (376606777 : ℕ)^4495*1562500000000^3471 ≤ 179783495783^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376606777 2000000000 179783495783 1562500000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298573753/2500000000 : ℝ)^4495 ≤ (2140782072119/5000000000000 : ℝ)^3471 := by
    have hnat : (1298573753 : ℕ)^4495*5000000000000^3471 ≤ 2140782072119^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298573753 2500000000 2140782072119 5000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365118479/2500000000 : ℝ)^4495 ≤ (22839107404321/50000000000000 : ℝ)^3471 := by
    have hnat : (1365118479 : ℕ)^4495*50000000000000^3471 ≤ 22839107404321^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365118479 2500000000 22839107404321 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-376606777/2000000000 : ℝ), (1298573753/2500000000 : ℝ), (1365118479/2500000000 : ℝ)] ![(179783495783/1562500000000 : ℝ), (2140782072119/5000000000000 : ℝ), (22839107404321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-376606777/2000000000 : ℝ)|^4495 ≤ (179783495783/1562500000000 : ℝ)^3471
        have hw : |(-376606777/2000000000 : ℝ)|=(376606777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298573753/2500000000 : ℝ)|^4495 ≤ (2140782072119/5000000000000 : ℝ)^3471
        have hw : |(1298573753/2500000000 : ℝ)|=(1298573753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365118479/2500000000 : ℝ)|^4495 ≤ (22839107404321/50000000000000 : ℝ)^3471
        have hw : |(1365118479/2500000000 : ℝ)|=(1365118479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_5 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057743891/2000000000 : ℝ)*x 0 + (-350798231/2000000000 : ℝ)*x 1 + (5460474093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057743891/2000000000 : ℝ)^4495 ≤ (1369571072549/3125000000000 : ℝ)^3471 := by
    have hnat : (1057743891 : ℕ)^4495*3125000000000^3471 ≤ 1369571072549^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057743891 2000000000 1369571072549 3125000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350798231/2000000000 : ℝ)^4495 ≤ (2099101787817/20000000000000 : ℝ)^3471 := by
    have hnat : (350798231 : ℕ)^4495*20000000000000^3471 ≤ 2099101787817^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350798231 2000000000 2099101787817 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460474093/10000000000 : ℝ)^4495 ≤ (22839108363053/50000000000000 : ℝ)^3471 := by
    have hnat : (5460474093 : ℕ)^4495*50000000000000^3471 ≤ 22839108363053^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460474093 10000000000 22839108363053 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057743891/2000000000 : ℝ), (-350798231/2000000000 : ℝ), (5460474093/10000000000 : ℝ)] ![(1369571072549/3125000000000 : ℝ), (2099101787817/20000000000000 : ℝ), (22839108363053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057743891/2000000000 : ℝ)|^4495 ≤ (1369571072549/3125000000000 : ℝ)^3471
        have hw : |(1057743891/2000000000 : ℝ)|=(1057743891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350798231/2000000000 : ℝ)|^4495 ≤ (2099101787817/20000000000000 : ℝ)^3471
        have hw : |(-350798231/2000000000 : ℝ)|=(350798231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460474093/10000000000 : ℝ)|^4495 ≤ (22839108363053/50000000000000 : ℝ)^3471
        have hw : |(5460474093/10000000000 : ℝ)|=(5460474093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_6 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661089779/1250000000 : ℝ)*x 0 + (136511841/250000000 : ℝ)*x 1 + (-876996741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661089779/1250000000 : ℝ)^4495 ≤ (5478282649623/12500000000000 : ℝ)^3471 := by
    have hnat : (661089779 : ℕ)^4495*12500000000000^3471 ≤ 5478282649623^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661089779 1250000000 5478282649623 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136511841/250000000 : ℝ)^4495 ≤ (45678211818699/100000000000000 : ℝ)^3471 := by
    have hnat : (136511841 : ℕ)^4495*100000000000000^3471 ≤ 45678211818699^3471*250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136511841 250000000 45678211818699 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (876996741/5000000000 : ℝ)^4495 ≤ (10495526971241/100000000000000 : ℝ)^3471 := by
    have hnat : (876996741 : ℕ)^4495*100000000000000^3471 ≤ 10495526971241^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876996741 5000000000 10495526971241 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661089779/1250000000 : ℝ), (136511841/250000000 : ℝ), (-876996741/5000000000 : ℝ)] ![(5478282649623/12500000000000 : ℝ), (45678211818699/100000000000000 : ℝ), (10495526971241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661089779/1250000000 : ℝ)|^4495 ≤ (5478282649623/12500000000000 : ℝ)^3471
        have hw : |(661089779/1250000000 : ℝ)|=(661089779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136511841/250000000 : ℝ)|^4495 ≤ (45678211818699/100000000000000 : ℝ)^3471
        have hw : |(136511841/250000000 : ℝ)|=(136511841/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-876996741/5000000000 : ℝ)|^4495 ≤ (10495526971241/100000000000000 : ℝ)^3471
        have hw : |(-876996741/5000000000 : ℝ)|=(876996741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s2_7 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4273136033/10000000000 : ℝ)*x 0 + (4581263123/10000000000 : ℝ)*x 1 + (995799997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273136033/10000000000 : ℝ)^4495 ≤ (4156436620341/12500000000000 : ℝ)^3471 := by
    have hnat : (4273136033 : ℕ)^4495*12500000000000^3471 ≤ 4156436620341^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273136033 10000000000 4156436620341 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4581263123/10000000000 : ℝ)^4495 ≤ (36389032492107/100000000000000 : ℝ)^3471 := by
    have hnat : (4581263123 : ℕ)^4495*100000000000000^3471 ≤ 36389032492107^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4581263123 10000000000 36389032492107 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995799997/2500000000 : ℝ)^4495 ≤ (30359474532219/100000000000000 : ℝ)^3471 := by
    have hnat : (995799997 : ℕ)^4495*100000000000000^3471 ≤ 30359474532219^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995799997 2500000000 30359474532219 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273136033/10000000000 : ℝ), (4581263123/10000000000 : ℝ), (995799997/2500000000 : ℝ)] ![(4156436620341/12500000000000 : ℝ), (36389032492107/100000000000000 : ℝ), (30359474532219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273136033/10000000000 : ℝ)|^4495 ≤ (4156436620341/12500000000000 : ℝ)^3471
        have hw : |(4273136033/10000000000 : ℝ)|=(4273136033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4581263123/10000000000 : ℝ)|^4495 ≤ (36389032492107/100000000000000 : ℝ)^3471
        have hw : |(4581263123/10000000000 : ℝ)|=(4581263123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995799997/2500000000 : ℝ)|^4495 ≤ (30359474532219/100000000000000 : ℝ)^3471
        have hw : |(995799997/2500000000 : ℝ)|=(995799997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1499_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4619/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4089/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5171/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1003/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4619/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4089/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4619/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4089/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4619/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4089/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4619/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4089/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4619/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4089/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4619/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4089/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4089/50000 : ℝ) ^ (4493/1024 : ℝ) ≤ (1694442379239003/100000000000000000000 : ℝ) := by
    have hpowers : (4089/50000 : ℝ)^4493 ≤ (1694442379239003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4089 : ℕ)^4493*100000000000000000000^1024 ≤ 1694442379239003^1024*50000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4089 50000 1694442379239003 100000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4089/50000 : ℝ)) (X := (1694442379239003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4619/25000 : ℝ) ^ (4493/1024 : ℝ) ≤ (378424436598297/625000000000000000 : ℝ) := by
    have hpowers : (4619/25000 : ℝ)^4493 ≤ (378424436598297/625000000000000000 : ℝ)^1024 := by
      have hnat : (4619 : ℕ)^4493*625000000000000000^1024 ≤ 378424436598297^1024*25000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4619 25000 378424436598297 625000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4619/25000 : ℝ)) (X := (378424436598297/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001694442379239003/50000000000000000000 : ℝ) ≤ (1250009654386251/1250000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (50001694442379239003/50000000000000000000 : ℝ)^1024 ≤ (1250009654386251/1250000000000000 : ℝ)^4493 := by
      have hnat : (50001694442379239003 : ℕ)^1024*1250000000000000^4493 ≤ 1250009654386251^4493*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001694442379239003 50000000000000000000 1250009654386251 1250000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009654386251/1250000000000000 : ℝ)) (X := (50001694442379239003/50000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100062242352234966523/100000000000000000000 : ℝ) ≤ (125017727815371/125000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (100062242352234966523/100000000000000000000 : ℝ)^1024 ≤ (125017727815371/125000000000000 : ℝ)^4493 := by
      have hnat : (100062242352234966523 : ℕ)^1024*125000000000000^4493 ≤ 125017727815371^4493*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062242352234966523 100000000000000000000 125017727815371 125000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125017727815371/125000000000000 : ℝ)) (X := (100062242352234966523/100000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312878424436598297/312500000000000000 : ℝ) ≤ (1250344901921169/1250000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (312878424436598297/312500000000000000 : ℝ)^1024 ≤ (1250344901921169/1250000000000000 : ℝ)^4493 := by
      have hnat : (312878424436598297 : ℕ)^1024*1250000000000000^4493 ≤ 1250344901921169^4493*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312878424436598297 312500000000000000 1250344901921169 1250000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250344901921169/1250000000000000 : ℝ)) (X := (312878424436598297/312500000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1694442379239003/100000000000000000000 : ℝ) ≤ ((6434928883264526697/6436250000000000000 : ℝ)+2*(167623767459/128725000000000 : ℝ)*(4089/50000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (6434928883264526697/6436250000000000000 : ℝ)+2*(167623767459/128725000000000 : ℝ)*(4089/50000 : ℝ)=(1250009654386251/1250000000000000 : ℝ) by norm_num, show 1+2*(1694442379239003/100000000000000000000 : ℝ)=(50001694442379239003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(378424436598297/625000000000000000 : ℝ)+(1694442379239003/100000000000000000000 : ℝ) ≤ ((6434928883264526697/6436250000000000000 : ℝ)+(167623767459/128725000000000 : ℝ)*((4619/25000 : ℝ)+(4089/50000 : ℝ)))^(4493/1024 : ℝ) := by
    rw [show (6434928883264526697/6436250000000000000 : ℝ)+(167623767459/128725000000000 : ℝ)*((4619/25000 : ℝ)+(4089/50000 : ℝ))=(125017727815371/125000000000000 : ℝ) by norm_num, show 1+(378424436598297/625000000000000000 : ℝ)+(1694442379239003/100000000000000000000 : ℝ)=(100062242352234966523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(378424436598297/625000000000000000 : ℝ) ≤ ((6434928883264526697/6436250000000000000 : ℝ)+2*(167623767459/128725000000000 : ℝ)*(4619/25000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (6434928883264526697/6436250000000000000 : ℝ)+2*(167623767459/128725000000000 : ℝ)*(4619/25000 : ℝ)=(1250344901921169/1250000000000000 : ℝ) by norm_num, show 1+2*(378424436598297/625000000000000000 : ℝ)=(312878424436598297/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6434928883264526697/6436250000000000000 : ℝ)*(X 1 0+X 2 0)+(167623767459/128725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (4089/50000 : ℝ)) (hi := (4619/25000 : ℝ)) (c := (6434928883264526697/6436250000000000000 : ℝ)) (alpha := (167623767459/128725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6434928883264526697/6436250000000000000 : ℝ)*(X 0 1+X 2 1)+(167623767459/128725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (4089/50000 : ℝ)) (hi := (4619/25000 : ℝ)) (c := (6434928883264526697/6436250000000000000 : ℝ)) (alpha := (167623767459/128725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6434928883264526697/6436250000000000000 : ℝ)*(X 0 2+X 1 2)+(167623767459/128725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (4089/50000 : ℝ)) (hi := (4619/25000 : ℝ)) (c := (6434928883264526697/6436250000000000000 : ℝ)) (alpha := (167623767459/128725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-470744903/2500000000 : ℝ)*X 0 0+(2731099423/5000000000 : ℝ)*X 0 1+(5192584531/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5359375881/10000000000 : ℝ)*X 1 0+(-505470539/2500000000 : ℝ)*X 1 1+(324536483/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535937559/1000000000 : ℝ)*X 2 0+(5192583879/10000000000 : ℝ)*X 2 1+(-404376469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4273010293/10000000000 : ℝ)*X 0 0+(3979325757/10000000000 : ℝ)*X 0 1+(917020579/2000000000 : ℝ)*X 0 2+(4273010293/10000000000 : ℝ)*X 1 0+(3979325757/10000000000 : ℝ)*X 1 1+(917020579/2000000000 : ℝ)*X 1 2+(4273010293/10000000000 : ℝ)*X 2 0+(3979325757/10000000000 : ℝ)*X 2 1+(917020579/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-376606777/2000000000 : ℝ)*X 0 0+(1298573753/2500000000 : ℝ)*X 0 1+(1365118479/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057743891/2000000000 : ℝ)*X 1 0+(-350798231/2000000000 : ℝ)*X 1 1+(5460474093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661089779/1250000000 : ℝ)*X 2 0+(136511841/250000000 : ℝ)*X 2 1+(-876996741/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4273136033/10000000000 : ℝ)*X 0 0+(4581263123/10000000000 : ℝ)*X 0 1+(995799997/2500000000 : ℝ)*X 0 2+(4273136033/10000000000 : ℝ)*X 1 0+(4581263123/10000000000 : ℝ)*X 1 1+(995799997/2500000000 : ℝ)*X 1 2+(4273136033/10000000000 : ℝ)*X 2 0+(4581263123/10000000000 : ℝ)*X 2 1+(995799997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1157839560320593823387091519/160906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3420062077/100000000000000 : ℝ)*(base19) + (350025777/12500000000000 : ℝ)*(base23) + (6601051/50000000000000 : ℝ)*(upper2) + (97143517/20000000000000 : ℝ)*(upper3) + (237472163/100000000000000 : ℝ)*(upper4) + (1339969907663403/50000000000000 : ℝ)*(major0) + (1339969907663403/50000000000000 : ℝ)*(major1) + (1339969907663403/50000000000000 : ℝ)*(major2) + (3709042631840883/100000000000000 : ℝ)*(sp0) + (370907133734887/10000000000000 : ℝ)*(sp1) + (927267989301183/25000000000000 : ℝ)*(sp2) + (1650785852575321/100000000000000 : ℝ)*(sp3) + (2007848129/6250000000000 : ℝ)*(sp4) + (1878080933/10000000000000 : ℝ)*(sp7) + (33016092667693/2000000000000 : ℝ)*(f.failure) + (3709074757410947/100000000000000 : ℝ)*(f.sum) + (25350835323101/25745000000000000000000000000 : ℝ)*base65 + (1222368619528842609/321812500000000000000000000000000 : ℝ)*base68 + (4647049442178280109/321812500000000000000000000000000 : ℝ)*base70 + (529522088713842609/321812500000000000000000000000000 : ℝ)*base72 + (44566044417099/25745000000000000000000000000 : ℝ)*base74 + (2329856513339967609/321812500000000000000000000000000 : ℝ)*base76 + (2766983805844467609/321812500000000000000000000000000 : ℝ)*base78 + (5797182274694967609/321812500000000000000000000000000 : ℝ)*base80 + (187869637968459/25745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (228599/50000000000000000000 : ℝ)*base90 + (228599/50000000000000000000 : ℝ)*base92 + (228599/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2557035318339000476558289117/321812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1058319509/50000000000000 : ℝ)*(base19) + (817693539/50000000000000 : ℝ)*(base23) + (3848141/25000000000000 : ℝ)*(upper3) + (77022741/20000000000000 : ℝ)*(lower4) + (2714466451941713/100000000000000 : ℝ)*(major0) + (2714466451941713/100000000000000 : ℝ)*(major1) + (2714466451941713/100000000000000 : ℝ)*(major2) + (18887533073/50000000000000 : ℝ)*(sp1) + (2455074837/20000000000000 : ℝ)*(sp2) + (3136360647/50000000000000 : ℝ)*(sp3) + (58700938919173/1562500000000 : ℝ)*(sp4) + (939205049780477/25000000000000 : ℝ)*(sp5) + (375684618006581/10000000000000 : ℝ)*(sp6) + (836033137738689/50000000000000 : ℝ)*(sp7) + (104504534262417/6250000000000 : ℝ)*(f.failure) + (58700938919173/1562500000000 : ℝ)*(f.sum) + (5386136205863/6436250000000000000000000000 : ℝ)*base66 + (297573610254261961/643625000000000000000000000000000 : ℝ)*base67 + (1381048311645511961/643625000000000000000000000000000 : ℝ)*base69 + (1036249493950011961/643625000000000000000000000000000 : ℝ)*base71 + (15893518149937/6436250000000000000000000000 : ℝ)*base73 + (3760306096743011961/643625000000000000000000000000000 : ℝ)*base75 + (1991135502086988039/643625000000000000000000000000000 : ℝ)*base78 + (2051559262308113039/643625000000000000000000000000000 : ℝ)*base80 + (208590075749063/25745000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (934631/156250000000000000000 : ℝ)*base90 + (934631/156250000000000000000 : ℝ)*base92 + (934631/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1499_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4619/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4089/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1499_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1499_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1499_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1499_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1499_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1499_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:39:19.123772+00:00
-- url     : https://prove2.me/submissions/9de90dab-b225-4010-b7bd-38f20a7db709

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
theorem support_rectangle_w1310_s3_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-517455599/2500000000 : ℝ)*x 0 + (1086294007/2000000000 : ℝ)*x 1 + (522784929/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517455599/2500000000 : ℝ)^2135 ≤ (2518626558299/20000000000000 : ℝ)^1623 := by
    have hnat : (517455599 : ℕ)^2135*20000000000000^1623 ≤ 2518626558299^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517455599 2500000000 2518626558299 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086294007/2000000000 : ℝ)^2135 ≤ (8960310254191/20000000000000 : ℝ)^1623 := by
    have hnat : (1086294007 : ℕ)^2135*20000000000000^1623 ≤ 8960310254191^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086294007 2000000000 8960310254191 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522784929/1000000000 : ℝ)^2135 ≤ (21302657963187/50000000000000 : ℝ)^1623 := by
    have hnat : (522784929 : ℕ)^2135*50000000000000^1623 ≤ 21302657963187^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522784929 1000000000 21302657963187 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517455599/2500000000 : ℝ), (1086294007/2000000000 : ℝ), (522784929/1000000000 : ℝ)] ![(2518626558299/20000000000000 : ℝ), (8960310254191/20000000000000 : ℝ), (21302657963187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517455599/2500000000 : ℝ)|^2135 ≤ (2518626558299/20000000000000 : ℝ)^1623
        have hw : |(-517455599/2500000000 : ℝ)|=(517455599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086294007/2000000000 : ℝ)|^2135 ≤ (8960310254191/20000000000000 : ℝ)^1623
        have hw : |(1086294007/2000000000 : ℝ)|=(1086294007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522784929/1000000000 : ℝ)|^2135 ≤ (21302657963187/50000000000000 : ℝ)^1623
        have hw : |(522784929/1000000000 : ℝ)|=(522784929/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214154641/400000000 : ℝ)*x 0 + (-2173977649/10000000000 : ℝ)*x 1 + (5227849261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214154641/400000000 : ℝ)^2135 ≤ (21980701330971/50000000000000 : ℝ)^1623 := by
    have hnat : (214154641 : ℕ)^2135*50000000000000^1623 ≤ 21980701330971^1623*400000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214154641 400000000 21980701330971 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173977649/10000000000 : ℝ)^2135 ≤ (13433281706021/100000000000000 : ℝ)^1623 := by
    have hnat : (2173977649 : ℕ)^2135*100000000000000^1623 ≤ 13433281706021^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173977649 10000000000 13433281706021 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227849261/10000000000 : ℝ)^2135 ≤ (10651328903869/25000000000000 : ℝ)^1623 := by
    have hnat : (5227849261 : ℕ)^2135*25000000000000^1623 ≤ 10651328903869^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227849261 10000000000 10651328903869 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214154641/400000000 : ℝ), (-2173977649/10000000000 : ℝ), (5227849261/10000000000 : ℝ)] ![(21980701330971/50000000000000 : ℝ), (13433281706021/100000000000000 : ℝ), (10651328903869/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214154641/400000000 : ℝ)|^2135 ≤ (21980701330971/50000000000000 : ℝ)^1623
        have hw : |(214154641/400000000 : ℝ)|=(214154641/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173977649/10000000000 : ℝ)|^2135 ≤ (13433281706021/100000000000000 : ℝ)^1623
        have hw : |(-2173977649/10000000000 : ℝ)|=(2173977649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227849261/10000000000 : ℝ)|^2135 ≤ (10651328903869/25000000000000 : ℝ)^1623
        have hw : |(5227849261/10000000000 : ℝ)|=(5227849261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676932967/5000000000 : ℝ)*x 0 + (5227849453/10000000000 : ℝ)*x 1 + (-2173977517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676932967/5000000000 : ℝ)^2135 ≤ (43961401679007/100000000000000 : ℝ)^1623 := by
    have hnat : (2676932967 : ℕ)^2135*100000000000000^1623 ≤ 43961401679007^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676932967 5000000000 43961401679007 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227849453/10000000000 : ℝ)^2135 ≤ (10651329418459/25000000000000 : ℝ)^1623 := by
    have hnat : (5227849453 : ℕ)^2135*25000000000000^1623 ≤ 10651329418459^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227849453 10000000000 10651329418459 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173977517/10000000000 : ℝ)^2135 ≤ (13433280633069/100000000000000 : ℝ)^1623 := by
    have hnat : (2173977517 : ℕ)^2135*100000000000000^1623 ≤ 13433280633069^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173977517 10000000000 13433280633069 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676932967/5000000000 : ℝ), (5227849453/10000000000 : ℝ), (-2173977517/10000000000 : ℝ)] ![(43961401679007/100000000000000 : ℝ), (10651329418459/25000000000000 : ℝ), (13433280633069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676932967/5000000000 : ℝ)|^2135 ≤ (43961401679007/100000000000000 : ℝ)^1623
        have hw : |(2676932967/5000000000 : ℝ)|=(2676932967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227849453/10000000000 : ℝ)|^2135 ≤ (10651329418459/25000000000000 : ℝ)^1623
        have hw : |(5227849453/10000000000 : ℝ)|=(5227849453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2173977517/10000000000 : ℝ)|^2135 ≤ (13433280633069/100000000000000 : ℝ)^1623
        have hw : |(-2173977517/10000000000 : ℝ)|=(2173977517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1083444389/2500000000 : ℝ)*x 0 + (4127945751/10000000000 : ℝ)*x 1 + (4549314603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083444389/2500000000 : ℝ)^2135 ≤ (16644880412187/50000000000000 : ℝ)^1623 := by
    have hnat : (1083444389 : ℕ)^2135*50000000000000^1623 ≤ 16644880412187^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083444389 2500000000 16644880412187 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127945751/10000000000 : ℝ)^2135 ≤ (6245129164043/20000000000000 : ℝ)^1623 := by
    have hnat : (4127945751 : ℕ)^2135*20000000000000^1623 ≤ 6245129164043^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127945751 10000000000 6245129164043 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4549314603/10000000000 : ℝ)^2135 ≤ (35484593341311/100000000000000 : ℝ)^1623 := by
    have hnat : (4549314603 : ℕ)^2135*100000000000000^1623 ≤ 35484593341311^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4549314603 10000000000 35484593341311 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083444389/2500000000 : ℝ), (4127945751/10000000000 : ℝ), (4549314603/10000000000 : ℝ)] ![(16644880412187/50000000000000 : ℝ), (6245129164043/20000000000000 : ℝ), (35484593341311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083444389/2500000000 : ℝ)|^2135 ≤ (16644880412187/50000000000000 : ℝ)^1623
        have hw : |(1083444389/2500000000 : ℝ)|=(1083444389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127945751/10000000000 : ℝ)|^2135 ≤ (6245129164043/20000000000000 : ℝ)^1623
        have hw : |(4127945751/10000000000 : ℝ)|=(4127945751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4549314603/10000000000 : ℝ)|^2135 ≤ (35484593341311/100000000000000 : ℝ)^1623
        have hw : |(4549314603/10000000000 : ℝ)|=(4549314603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2069843659/10000000000 : ℝ)*x 0 + (163397351/312500000 : ℝ)*x 1 + (271529937/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069843659/10000000000 : ℝ)^2135 ≤ (2518660594047/20000000000000 : ℝ)^1623 := by
    have hnat : (2069843659 : ℕ)^2135*20000000000000^1623 ≤ 2518660594047^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069843659 10000000000 2518660594047 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163397351/312500000 : ℝ)^2135 ≤ (8522919921611/20000000000000 : ℝ)^1623 := by
    have hnat : (163397351 : ℕ)^2135*20000000000000^1623 ≤ 8522919921611^1623*312500000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163397351 312500000 8522919921611 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271529937/500000000 : ℝ)^2135 ≤ (44792097409013/100000000000000 : ℝ)^1623 := by
    have hnat : (271529937 : ℕ)^2135*100000000000000^1623 ≤ 44792097409013^1623*500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271529937 500000000 44792097409013 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2069843659/10000000000 : ℝ), (163397351/312500000 : ℝ), (271529937/500000000 : ℝ)] ![(2518660594047/20000000000000 : ℝ), (8522919921611/20000000000000 : ℝ), (44792097409013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2069843659/10000000000 : ℝ)|^2135 ≤ (2518660594047/20000000000000 : ℝ)^1623
        have hw : |(-2069843659/10000000000 : ℝ)|=(2069843659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163397351/312500000 : ℝ)|^2135 ≤ (8522919921611/20000000000000 : ℝ)^1623
        have hw : |(163397351/312500000 : ℝ)|=(163397351/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271529937/500000000 : ℝ)|^2135 ≤ (44792097409013/100000000000000 : ℝ)^1623
        have hw : |(271529937/500000000 : ℝ)|=(271529937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132540353/250000000 : ℝ)*x 0 + (-492807019/2500000000 : ℝ)*x 1 + (339412419/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132540353/250000000 : ℝ)^2135 ≤ (21698937682843/50000000000000 : ℝ)^1623 := by
    have hnat : (132540353 : ℕ)^2135*50000000000000^1623 ≤ 21698937682843^1623*250000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132540353 250000000 21698937682843 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492807019/2500000000 : ℝ)^2135 ≤ (1476253448901/12500000000000 : ℝ)^1623 := by
    have hnat : (492807019 : ℕ)^2135*12500000000000^1623 ≤ 1476253448901^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492807019 2500000000 1476253448901 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339412419/625000000 : ℝ)^2135 ≤ (4479209701841/10000000000000 : ℝ)^1623 := by
    have hnat : (339412419 : ℕ)^2135*10000000000000^1623 ≤ 4479209701841^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339412419 625000000 4479209701841 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132540353/250000000 : ℝ), (-492807019/2500000000 : ℝ), (339412419/625000000 : ℝ)] ![(21698937682843/50000000000000 : ℝ), (1476253448901/12500000000000 : ℝ), (4479209701841/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132540353/250000000 : ℝ)|^2135 ≤ (21698937682843/50000000000000 : ℝ)^1623
        have hw : |(132540353/250000000 : ℝ)|=(132540353/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492807019/2500000000 : ℝ)|^2135 ≤ (1476253448901/12500000000000 : ℝ)^1623
        have hw : |(-492807019/2500000000 : ℝ)|=(492807019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339412419/625000000 : ℝ)|^2135 ≤ (4479209701841/10000000000000 : ℝ)^1623
        have hw : |(339412419/625000000 : ℝ)|=(339412419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (21206457/40000000 : ℝ)*x 0 + (5430598581/10000000000 : ℝ)*x 1 + (-197122807/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21206457/40000000 : ℝ)^2135 ≤ (43397876765541/100000000000000 : ℝ)^1623 := by
    have hnat : (21206457 : ℕ)^2135*100000000000000^1623 ≤ 43397876765541^1623*40000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21206457 40000000 43397876765541 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430598581/10000000000 : ℝ)^2135 ≤ (895841913677/2000000000000 : ℝ)^1623 := by
    have hnat : (5430598581 : ℕ)^2135*2000000000000^1623 ≤ 895841913677^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430598581 10000000000 895841913677 2000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197122807/1000000000 : ℝ)^2135 ≤ (11810027543921/100000000000000 : ℝ)^1623 := by
    have hnat : (197122807 : ℕ)^2135*100000000000000^1623 ≤ 11810027543921^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197122807 1000000000 11810027543921 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21206457/40000000 : ℝ), (5430598581/10000000000 : ℝ), (-197122807/1000000000 : ℝ)] ![(43397876765541/100000000000000 : ℝ), (895841913677/2000000000000 : ℝ), (11810027543921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21206457/40000000 : ℝ)|^2135 ≤ (43397876765541/100000000000000 : ℝ)^1623
        have hw : |(21206457/40000000 : ℝ)|=(21206457/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430598581/10000000000 : ℝ)|^2135 ≤ (895841913677/2000000000000 : ℝ)^1623
        have hw : |(5430598581/10000000000 : ℝ)|=(5430598581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197122807/1000000000 : ℝ)|^2135 ≤ (11810027543921/100000000000000 : ℝ)^1623
        have hw : |(-197122807/1000000000 : ℝ)|=(197122807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s3_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2166910859/5000000000 : ℝ)*x 0 + (1136880641/2500000000 : ℝ)*x 1 + (825949701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166910859/5000000000 : ℝ)^2135 ≤ (16645103534423/50000000000000 : ℝ)^1623 := by
    have hnat : (2166910859 : ℕ)^2135*50000000000000^1623 ≤ 16645103534423^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166910859 5000000000 16645103534423 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136880641/2500000000 : ℝ)^2135 ≤ (35466207068887/100000000000000 : ℝ)^1623 := by
    have hnat : (1136880641 : ℕ)^2135*100000000000000^1623 ≤ 35466207068887^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136880641 2500000000 35466207068887 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825949701/2000000000 : ℝ)^2135 ≤ (15621792925581/50000000000000 : ℝ)^1623 := by
    have hnat : (825949701 : ℕ)^2135*50000000000000^1623 ≤ 15621792925581^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825949701 2000000000 15621792925581 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166910859/5000000000 : ℝ), (1136880641/2500000000 : ℝ), (825949701/2000000000 : ℝ)] ![(16645103534423/50000000000000 : ℝ), (35466207068887/100000000000000 : ℝ), (15621792925581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166910859/5000000000 : ℝ)|^2135 ≤ (16645103534423/50000000000000 : ℝ)^1623
        have hw : |(2166910859/5000000000 : ℝ)|=(2166910859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136880641/2500000000 : ℝ)|^2135 ≤ (35466207068887/100000000000000 : ℝ)^1623
        have hw : |(1136880641/2500000000 : ℝ)|=(1136880641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825949701/2000000000 : ℝ)|^2135 ≤ (15621792925581/50000000000000 : ℝ)^1623
        have hw : |(825949701/2000000000 : ℝ)|=(825949701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (671/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3761/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4817/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4817/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4817/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4817/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4817/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4817/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4817/50000 : ℝ) ^ (4269/1024 : ℝ) ≤ (2900784511101203/50000000000000000000 : ℝ) := by
    have hpowers : (4817/50000 : ℝ)^4269 ≤ (2900784511101203/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4817 : ℕ)^4269*50000000000000000000^1024 ≤ 2900784511101203^1024*50000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4817 50000 2900784511101203 50000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4817/50000 : ℝ)) (X := (2900784511101203/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16237/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (51126000132276209/100000000000000000000 : ℝ) := by
    have hpowers : (16237/100000 : ℝ)^4269 ≤ (51126000132276209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16237 : ℕ)^4269*100000000000000000000^1024 ≤ 51126000132276209^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16237 100000 51126000132276209 100000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16237/100000 : ℝ)) (X := (51126000132276209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002900784511101203/25000000000000000000 : ℝ) ≤ (5000139155416017/5000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (25002900784511101203/25000000000000000000 : ℝ)^1024 ≤ (5000139155416017/5000000000000000 : ℝ)^4269 := by
      have hnat : (25002900784511101203 : ℕ)^1024*5000000000000000^4269 ≤ 5000139155416017^4269*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002900784511101203 25000000000000000000 5000139155416017 5000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139155416017/5000000000000000 : ℝ)) (X := (25002900784511101203/25000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20011385513830895723/20000000000000000000 : ℝ) ≤ (10001365219546719/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (20011385513830895723/20000000000000000000 : ℝ)^1024 ≤ (10001365219546719/10000000000000000 : ℝ)^4269 := by
      have hnat : (20011385513830895723 : ℕ)^1024*10000000000000000^4269 ≤ 10001365219546719^4269*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20011385513830895723 20000000000000000000 10001365219546719 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001365219546719/10000000000000000 : ℝ)) (X := (20011385513830895723/20000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50051126000132276209/50000000000000000000 : ℝ) ≤ (2500613032065351/2500000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50051126000132276209/50000000000000000000 : ℝ)^1024 ≤ (2500613032065351/2500000000000000 : ℝ)^4269 := by
      have hnat : (50051126000132276209 : ℕ)^1024*2500000000000000^4269 ≤ 2500613032065351^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50051126000132276209 50000000000000000000 2500613032065351 2500000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500613032065351/2500000000000000 : ℝ)) (X := (50051126000132276209/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2900784511101203/50000000000000000000 : ℝ) ≤ ((11001815854884894987/11005000000000000000 : ℝ)+2*(72460580979/44020000000000 : ℝ)*(4817/50000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (11001815854884894987/11005000000000000000 : ℝ)+2*(72460580979/44020000000000 : ℝ)*(4817/50000 : ℝ)=(5000139155416017/5000000000000000 : ℝ) by norm_num, show 1+2*(2900784511101203/50000000000000000000 : ℝ)=(25002900784511101203/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51126000132276209/100000000000000000000 : ℝ)+(2900784511101203/50000000000000000000 : ℝ) ≤ ((11001815854884894987/11005000000000000000 : ℝ)+(72460580979/44020000000000 : ℝ)*((16237/100000 : ℝ)+(4817/50000 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (11001815854884894987/11005000000000000000 : ℝ)+(72460580979/44020000000000 : ℝ)*((16237/100000 : ℝ)+(4817/50000 : ℝ))=(10001365219546719/10000000000000000 : ℝ) by norm_num, show 1+(51126000132276209/100000000000000000000 : ℝ)+(2900784511101203/50000000000000000000 : ℝ)=(20011385513830895723/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51126000132276209/100000000000000000000 : ℝ) ≤ ((11001815854884894987/11005000000000000000 : ℝ)+2*(72460580979/44020000000000 : ℝ)*(16237/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (11001815854884894987/11005000000000000000 : ℝ)+2*(72460580979/44020000000000 : ℝ)*(16237/100000 : ℝ)=(2500613032065351/2500000000000000 : ℝ) by norm_num, show 1+2*(51126000132276209/100000000000000000000 : ℝ)=(50051126000132276209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11001815854884894987/11005000000000000000 : ℝ)*(X 1 0+X 2 0)+(72460580979/44020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (4817/50000 : ℝ)) (hi := (16237/100000 : ℝ)) (c := (11001815854884894987/11005000000000000000 : ℝ)) (alpha := (72460580979/44020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11001815854884894987/11005000000000000000 : ℝ)*(X 0 1+X 2 1)+(72460580979/44020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (4817/50000 : ℝ)) (hi := (16237/100000 : ℝ)) (c := (11001815854884894987/11005000000000000000 : ℝ)) (alpha := (72460580979/44020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11001815854884894987/11005000000000000000 : ℝ)*(X 0 2+X 1 2)+(72460580979/44020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (4817/50000 : ℝ)) (hi := (16237/100000 : ℝ)) (c := (11001815854884894987/11005000000000000000 : ℝ)) (alpha := (72460580979/44020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517455599/2500000000 : ℝ)*X 0 0+(1086294007/2000000000 : ℝ)*X 0 1+(522784929/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214154641/400000000 : ℝ)*X 1 0+(-2173977649/10000000000 : ℝ)*X 1 1+(5227849261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676932967/5000000000 : ℝ)*X 2 0+(5227849453/10000000000 : ℝ)*X 2 1+(-2173977517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083444389/2500000000 : ℝ)*X 0 0+(4127945751/10000000000 : ℝ)*X 0 1+(4549314603/10000000000 : ℝ)*X 0 2+(1083444389/2500000000 : ℝ)*X 1 0+(4127945751/10000000000 : ℝ)*X 1 1+(4549314603/10000000000 : ℝ)*X 1 2+(1083444389/2500000000 : ℝ)*X 2 0+(4127945751/10000000000 : ℝ)*X 2 1+(4549314603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2069843659/10000000000 : ℝ)*X 0 0+(163397351/312500000 : ℝ)*X 0 1+(271529937/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132540353/250000000 : ℝ)*X 1 0+(-492807019/2500000000 : ℝ)*X 1 1+(339412419/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21206457/40000000 : ℝ)*X 2 0+(5430598581/10000000000 : ℝ)*X 2 1+(-197122807/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166910859/5000000000 : ℝ)*X 0 0+(1136880641/2500000000 : ℝ)*X 0 1+(825949701/2000000000 : ℝ)*X 0 2+(2166910859/5000000000 : ℝ)*X 1 0+(1136880641/2500000000 : ℝ)*X 1 1+(825949701/2000000000 : ℝ)*X 1 2+(2166910859/5000000000 : ℝ)*X 2 0+(1136880641/2500000000 : ℝ)*X 2 1+(825949701/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1164975927140050229295906519/275125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (331367903/50000000000000 : ℝ)*(base19) + (265067869/50000000000000 : ℝ)*(base23) + (28430681/100000000000000 : ℝ)*(upper3) + (26301157/100000000000000 : ℝ)*(upper4) + (113533797/100000000000000 : ℝ)*(upper5) + (1821085831036321/50000000000000 : ℝ)*(major0) + (1821085831036321/50000000000000 : ℝ)*(major1) + (1821085831036321/50000000000000 : ℝ)*(major2) + (4911101682572349/100000000000000 : ℝ)*(sp0) + (4911114514058201/100000000000000 : ℝ)*(sp1) + (4911114646658269/100000000000000 : ℝ)*(sp2) + (474644678996487/20000000000000 : ℝ)*(sp3) + (6747110829/50000000000000 : ℝ)*(sp4) + (4611223793/100000000000000 : ℝ)*(sp7) + (593307001551557/25000000000000 : ℝ)*(f.failure) + (4911115176794007/100000000000000 : ℝ)*(f.sum) + (108226990851/220100000000000000000000000 : ℝ)*base65 + (1180188067180572827/550250000000000000000000000000000 : ℝ)*base67 + (467186199692427173/550250000000000000000000000000000 : ℝ)*base70 + (2091302774017822827/550250000000000000000000000000000 : ℝ)*base71 + (37749729657/220100000000000000000000000 : ℝ)*base74 + (1238563306674822827/550250000000000000000000000000000 : ℝ)*base75 + (4219676805662572827/550250000000000000000000000000000 : ℝ)*base77 + (2884849830115927173/550250000000000000000000000000000 : ℝ)*base80 + (705086103421/2201000000000000000000000000 : ℝ)*base81 + (63887/25000000000000000000 : ℝ)*base89 + (63887/25000000000000000000 : ℝ)*base91 + (63887/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2504451107938888356004520427/275125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1012767917/50000000000000 : ℝ)*(base19) + (2251972421/100000000000000 : ℝ)*(base23) + (108735889/50000000000000 : ℝ)*(upper3) + (45294017/100000000000000 : ℝ)*(lower4) + (55973673/25000000000000 : ℝ)*(upper5) + (1836747617525431/50000000000000 : ℝ)*(major0) + (1836747617525431/50000000000000 : ℝ)*(major1) + (1836747617525431/50000000000000 : ℝ)*(major2) + (34044224829/100000000000000 : ℝ)*(sp1) + (3602715263/10000000000000 : ℝ)*(sp2) + (619168976916671/12500000000000 : ℝ)*(sp4) + (990663149114541/20000000000000 : ℝ)*(sp5) + (4953313536208317/100000000000000 : ℝ)*(sp6) + (149602396958527/6250000000000 : ℝ)*(sp7) + (149602396958527/6250000000000 : ℝ)*(f.failure) + (619168976916671/12500000000000 : ℝ)*(f.sum) + (220918888217/1100500000000000000000000000 : ℝ)*base65 + (8527756174018164397/550250000000000000000000000000000 : ℝ)*base67 + (3153972053854164397/550250000000000000000000000000000 : ℝ)*base69 + (7136038300048914397/550250000000000000000000000000000 : ℝ)*base71 + (7258725711451/2201000000000000000000000000 : ℝ)*base73 + (4157892521061914397/550250000000000000000000000000000 : ℝ)*base75 + (7470538386712664397/550250000000000000000000000000000 : ℝ)*base77 + (5284501131920414397/550250000000000000000000000000000 : ℝ)*base79 + (3282026112819/1100500000000000000000000000 : ℝ)*base81 + (114843/6250000000000000000 : ℝ)*base90 + (114843/6250000000000000000 : ℝ)*base92 + (114843/6250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3761/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1310_s4_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071561717/10000000000 : ℝ)*x 0 + (5417569037/10000000000 : ℝ)*x 1 + (1310152401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071561717/10000000000 : ℝ)^2135 ≤ (3151763823867/25000000000000 : ℝ)^1623 := by
    have hnat : (2071561717 : ℕ)^2135*25000000000000^1623 ≤ 3151763823867^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071561717 10000000000 3151763823867 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417569037/10000000000 : ℝ)^2135 ≤ (4465077758739/10000000000000 : ℝ)^1623 := by
    have hnat : (5417569037 : ℕ)^2135*10000000000000^1623 ≤ 4465077758739^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417569037 10000000000 4465077758739 10000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310152401/2500000000 : ℝ)^2135 ≤ (42742167101093/100000000000000 : ℝ)^1623 := by
    have hnat : (1310152401 : ℕ)^2135*100000000000000^1623 ≤ 42742167101093^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310152401 2500000000 42742167101093 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071561717/10000000000 : ℝ), (5417569037/10000000000 : ℝ), (1310152401/2500000000 : ℝ)] ![(3151763823867/25000000000000 : ℝ), (4465077758739/10000000000000 : ℝ), (42742167101093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071561717/10000000000 : ℝ)|^2135 ≤ (3151763823867/25000000000000 : ℝ)^1623
        have hw : |(-2071561717/10000000000 : ℝ)|=(2071561717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417569037/10000000000 : ℝ)|^2135 ≤ (4465077758739/10000000000000 : ℝ)^1623
        have hw : |(5417569037/10000000000 : ℝ)|=(5417569037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310152401/2500000000 : ℝ)|^2135 ≤ (42742167101093/100000000000000 : ℝ)^1623
        have hw : |(1310152401/2500000000 : ℝ)|=(1310152401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675171263/5000000000 : ℝ)*x 0 + (-2161812651/10000000000 : ℝ)*x 1 + (262030473/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675171263/5000000000 : ℝ)^2135 ≤ (21961673798751/50000000000000 : ℝ)^1623 := by
    have hnat : (2675171263 : ℕ)^2135*50000000000000^1623 ≤ 21961673798751^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675171263 5000000000 21961673798751 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2161812651/10000000000 : ℝ)^2135 ≤ (13334486819297/100000000000000 : ℝ)^1623 := by
    have hnat : (2161812651 : ℕ)^2135*100000000000000^1623 ≤ 13334486819297^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161812651 10000000000 13334486819297 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262030473/500000000 : ℝ)^2135 ≤ (5342770694517/12500000000000 : ℝ)^1623 := by
    have hnat : (262030473 : ℕ)^2135*12500000000000^1623 ≤ 5342770694517^1623*500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262030473 500000000 5342770694517 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675171263/5000000000 : ℝ), (-2161812651/10000000000 : ℝ), (262030473/500000000 : ℝ)] ![(21961673798751/50000000000000 : ℝ), (13334486819297/100000000000000 : ℝ), (5342770694517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675171263/5000000000 : ℝ)|^2135 ≤ (21961673798751/50000000000000 : ℝ)^1623
        have hw : |(2675171263/5000000000 : ℝ)|=(2675171263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2161812651/10000000000 : ℝ)|^2135 ≤ (13334486819297/100000000000000 : ℝ)^1623
        have hw : |(-2161812651/10000000000 : ℝ)|=(2161812651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262030473/500000000 : ℝ)|^2135 ≤ (5342770694517/12500000000000 : ℝ)^1623
        have hw : |(262030473/500000000 : ℝ)|=(262030473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350342313/10000000000 : ℝ)*x 0 + (2620304713/5000000000 : ℝ)*x 1 + (-2161812981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350342313/10000000000 : ℝ)^2135 ≤ (2745209081079/6250000000000 : ℝ)^1623 := by
    have hnat : (5350342313 : ℕ)^2135*6250000000000^1623 ≤ 2745209081079^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350342313 10000000000 2745209081079 6250000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620304713/5000000000 : ℝ)^2135 ≤ (21371082595677/50000000000000 : ℝ)^1623 := by
    have hnat : (2620304713 : ℕ)^2135*50000000000000^1623 ≤ 21371082595677^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620304713 5000000000 21371082595677 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161812981/10000000000 : ℝ)^2135 ≤ (13334489496933/100000000000000 : ℝ)^1623 := by
    have hnat : (2161812981 : ℕ)^2135*100000000000000^1623 ≤ 13334489496933^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161812981 10000000000 13334489496933 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350342313/10000000000 : ℝ), (2620304713/5000000000 : ℝ), (-2161812981/10000000000 : ℝ)] ![(2745209081079/6250000000000 : ℝ), (21371082595677/50000000000000 : ℝ), (13334489496933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350342313/10000000000 : ℝ)|^2135 ≤ (2745209081079/6250000000000 : ℝ)^1623
        have hw : |(5350342313/10000000000 : ℝ)|=(5350342313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620304713/5000000000 : ℝ)|^2135 ≤ (21371082595677/50000000000000 : ℝ)^1623
        have hw : |(2620304713/5000000000 : ℝ)|=(2620304713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161812981/10000000000 : ℝ)|^2135 ≤ (13334489496933/100000000000000 : ℝ)^1623
        have hw : |(-2161812981/10000000000 : ℝ)|=(2161812981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4334831787/10000000000 : ℝ)*x 0 + (259712481/625000000 : ℝ)*x 1 + (4521596867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334831787/10000000000 : ℝ)^2135 ≤ (4162551740117/12500000000000 : ℝ)^1623 := by
    have hnat : (4334831787 : ℕ)^2135*12500000000000^1623 ≤ 4162551740117^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334831787 10000000000 4162551740117 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259712481/625000000 : ℝ)^2135 ≤ (31499119939223/100000000000000 : ℝ)^1623 := by
    have hnat : (259712481 : ℕ)^2135*100000000000000^1623 ≤ 31499119939223^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259712481 625000000 31499119939223 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521596867/10000000000 : ℝ)^2135 ≤ (7040093226421/20000000000000 : ℝ)^1623 := by
    have hnat : (4521596867 : ℕ)^2135*20000000000000^1623 ≤ 7040093226421^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521596867 10000000000 7040093226421 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334831787/10000000000 : ℝ), (259712481/625000000 : ℝ), (4521596867/10000000000 : ℝ)] ![(4162551740117/12500000000000 : ℝ), (31499119939223/100000000000000 : ℝ), (7040093226421/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334831787/10000000000 : ℝ)|^2135 ≤ (4162551740117/12500000000000 : ℝ)^1623
        have hw : |(4334831787/10000000000 : ℝ)|=(4334831787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259712481/625000000 : ℝ)|^2135 ≤ (31499119939223/100000000000000 : ℝ)^1623
        have hw : |(259712481/625000000 : ℝ)|=(259712481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521596867/10000000000 : ℝ)|^2135 ≤ (7040093226421/20000000000000 : ℝ)^1623
        have hw : |(4521596867/10000000000 : ℝ)|=(4521596867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071575323/10000000000 : ℝ)*x 0 + (2620632111/5000000000 : ℝ)*x 1 + (541691117/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071575323/10000000000 : ℝ)^2135 ≤ (12607164220089/100000000000000 : ℝ)^1623 := by
    have hnat : (2071575323 : ℕ)^2135*100000000000000^1623 ≤ 12607164220089^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071575323 10000000000 12607164220089 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620632111/5000000000 : ℝ)^2135 ≤ (42749190552603/100000000000000 : ℝ)^1623 := by
    have hnat : (2620632111 : ℕ)^2135*100000000000000^1623 ≤ 42749190552603^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620632111 5000000000 42749190552603 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541691117/1000000000 : ℝ)^2135 ≤ (892872904397/2000000000000 : ℝ)^1623 := by
    have hnat : (541691117 : ℕ)^2135*2000000000000^1623 ≤ 892872904397^1623*1000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541691117 1000000000 892872904397 2000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071575323/10000000000 : ℝ), (2620632111/5000000000 : ℝ), (541691117/1000000000 : ℝ)] ![(12607164220089/100000000000000 : ℝ), (42749190552603/100000000000000 : ℝ), (892872904397/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071575323/10000000000 : ℝ)|^2135 ≤ (12607164220089/100000000000000 : ℝ)^1623
        have hw : |(-2071575323/10000000000 : ℝ)|=(2071575323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620632111/5000000000 : ℝ)|^2135 ≤ (42749190552603/100000000000000 : ℝ)^1623
        have hw : |(2620632111/5000000000 : ℝ)|=(2620632111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541691117/1000000000 : ℝ)|^2135 ≤ (892872904397/2000000000000 : ℝ)^1623
        have hw : |(541691117/1000000000 : ℝ)|=(541691117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304934267/10000000000 : ℝ)*x 0 + (-496377789/2500000000 : ℝ)*x 1 + (5416911173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304934267/10000000000 : ℝ)^2135 ≤ (678650478497/1562500000000 : ℝ)^1623 := by
    have hnat : (5304934267 : ℕ)^2135*1562500000000^1623 ≤ 678650478497^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304934267 10000000000 678650478497 1562500000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496377789/2500000000 : ℝ)^2135 ≤ (5961362057071/50000000000000 : ℝ)^1623 := by
    have hnat : (496377789 : ℕ)^2135*50000000000000^1623 ≤ 5961362057071^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496377789 2500000000 5961362057071 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416911173/10000000000 : ℝ)^2135 ≤ (357149162019/800000000000 : ℝ)^1623 := by
    have hnat : (5416911173 : ℕ)^2135*800000000000^1623 ≤ 357149162019^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416911173 10000000000 357149162019 800000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304934267/10000000000 : ℝ), (-496377789/2500000000 : ℝ), (5416911173/10000000000 : ℝ)] ![(678650478497/1562500000000 : ℝ), (5961362057071/50000000000000 : ℝ), (357149162019/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304934267/10000000000 : ℝ)|^2135 ≤ (678650478497/1562500000000 : ℝ)^1623
        have hw : |(5304934267/10000000000 : ℝ)|=(5304934267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496377789/2500000000 : ℝ)|^2135 ≤ (5961362057071/50000000000000 : ℝ)^1623
        have hw : |(-496377789/2500000000 : ℝ)|=(496377789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416911173/10000000000 : ℝ)|^2135 ≤ (357149162019/800000000000 : ℝ)^1623
        have hw : |(5416911173/10000000000 : ℝ)|=(5416911173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304934273/10000000000 : ℝ)*x 0 + (1354227791/2500000000 : ℝ)*x 1 + (-1985511159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304934273/10000000000 : ℝ)^2135 ≤ (43433630688429/100000000000000 : ℝ)^1623 := by
    have hnat : (5304934273 : ℕ)^2135*100000000000000^1623 ≤ 43433630688429^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304934273 10000000000 43433630688429 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354227791/2500000000 : ℝ)^2135 ≤ (22321822577401/50000000000000 : ℝ)^1623 := by
    have hnat : (1354227791 : ℕ)^2135*50000000000000^1623 ≤ 22321822577401^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354227791 2500000000 22321822577401 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985511159/10000000000 : ℝ)^2135 ≤ (149034051723/1250000000000 : ℝ)^1623 := by
    have hnat : (1985511159 : ℕ)^2135*1250000000000^1623 ≤ 149034051723^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985511159 10000000000 149034051723 1250000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304934273/10000000000 : ℝ), (1354227791/2500000000 : ℝ), (-1985511159/10000000000 : ℝ)] ![(43433630688429/100000000000000 : ℝ), (22321822577401/50000000000000 : ℝ), (149034051723/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304934273/10000000000 : ℝ)|^2135 ≤ (43433630688429/100000000000000 : ℝ)^1623
        have hw : |(5304934273/10000000000 : ℝ)|=(5304934273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354227791/2500000000 : ℝ)|^2135 ≤ (22321822577401/50000000000000 : ℝ)^1623
        have hw : |(1354227791/2500000000 : ℝ)|=(1354227791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1985511159/10000000000 : ℝ)|^2135 ≤ (149034051723/1250000000000 : ℝ)^1623
        have hw : |(-1985511159/10000000000 : ℝ)|=(1985511159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s4_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4334861007/10000000000 : ℝ)*x 0 + (4520242011/10000000000 : ℝ)*x 1 + (2078380693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334861007/10000000000 : ℝ)^2135 ≤ (8325177300809/25000000000000 : ℝ)^1623 := by
    have hnat : (4334861007 : ℕ)^2135*25000000000000^1623 ≤ 8325177300809^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334861007 10000000000 8325177300809 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4520242011/10000000000 : ℝ)^2135 ≤ (17593295956547/50000000000000 : ℝ)^1623 := by
    have hnat : (4520242011 : ℕ)^2135*50000000000000^1623 ≤ 17593295956547^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520242011 10000000000 17593295956547 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078380693/5000000000 : ℝ)^2135 ≤ (15756349436487/50000000000000 : ℝ)^1623 := by
    have hnat : (2078380693 : ℕ)^2135*50000000000000^1623 ≤ 15756349436487^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078380693 5000000000 15756349436487 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334861007/10000000000 : ℝ), (4520242011/10000000000 : ℝ), (2078380693/5000000000 : ℝ)] ![(8325177300809/25000000000000 : ℝ), (17593295956547/50000000000000 : ℝ), (15756349436487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334861007/10000000000 : ℝ)|^2135 ≤ (8325177300809/25000000000000 : ℝ)^1623
        have hw : |(4334861007/10000000000 : ℝ)|=(4334861007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4520242011/10000000000 : ℝ)|^2135 ≤ (17593295956547/50000000000000 : ℝ)^1623
        have hw : |(4520242011/10000000000 : ℝ)|=(4520242011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078380693/5000000000 : ℝ)|^2135 ≤ (15756349436487/50000000000000 : ℝ)^1623
        have hw : |(2078380693/5000000000 : ℝ)|=(2078380693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3761/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (344/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3761/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3761/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (671/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3761/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3761/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (671/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3761/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3761/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (671/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (671/6250 : ℝ) ^ (4269/1024 : ℝ) ≤ (9112454966870733/100000000000000000000 : ℝ) := by
    have hpowers : (671/6250 : ℝ)^4269 ≤ (9112454966870733/100000000000000000000 : ℝ)^1024 := by
      have hnat : (671 : ℕ)^4269*100000000000000000000^1024 ≤ 9112454966870733^1024*6250^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        671 6250 9112454966870733 100000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (671/6250 : ℝ)) (X := (9112454966870733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3761/25000 : ℝ) ^ (4269/1024 : ℝ) ≤ (4649247881339539/12500000000000000000 : ℝ) := by
    have hpowers : (3761/25000 : ℝ)^4269 ≤ (4649247881339539/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3761 : ℕ)^4269*12500000000000000000^1024 ≤ 4649247881339539^1024*25000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3761 25000 4649247881339539 12500000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3761/25000 : ℝ)) (X := (4649247881339539/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009112454966870733/50000000000000000000 : ℝ) ≤ (500021856424497/500000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50009112454966870733/50000000000000000000 : ℝ)^1024 ≤ (500021856424497/500000000000000 : ℝ)^4269 := by
      have hnat : (50009112454966870733 : ℕ)^1024*500000000000000^4269 ≤ 500021856424497^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009112454966870733 50000000000000000000 500021856424497 500000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500021856424497/500000000000000 : ℝ)) (X := (50009112454966870733/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009261287603517409/20000000000000000000 : ℝ) ≤ (10001110551639961/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (20009261287603517409/20000000000000000000 : ℝ)^1024 ≤ (10001110551639961/10000000000000000 : ℝ)^4269 := by
      have hnat : (20009261287603517409 : ℕ)^1024*10000000000000000^4269 ≤ 10001110551639961^4269*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009261287603517409 20000000000000000000 10001110551639961 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001110551639961/10000000000000000 : ℝ)) (X := (20009261287603517409/20000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254649247881339539/6250000000000000000 : ℝ) ≤ (5000891987394991/5000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (6254649247881339539/6250000000000000000 : ℝ)^1024 ≤ (5000891987394991/5000000000000000 : ℝ)^4269 := by
      have hnat : (6254649247881339539 : ℕ)^1024*5000000000000000^4269 ≤ 5000891987394991^4269*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254649247881339539 6250000000000000000 5000891987394991 5000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000891987394991/5000000000000000 : ℝ)) (X := (6254649247881339539/6250000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9112454966870733/100000000000000000000 : ℝ) ≤ ((2691713962978588163/2692500000000000000 : ℝ)+2*(673423150021/430800000000000 : ℝ)*(671/6250 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (2691713962978588163/2692500000000000000 : ℝ)+2*(673423150021/430800000000000 : ℝ)*(671/6250 : ℝ)=(500021856424497/500000000000000 : ℝ) by norm_num, show 1+2*(9112454966870733/100000000000000000000 : ℝ)=(50009112454966870733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4649247881339539/12500000000000000000 : ℝ)+(9112454966870733/100000000000000000000 : ℝ) ≤ ((2691713962978588163/2692500000000000000 : ℝ)+(673423150021/430800000000000 : ℝ)*((3761/25000 : ℝ)+(671/6250 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (2691713962978588163/2692500000000000000 : ℝ)+(673423150021/430800000000000 : ℝ)*((3761/25000 : ℝ)+(671/6250 : ℝ))=(10001110551639961/10000000000000000 : ℝ) by norm_num, show 1+(4649247881339539/12500000000000000000 : ℝ)+(9112454966870733/100000000000000000000 : ℝ)=(20009261287603517409/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4649247881339539/12500000000000000000 : ℝ) ≤ ((2691713962978588163/2692500000000000000 : ℝ)+2*(673423150021/430800000000000 : ℝ)*(3761/25000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (2691713962978588163/2692500000000000000 : ℝ)+2*(673423150021/430800000000000 : ℝ)*(3761/25000 : ℝ)=(5000891987394991/5000000000000000 : ℝ) by norm_num, show 1+2*(4649247881339539/12500000000000000000 : ℝ)=(6254649247881339539/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2691713962978588163/2692500000000000000 : ℝ)*(X 1 0+X 2 0)+(673423150021/430800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (3761/25000 : ℝ)) (c := (2691713962978588163/2692500000000000000 : ℝ)) (alpha := (673423150021/430800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2691713962978588163/2692500000000000000 : ℝ)*(X 0 1+X 2 1)+(673423150021/430800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (3761/25000 : ℝ)) (c := (2691713962978588163/2692500000000000000 : ℝ)) (alpha := (673423150021/430800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2691713962978588163/2692500000000000000 : ℝ)*(X 0 2+X 1 2)+(673423150021/430800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (671/6250 : ℝ)) (hi := (3761/25000 : ℝ)) (c := (2691713962978588163/2692500000000000000 : ℝ)) (alpha := (673423150021/430800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2071561717/10000000000 : ℝ)*X 0 0+(5417569037/10000000000 : ℝ)*X 0 1+(1310152401/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675171263/5000000000 : ℝ)*X 1 0+(-2161812651/10000000000 : ℝ)*X 1 1+(262030473/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350342313/10000000000 : ℝ)*X 2 0+(2620304713/5000000000 : ℝ)*X 2 1+(-2161812981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4334831787/10000000000 : ℝ)*X 0 0+(259712481/625000000 : ℝ)*X 0 1+(4521596867/10000000000 : ℝ)*X 0 2+(4334831787/10000000000 : ℝ)*X 1 0+(259712481/625000000 : ℝ)*X 1 1+(4521596867/10000000000 : ℝ)*X 1 2+(4334831787/10000000000 : ℝ)*X 2 0+(259712481/625000000 : ℝ)*X 2 1+(4521596867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2071575323/10000000000 : ℝ)*X 0 0+(2620632111/5000000000 : ℝ)*X 0 1+(541691117/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304934267/10000000000 : ℝ)*X 1 0+(-496377789/2500000000 : ℝ)*X 1 1+(5416911173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304934273/10000000000 : ℝ)*X 2 0+(1354227791/2500000000 : ℝ)*X 2 1+(-1985511159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334861007/10000000000 : ℝ)*X 0 0+(4520242011/10000000000 : ℝ)*X 0 1+(2078380693/5000000000 : ℝ)*X 0 2+(4334861007/10000000000 : ℝ)*X 1 0+(4520242011/10000000000 : ℝ)*X 1 1+(2078380693/5000000000 : ℝ)*X 1 2+(4334861007/10000000000 : ℝ)*X 2 0+(4520242011/10000000000 : ℝ)*X 2 1+(2078380693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44714893383155107797342939/5609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1994526659/100000000000000 : ℝ)*(base19) + (893039539/50000000000000 : ℝ)*(base23) + (6207321/5000000000000 : ℝ)*(upper2) + (413508377/100000000000000 : ℝ)*(upper3) + (57652517/50000000000000 : ℝ)*(upper4) + (523867942073097/12500000000000 : ℝ)*(major0) + (523867942073097/12500000000000 : ℝ)*(major1) + (523867942073097/12500000000000 : ℝ)*(major2) + (1130210987830011/20000000000000 : ℝ)*(sp0) + (176596209938433/3125000000000 : ℝ)*(sp1) + (5651078926477437/100000000000000 : ℝ)*(sp2) + (54615702915651/2000000000000 : ℝ)*(sp3) + (1288670323/5000000000000 : ℝ)*(sp4) + (10474557617/50000000000000 : ℝ)*(sp7) + (341350761862223/12500000000000 : ℝ)*(f.failure) + (1130216142511303/20000000000000 : ℝ)*(f.sum) + (112437904323/1795000000000000000000000000 : ℝ)*base65 + (39106711924658063/11218750000000000000000000000000 : ℝ)*base68 + (90752674533623187/11218750000000000000000000000000 : ℝ)*base69 + (62289111038310687/11218750000000000000000000000000 : ℝ)*base71 + (765169842887/448750000000000000000000000 : ℝ)*base73 + (91181776687998187/11218750000000000000000000000000 : ℝ)*base75 + (1954337507783063/11218750000000000000000000000000 : ℝ)*base78 + (158433037996810687/11218750000000000000000000000000 : ℝ)*base79 + (2116287942143/1795000000000000000000000000 : ℝ)*base81 + (121907/12500000000000000000 : ℝ)*base90 + (121907/12500000000000000000 : ℝ)*base92 + (121907/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1119541921879843324690377/448750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (451573359/100000000000000 : ℝ)*(base19) + (486086417/100000000000000 : ℝ)*(base23) + (51559653/100000000000000 : ℝ)*(upper3) + (6615053/50000000000000 : ℝ)*(lower4) + (2666461/5000000000000 : ℝ)*(upper5) + (42222084126079/1000000000000 : ℝ)*(major0) + (42222084126079/1000000000000 : ℝ)*(major1) + (42222084126079/1000000000000 : ℝ)*(major2) + (8911337049/100000000000000 : ℝ)*(sp1) + (4638796463/50000000000000 : ℝ)*(sp2) + (5693238548785651/100000000000000 : ℝ)*(sp4) + (5693229185875243/100000000000000 : ℝ)*(sp5) + (5693228785106307/100000000000000 : ℝ)*(sp6) + (2751178193270111/100000000000000 : ℝ)*(sp7) + (2751178193270111/100000000000000 : ℝ)*(f.failure) + (5693238548785651/100000000000000 : ℝ)*(f.sum) + (1576750621513/1077000000000000000000000000 : ℝ)*base66 + (8692249632885291/897500000000000000000000000000 : ℝ)*base68 + (2563261419152791/897500000000000000000000000000 : ℝ)*base70 + (3649419433762791/897500000000000000000000000000 : ℝ)*base72 + (4801874412583/1077000000000000000000000000 : ℝ)*base74 + (16017730507480291/897500000000000000000000000000 : ℝ)*base76 + (6260470421622209/897500000000000000000000000000 : ℝ)*base77 + (4080653278569709/897500000000000000000000000000 : ℝ)*base79 + (51294220249/67312500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (79299/100000000000000000000 : ℝ)*base90 + (79299/100000000000000000000 : ℝ)*base92 + (79299/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3761/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (671/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1310_s5_0 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1035940393/5000000000 : ℝ)*x 0 + (2707435041/5000000000 : ℝ)*x 1 + (1048619699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035940393/5000000000 : ℝ)^2135 ≤ (3152402425921/25000000000000 : ℝ)^1623 := by
    have hnat : (1035940393 : ℕ)^2135*25000000000000^1623 ≤ 3152402425921^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035940393 5000000000 3152402425921 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707435041/5000000000 : ℝ)^2135 ≤ (44621518185571/100000000000000 : ℝ)^1623 := by
    have hnat : (2707435041 : ℕ)^2135*100000000000000^1623 ≤ 44621518185571^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707435041 5000000000 44621518185571 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048619699/2000000000 : ℝ)^2135 ≤ (42768872095721/100000000000000 : ℝ)^1623 := by
    have hnat : (1048619699 : ℕ)^2135*100000000000000^1623 ≤ 42768872095721^1623*2000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048619699 2000000000 42768872095721 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1035940393/5000000000 : ℝ), (2707435041/5000000000 : ℝ), (1048619699/2000000000 : ℝ)] ![(3152402425921/25000000000000 : ℝ), (44621518185571/100000000000000 : ℝ), (42768872095721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1035940393/5000000000 : ℝ)|^2135 ≤ (3152402425921/25000000000000 : ℝ)^1623
        have hw : |(-1035940393/5000000000 : ℝ)|=(1035940393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707435041/5000000000 : ℝ)|^2135 ≤ (44621518185571/100000000000000 : ℝ)^1623
        have hw : |(2707435041/5000000000 : ℝ)|=(2707435041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048619699/2000000000 : ℝ)|^2135 ≤ (42768872095721/100000000000000 : ℝ)^1623
        have hw : |(1048619699/2000000000 : ℝ)|=(1048619699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_1 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674827523/5000000000 : ℝ)*x 0 + (-2159435851/10000000000 : ℝ)*x 1 + (1310774617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674827523/5000000000 : ℝ)^2135 ≤ (21957961743123/50000000000000 : ℝ)^1623 := by
    have hnat : (2674827523 : ℕ)^2135*50000000000000^1623 ≤ 21957961743123^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674827523 5000000000 21957961743123 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159435851/10000000000 : ℝ)^2135 ≤ (13315204693561/100000000000000 : ℝ)^1623 := by
    have hnat : (2159435851 : ℕ)^2135*100000000000000^1623 ≤ 13315204693561^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159435851 10000000000 13315204693561 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310774617/2500000000 : ℝ)^2135 ≤ (21384435902999/50000000000000 : ℝ)^1623 := by
    have hnat : (1310774617 : ℕ)^2135*50000000000000^1623 ≤ 21384435902999^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310774617 2500000000 21384435902999 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674827523/5000000000 : ℝ), (-2159435851/10000000000 : ℝ), (1310774617/2500000000 : ℝ)] ![(21957961743123/50000000000000 : ℝ), (13315204693561/100000000000000 : ℝ), (21384435902999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674827523/5000000000 : ℝ)|^2135 ≤ (21957961743123/50000000000000 : ℝ)^1623
        have hw : |(2674827523/5000000000 : ℝ)|=(2674827523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159435851/10000000000 : ℝ)|^2135 ≤ (13315204693561/100000000000000 : ℝ)^1623
        have hw : |(-2159435851/10000000000 : ℝ)|=(2159435851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310774617/2500000000 : ℝ)|^2135 ≤ (21384435902999/50000000000000 : ℝ)^1623
        have hw : |(1310774617/2500000000 : ℝ)|=(1310774617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_2 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674827493/5000000000 : ℝ)*x 0 + (2621549251/5000000000 : ℝ)*x 1 + (-1079717943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674827493/5000000000 : ℝ)^2135 ≤ (21957961419159/50000000000000 : ℝ)^1623 := by
    have hnat : (2674827493 : ℕ)^2135*50000000000000^1623 ≤ 21957961419159^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674827493 5000000000 21957961419159 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621549251/5000000000 : ℝ)^2135 ≤ (8553774434167/20000000000000 : ℝ)^1623 := by
    have hnat : (2621549251 : ℕ)^2135*20000000000000^1623 ≤ 8553774434167^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621549251 5000000000 8553774434167 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079717943/5000000000 : ℝ)^2135 ≤ (2663040995491/20000000000000 : ℝ)^1623 := by
    have hnat : (1079717943 : ℕ)^2135*20000000000000^1623 ≤ 2663040995491^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079717943 5000000000 2663040995491 20000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674827493/5000000000 : ℝ), (2621549251/5000000000 : ℝ), (-1079717943/5000000000 : ℝ)] ![(21957961419159/50000000000000 : ℝ), (8553774434167/20000000000000 : ℝ), (2663040995491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674827493/5000000000 : ℝ)|^2135 ≤ (21957961419159/50000000000000 : ℝ)^1623
        have hw : |(2674827493/5000000000 : ℝ)|=(2674827493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621549251/5000000000 : ℝ)|^2135 ≤ (8553774434167/20000000000000 : ℝ)^1623
        have hw : |(2621549251/5000000000 : ℝ)|=(2621549251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079717943/5000000000 : ℝ)|^2135 ≤ (2663040995491/20000000000000 : ℝ)^1623
        have hw : |(-1079717943/5000000000 : ℝ)|=(1079717943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_3 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4335020201/10000000000 : ℝ)*x 0 + (4160744023/10000000000 : ℝ)*x 1 + (2258102527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335020201/10000000000 : ℝ)^2135 ≤ (33302317946999/100000000000000 : ℝ)^1623 := by
    have hnat : (4335020201 : ℕ)^2135*100000000000000^1623 ≤ 33302317946999^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335020201 10000000000 33302317946999 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4160744023/10000000000 : ℝ)^2135 ≤ (31552422253601/100000000000000 : ℝ)^1623 := by
    have hnat : (4160744023 : ℕ)^2135*100000000000000^1623 ≤ 31552422253601^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160744023 10000000000 31552422253601 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258102527/5000000000 : ℝ)^2135 ≤ (35145259781377/100000000000000 : ℝ)^1623 := by
    have hnat : (2258102527 : ℕ)^2135*100000000000000^1623 ≤ 35145259781377^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258102527 5000000000 35145259781377 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335020201/10000000000 : ℝ), (4160744023/10000000000 : ℝ), (2258102527/5000000000 : ℝ)] ![(33302317946999/100000000000000 : ℝ), (31552422253601/100000000000000 : ℝ), (35145259781377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335020201/10000000000 : ℝ)|^2135 ≤ (33302317946999/100000000000000 : ℝ)^1623
        have hw : |(4335020201/10000000000 : ℝ)|=(4335020201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4160744023/10000000000 : ℝ)|^2135 ≤ (31552422253601/100000000000000 : ℝ)^1623
        have hw : |(4160744023/10000000000 : ℝ)|=(4160744023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258102527/5000000000 : ℝ)|^2135 ≤ (35145259781377/100000000000000 : ℝ)^1623
        have hw : |(2258102527/5000000000 : ℝ)|=(2258102527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_4 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071893557/10000000000 : ℝ)*x 0 + (1310928857/2500000000 : ℝ)*x 1 + (338390621/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071893557/10000000000 : ℝ)^2135 ≤ (12609711948563/100000000000000 : ℝ)^1623 := by
    have hnat : (2071893557 : ℕ)^2135*100000000000000^1623 ≤ 12609711948563^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071893557 10000000000 12609711948563 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310928857/2500000000 : ℝ)^2135 ≤ (42775492205663/100000000000000 : ℝ)^1623 := by
    have hnat : (1310928857 : ℕ)^2135*100000000000000^1623 ≤ 42775492205663^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310928857 2500000000 42775492205663 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338390621/625000000 : ℝ)^2135 ≤ (22307397912819/50000000000000 : ℝ)^1623 := by
    have hnat : (338390621 : ℕ)^2135*50000000000000^1623 ≤ 22307397912819^1623*625000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338390621 625000000 22307397912819 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071893557/10000000000 : ℝ), (1310928857/2500000000 : ℝ), (338390621/625000000 : ℝ)] ![(12609711948563/100000000000000 : ℝ), (42775492205663/100000000000000 : ℝ), (22307397912819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071893557/10000000000 : ℝ)|^2135 ≤ (12609711948563/100000000000000 : ℝ)^1623
        have hw : |(-2071893557/10000000000 : ℝ)|=(2071893557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310928857/2500000000 : ℝ)|^2135 ≤ (42775492205663/100000000000000 : ℝ)^1623
        have hw : |(1310928857/2500000000 : ℝ)|=(1310928857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338390621/625000000 : ℝ)|^2135 ≤ (22307397912819/50000000000000 : ℝ)^1623
        have hw : |(338390621/625000000 : ℝ)|=(338390621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_5 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265278923/500000000 : ℝ)*x 0 + (-994142203/5000000000 : ℝ)*x 1 + (5414249929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265278923/500000000 : ℝ)^2135 ≤ (5430071108949/12500000000000 : ℝ)^1623 := by
    have hnat : (265278923 : ℕ)^2135*12500000000000^1623 ≤ 5430071108949^1623*500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265278923 500000000 5430071108949 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994142203/5000000000 : ℝ)^2135 ≤ (5972317682817/50000000000000 : ℝ)^1623 := by
    have hnat : (994142203 : ℕ)^2135*50000000000000^1623 ≤ 5972317682817^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994142203 5000000000 5972317682817 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414249929/10000000000 : ℝ)^2135 ≤ (44614795749759/100000000000000 : ℝ)^1623 := by
    have hnat : (5414249929 : ℕ)^2135*100000000000000^1623 ≤ 44614795749759^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414249929 10000000000 44614795749759 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265278923/500000000 : ℝ), (-994142203/5000000000 : ℝ), (5414249929/10000000000 : ℝ)] ![(5430071108949/12500000000000 : ℝ), (5972317682817/50000000000000 : ℝ), (44614795749759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265278923/500000000 : ℝ)|^2135 ≤ (5430071108949/12500000000000 : ℝ)^1623
        have hw : |(265278923/500000000 : ℝ)|=(265278923/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-994142203/5000000000 : ℝ)|^2135 ≤ (5972317682817/50000000000000 : ℝ)^1623
        have hw : |(-994142203/5000000000 : ℝ)|=(994142203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414249929/10000000000 : ℝ)|^2135 ≤ (44614795749759/100000000000000 : ℝ)^1623
        have hw : |(5414249929/10000000000 : ℝ)|=(5414249929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_6 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652789227/5000000000 : ℝ)*x 0 + (5414249933/10000000000 : ℝ)*x 1 + (-1988284407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652789227/5000000000 : ℝ)^2135 ≤ (5430071100871/12500000000000 : ℝ)^1623 := by
    have hnat : (2652789227 : ℕ)^2135*12500000000000^1623 ≤ 5430071100871^1623*5000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652789227 5000000000 5430071100871 12500000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414249933/10000000000 : ℝ)^2135 ≤ (22307397896559/50000000000000 : ℝ)^1623 := by
    have hnat : (5414249933 : ℕ)^2135*50000000000000^1623 ≤ 22307397896559^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414249933 10000000000 22307397896559 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988284407/10000000000 : ℝ)^2135 ≤ (11944635373537/100000000000000 : ℝ)^1623 := by
    have hnat : (1988284407 : ℕ)^2135*100000000000000^1623 ≤ 11944635373537^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988284407 10000000000 11944635373537 100000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652789227/5000000000 : ℝ), (5414249933/10000000000 : ℝ), (-1988284407/10000000000 : ℝ)] ![(5430071100871/12500000000000 : ℝ), (22307397896559/50000000000000 : ℝ), (11944635373537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652789227/5000000000 : ℝ)|^2135 ≤ (5430071100871/12500000000000 : ℝ)^1623
        have hw : |(2652789227/5000000000 : ℝ)|=(2652789227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414249933/10000000000 : ℝ)|^2135 ≤ (22307397896559/50000000000000 : ℝ)^1623
        have hw : |(5414249933/10000000000 : ℝ)|=(5414249933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988284407/10000000000 : ℝ)|^2135 ≤ (11944635373537/100000000000000 : ℝ)^1623
        have hw : |(-1988284407/10000000000 : ℝ)|=(1988284407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1310_s5_7 (p : ℝ) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1083761649/2500000000 : ℝ)*x 0 + (4514928349/10000000000 : ℝ)*x 1 + (1040506829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083761649/2500000000 : ℝ)^2135 ≤ (8325646171233/25000000000000 : ℝ)^1623 := by
    have hnat : (1083761649 : ℕ)^2135*25000000000000^1623 ≤ 8325646171233^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083761649 2500000000 8325646171233 25000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514928349/10000000000 : ℝ)^2135 ≤ (17566095371139/50000000000000 : ℝ)^1623 := by
    have hnat : (4514928349 : ℕ)^2135*50000000000000^1623 ≤ 17566095371139^1623*10000000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514928349 10000000000 17566095371139 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040506829/2500000000 : ℝ)^2135 ≤ (15782612277071/50000000000000 : ℝ)^1623 := by
    have hnat : (1040506829 : ℕ)^2135*50000000000000^1623 ≤ 15782612277071^1623*2500000000^2135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040506829 2500000000 15782612277071 50000000000000 2135 1623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2135/512 : ℝ)) 2135 1623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083761649/2500000000 : ℝ), (4514928349/10000000000 : ℝ), (1040506829/2500000000 : ℝ)] ![(8325646171233/25000000000000 : ℝ), (17566095371139/50000000000000 : ℝ), (15782612277071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083761649/2500000000 : ℝ)|^2135 ≤ (8325646171233/25000000000000 : ℝ)^1623
        have hw : |(1083761649/2500000000 : ℝ)|=(1083761649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514928349/10000000000 : ℝ)|^2135 ≤ (17566095371139/50000000000000 : ℝ)^1623
        have hw : |(4514928349/10000000000 : ℝ)|=(4514928349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040506829/2500000000 : ℝ)|^2135 ≤ (15782612277071/50000000000000 : ℝ)^1623
        have hw : |(1040506829/2500000000 : ℝ)|=(1040506829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1310_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11061/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14697/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (344/3125 : ℝ) ^ (4269/1024 : ℝ) ≤ (316071134250683/3125000000000000000 : ℝ) := by
    have hpowers : (344/3125 : ℝ)^4269 ≤ (316071134250683/3125000000000000000 : ℝ)^1024 := by
      have hnat : (344 : ℕ)^4269*3125000000000000000^1024 ≤ 316071134250683^1024*3125^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        344 3125 316071134250683 3125000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (344/3125 : ℝ)) (X := (316071134250683/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (4269/1024 : ℝ) ≤ (17142636004592793/50000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^4269 ≤ (17142636004592793/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14753 : ℕ)^4269*50000000000000000000^1024 ≤ 17142636004592793^1024*100000^4269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 17142636004592793 50000000000000000000 4269 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (17142636004592793/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562816071134250683/1562500000000000000 : ℝ) ≤ (2000097036521487/2000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (1562816071134250683/1562500000000000000 : ℝ)^1024 ≤ (2000097036521487/2000000000000000 : ℝ)^4269 := by
      have hnat : (1562816071134250683 : ℕ)^1024*2000000000000000^4269 ≤ 2000097036521487^4269*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562816071134250683 1562500000000000000 2000097036521487 2000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000097036521487/2000000000000000 : ℝ)) (X := (1562816071134250683/1562500000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022199774152603721/50000000000000000000 : ℝ) ≤ (10001064827063447/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (50022199774152603721/50000000000000000000 : ℝ)^1024 ≤ (10001064827063447/10000000000000000 : ℝ)^4269 := by
      have hnat : (50022199774152603721 : ℕ)^1024*10000000000000000^4269 ≤ 10001064827063447^4269*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022199774152603721 50000000000000000000 10001064827063447 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001064827063447/10000000000000000 : ℝ)) (X := (50022199774152603721/50000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017142636004592793/25000000000000000000 : ℝ) ≤ (10001644471519459/10000000000000000 : ℝ) ^ (4269/1024 : ℝ) := by
    have hpowers : (25017142636004592793/25000000000000000000 : ℝ)^1024 ≤ (10001644471519459/10000000000000000 : ℝ)^4269 := by
      have hnat : (25017142636004592793 : ℕ)^1024*10000000000000000^4269 ≤ 10001644471519459^4269*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017142636004592793 25000000000000000000 10001644471519459 10000000000000000 1024 4269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001644471519459/10000000000000000 : ℝ)) (X := (25017142636004592793/25000000000000000000 : ℝ)) (by norm_num) 4269 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(316071134250683/3125000000000000000 : ℝ) ≤ ((37439055556521283883/37450000000000000000 : ℝ)+2*(144911114003/93625000000000 : ℝ)*(344/3125 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (37439055556521283883/37450000000000000000 : ℝ)+2*(144911114003/93625000000000 : ℝ)*(344/3125 : ℝ)=(2000097036521487/2000000000000000 : ℝ) by norm_num, show 1+2*(316071134250683/3125000000000000000 : ℝ)=(1562816071134250683/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17142636004592793/50000000000000000000 : ℝ)+(316071134250683/3125000000000000000 : ℝ) ≤ ((37439055556521283883/37450000000000000000 : ℝ)+(144911114003/93625000000000 : ℝ)*((14753/100000 : ℝ)+(344/3125 : ℝ)))^(4269/1024 : ℝ) := by
    rw [show (37439055556521283883/37450000000000000000 : ℝ)+(144911114003/93625000000000 : ℝ)*((14753/100000 : ℝ)+(344/3125 : ℝ))=(10001064827063447/10000000000000000 : ℝ) by norm_num, show 1+(17142636004592793/50000000000000000000 : ℝ)+(316071134250683/3125000000000000000 : ℝ)=(50022199774152603721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17142636004592793/50000000000000000000 : ℝ) ≤ ((37439055556521283883/37450000000000000000 : ℝ)+2*(144911114003/93625000000000 : ℝ)*(14753/100000 : ℝ))^(4269/1024 : ℝ) := by
    rw [show (37439055556521283883/37450000000000000000 : ℝ)+2*(144911114003/93625000000000 : ℝ)*(14753/100000 : ℝ)=(10001644471519459/10000000000000000 : ℝ) by norm_num, show 1+2*(17142636004592793/50000000000000000000 : ℝ)=(25017142636004592793/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37439055556521283883/37450000000000000000 : ℝ)*(X 1 0+X 2 0)+(144911114003/93625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (37439055556521283883/37450000000000000000 : ℝ)) (alpha := (144911114003/93625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37439055556521283883/37450000000000000000 : ℝ)*(X 0 1+X 2 1)+(144911114003/93625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (37439055556521283883/37450000000000000000 : ℝ)) (alpha := (144911114003/93625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37439055556521283883/37450000000000000000 : ℝ)*(X 0 2+X 1 2)+(144911114003/93625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4269/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (37439055556521283883/37450000000000000000 : ℝ)) (alpha := (144911114003/93625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1035940393/5000000000 : ℝ)*X 0 0+(2707435041/5000000000 : ℝ)*X 0 1+(1048619699/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674827523/5000000000 : ℝ)*X 1 0+(-2159435851/10000000000 : ℝ)*X 1 1+(1310774617/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674827493/5000000000 : ℝ)*X 2 0+(2621549251/5000000000 : ℝ)*X 2 1+(-1079717943/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4335020201/10000000000 : ℝ)*X 0 0+(4160744023/10000000000 : ℝ)*X 0 1+(2258102527/5000000000 : ℝ)*X 0 2+(4335020201/10000000000 : ℝ)*X 1 0+(4160744023/10000000000 : ℝ)*X 1 1+(2258102527/5000000000 : ℝ)*X 1 2+(4335020201/10000000000 : ℝ)*X 2 0+(4160744023/10000000000 : ℝ)*X 2 1+(2258102527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2071893557/10000000000 : ℝ)*X 0 0+(1310928857/2500000000 : ℝ)*X 0 1+(338390621/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265278923/500000000 : ℝ)*X 1 0+(-994142203/5000000000 : ℝ)*X 1 1+(5414249929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652789227/5000000000 : ℝ)*X 2 0+(5414249933/10000000000 : ℝ)*X 2 1+(-1988284407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083761649/2500000000 : ℝ)*X 0 0+(4514928349/10000000000 : ℝ)*X 0 1+(1040506829/2500000000 : ℝ)*X 0 2+(1083761649/2500000000 : ℝ)*X 1 0+(4514928349/10000000000 : ℝ)*X 1 1+(1040506829/2500000000 : ℝ)*X 1 2+(1083761649/2500000000 : ℝ)*X 2 0+(4514928349/10000000000 : ℝ)*X 2 1+(1040506829/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1310_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19555035789330181911988123251/1872500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (195029407/10000000000000 : ℝ)*(base19) + (172584493/10000000000000 : ℝ)*(base23) + (85141983/100000000000000 : ℝ)*(lower2) + (449091/156250000000 : ℝ)*(upper3) + (57813813/50000000000000 : ℝ)*(upper5) + (4317524100630033/100000000000000 : ℝ)*(major0) + (4317524100630033/100000000000000 : ℝ)*(major1) + (4317524100630033/100000000000000 : ℝ)*(major2) + (2910862876396749/50000000000000 : ℝ)*(sp0) + (2910880148209349/50000000000000 : ℝ)*(sp1) + (5821760520867837/100000000000000 : ℝ)*(sp2) + (2813265233208511/100000000000000 : ℝ)*(sp3) + (3649391927/10000000000000 : ℝ)*(sp4) + (407464591/2000000000000 : ℝ)*(sp7) + (140664280321903/5000000000000 : ℝ)*(f.failure) + (90965035104887/1562500000000 : ℝ)*(f.sum) + (103948147893029/18725000000000000000000000000 : ℝ)*base66 + (71408329220566741861/3745000000000000000000000000000000 : ℝ)*base68 + (55795939251691741861/3745000000000000000000000000000000 : ℝ)*base70 + (18188042542966741861/3745000000000000000000000000000000 : ℝ)*base72 + (10154867657271/18725000000000000000000000000 : ℝ)*base73 + (48208952867021741861/3745000000000000000000000000000000 : ℝ)*base76 + (47285326269596741861/3745000000000000000000000000000000 : ℝ)*base78 + (39144614109176741861/3745000000000000000000000000000000 : ℝ)*base80 + (6463722721413/2340625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13027/5000000000000000000 : ℝ)*base90 + (13027/5000000000000000000 : ℝ)*base92 + (13027/5000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6057626865695916027133706307/936250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1144055993/100000000000000 : ℝ)*(base19) + (155357371/12500000000000 : ℝ)*(base23) + (64708491/50000000000000 : ℝ)*(upper3) + (12104101/25000000000000 : ℝ)*(lower4) + (66444833/50000000000000 : ℝ)*(upper5) + (2174392602145357/50000000000000 : ℝ)*(major0) + (2174392602145357/50000000000000 : ℝ)*(major1) + (2174392602145357/50000000000000 : ℝ)*(major2) + (2285190907/10000000000000 : ℝ)*(sp1) + (24558659/100000000000 : ℝ)*(sp2) + (5863914946161107/100000000000000 : ℝ)*(sp4) + (1465972737549011/25000000000000 : ℝ)*(sp5) + (2931944572321569/50000000000000 : ℝ)*(sp6) + (1416827623375231/50000000000000 : ℝ)*(sp7) + (1416827623375231/50000000000000 : ℝ)*(f.failure) + (5863914946161107/100000000000000 : ℝ)*(f.sum) + (31471481302357/18725000000000000000000000000 : ℝ)*base66 + (10365727902790781231/1872500000000000000000000000000000 : ℝ)*base67 + (7902294295684218769/1872500000000000000000000000000000 : ℝ)*base70 + (14823587195985781231/1872500000000000000000000000000000 : ℝ)*base71 + (21824132554417/4681250000000000000000000000 : ℝ)*base73 + (12648981586974218769/1872500000000000000000000000000000 : ℝ)*base76 + (14012339318965781231/1872500000000000000000000000000000 : ℝ)*base77 + (38257048028935781231/1872500000000000000000000000000000 : ℝ)*base79 + (15155293752859/9362500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (361379/50000000000000000000 : ℝ)*base90 + (361379/50000000000000000000 : ℝ)*base92 + (361379/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1310_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1310_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1310_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1310_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1310_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1310_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4269/1024 : ℝ) ≤ p) (hpb : p ≤ (2135/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1534691/1000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4817/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11061/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1310_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

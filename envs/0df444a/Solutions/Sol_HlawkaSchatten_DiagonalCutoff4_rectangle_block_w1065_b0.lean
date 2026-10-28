-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:06:20.520367+00:00
-- url     : https://prove2.me/submissions/00319fec-1be2-485d-8963-42fd7c768898

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
theorem support_rectangle_w1065_s0_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1916421847/10000000000 : ℝ)*x 0 + (6072299149/10000000000 : ℝ)*x 1 + (4770657089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916421847/10000000000 : ℝ)^4129 ≤ (5556910319281/50000000000000 : ℝ)^3105 := by
    have hnat : (1916421847 : ℕ)^4129*50000000000000^3105 ≤ 5556910319281^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916421847 10000000000 5556910319281 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6072299149/10000000000 : ℝ)^4129 ≤ (51511601686259/100000000000000 : ℝ)^3105 := by
    have hnat : (6072299149 : ℕ)^4129*100000000000000^3105 ≤ 51511601686259^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6072299149 10000000000 51511601686259 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770657089/10000000000 : ℝ)^4129 ≤ (3737457764899/10000000000000 : ℝ)^3105 := by
    have hnat : (4770657089 : ℕ)^4129*10000000000000^3105 ≤ 3737457764899^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770657089 10000000000 3737457764899 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1916421847/10000000000 : ℝ), (6072299149/10000000000 : ℝ), (4770657089/10000000000 : ℝ)] ![(5556910319281/50000000000000 : ℝ), (51511601686259/100000000000000 : ℝ), (3737457764899/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1916421847/10000000000 : ℝ)|^4129 ≤ (5556910319281/50000000000000 : ℝ)^3105
        have hw : |(-1916421847/10000000000 : ℝ)|=(1916421847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6072299149/10000000000 : ℝ)|^4129 ≤ (51511601686259/100000000000000 : ℝ)^3105
        have hw : |(6072299149/10000000000 : ℝ)|=(6072299149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770657089/10000000000 : ℝ)|^4129 ≤ (3737457764899/10000000000000 : ℝ)^3105
        have hw : |(4770657089/10000000000 : ℝ)|=(4770657089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5521131011/10000000000 : ℝ)*x 0 + (-2665683623/10000000000 : ℝ)*x 1 + (4770655723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521131011/10000000000 : ℝ)^4129 ≤ (45389073078199/100000000000000 : ℝ)^3105 := by
    have hnat : (5521131011 : ℕ)^4129*100000000000000^3105 ≤ 45389073078199^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521131011 10000000000 45389073078199 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2665683623/10000000000 : ℝ)^4129 ≤ (8618181745979/50000000000000 : ℝ)^3105 := by
    have hnat : (2665683623 : ℕ)^4129*50000000000000^3105 ≤ 8618181745979^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665683623 10000000000 8618181745979 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4770655723/10000000000 : ℝ)^4129 ≤ (37374563418101/100000000000000 : ℝ)^3105 := by
    have hnat : (4770655723 : ℕ)^4129*100000000000000^3105 ≤ 37374563418101^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770655723 10000000000 37374563418101 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521131011/10000000000 : ℝ), (-2665683623/10000000000 : ℝ), (4770655723/10000000000 : ℝ)] ![(45389073078199/100000000000000 : ℝ), (8618181745979/50000000000000 : ℝ), (37374563418101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521131011/10000000000 : ℝ)|^4129 ≤ (45389073078199/100000000000000 : ℝ)^3105
        have hw : |(5521131011/10000000000 : ℝ)|=(5521131011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2665683623/10000000000 : ℝ)|^4129 ≤ (8618181745979/50000000000000 : ℝ)^3105
        have hw : |(-2665683623/10000000000 : ℝ)|=(2665683623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4770655723/10000000000 : ℝ)|^4129 ≤ (37374563418101/100000000000000 : ℝ)^3105
        have hw : |(4770655723/10000000000 : ℝ)|=(4770655723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5521129073/10000000000 : ℝ)*x 0 + (4770656881/10000000000 : ℝ)*x 1 + (-1332842341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5521129073/10000000000 : ℝ)^4129 ≤ (45389051891647/100000000000000 : ℝ)^3105 := by
    have hnat : (5521129073 : ℕ)^4129*100000000000000^3105 ≤ 45389051891647^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521129073 10000000000 45389051891647 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4770656881/10000000000 : ℝ)^4129 ≤ (37374575482061/100000000000000 : ℝ)^3105 := by
    have hnat : (4770656881 : ℕ)^4129*100000000000000^3105 ≤ 37374575482061^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4770656881 10000000000 37374575482061 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1332842341/5000000000 : ℝ)^4129 ≤ (17236372597721/100000000000000 : ℝ)^3105 := by
    have hnat : (1332842341 : ℕ)^4129*100000000000000^3105 ≤ 17236372597721^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332842341 5000000000 17236372597721 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5521129073/10000000000 : ℝ), (4770656881/10000000000 : ℝ), (-1332842341/5000000000 : ℝ)] ![(45389051891647/100000000000000 : ℝ), (37374575482061/100000000000000 : ℝ), (17236372597721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5521129073/10000000000 : ℝ)|^4129 ≤ (45389051891647/100000000000000 : ℝ)^3105
        have hw : |(5521129073/10000000000 : ℝ)|=(5521129073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4770656881/10000000000 : ℝ)|^4129 ≤ (37374575482061/100000000000000 : ℝ)^3105
        have hw : |(4770656881/10000000000 : ℝ)|=(4770656881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1332842341/5000000000 : ℝ)|^4129 ≤ (17236372597721/100000000000000 : ℝ)^3105
        have hw : |(-1332842341/5000000000 : ℝ)|=(1332842341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2103645963/5000000000 : ℝ)*x 0 + (3124921691/10000000000 : ℝ)*x 1 + (2837723893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103645963/5000000000 : ℝ)^4129 ≤ (15811469546261/50000000000000 : ℝ)^3105 := by
    have hnat : (2103645963 : ℕ)^4129*50000000000000^3105 ≤ 15811469546261^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103645963 5000000000 15811469546261 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3124921691/10000000000 : ℝ)^4129 ≤ (4258648544009/20000000000000 : ℝ)^3105 := by
    have hnat : (3124921691 : ℕ)^4129*20000000000000^3105 ≤ 4258648544009^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124921691 10000000000 4258648544009 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837723893/5000000000 : ℝ)^4129 ≤ (23541909082863/50000000000000 : ℝ)^3105 := by
    have hnat : (2837723893 : ℕ)^4129*50000000000000^3105 ≤ 23541909082863^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837723893 5000000000 23541909082863 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103645963/5000000000 : ℝ), (3124921691/10000000000 : ℝ), (2837723893/5000000000 : ℝ)] ![(15811469546261/50000000000000 : ℝ), (4258648544009/20000000000000 : ℝ), (23541909082863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103645963/5000000000 : ℝ)|^4129 ≤ (15811469546261/50000000000000 : ℝ)^3105
        have hw : |(2103645963/5000000000 : ℝ)|=(2103645963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3124921691/10000000000 : ℝ)|^4129 ≤ (4258648544009/20000000000000 : ℝ)^3105
        have hw : |(3124921691/10000000000 : ℝ)|=(3124921691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2837723893/5000000000 : ℝ)|^4129 ≤ (23541909082863/50000000000000 : ℝ)^3105
        have hw : |(2837723893/5000000000 : ℝ)|=(2837723893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-960899289/5000000000 : ℝ)*x 0 + (4804266761/10000000000 : ℝ)*x 1 + (6037513663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (960899289/5000000000 : ℝ)^4129 ≤ (5577652031701/50000000000000 : ℝ)^3105 := by
    have hnat : (960899289 : ℕ)^4129*50000000000000^3105 ≤ 5577652031701^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960899289 5000000000 5577652031701 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4804266761/10000000000 : ℝ)^4129 ≤ (18862563465519/50000000000000 : ℝ)^3105 := by
    have hnat : (4804266761 : ℕ)^4129*50000000000000^3105 ≤ 18862563465519^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4804266761 10000000000 18862563465519 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6037513663/10000000000 : ℝ)^4129 ≤ (12779892247681/25000000000000 : ℝ)^3105 := by
    have hnat : (6037513663 : ℕ)^4129*25000000000000^3105 ≤ 12779892247681^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6037513663 10000000000 12779892247681 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-960899289/5000000000 : ℝ), (4804266761/10000000000 : ℝ), (6037513663/10000000000 : ℝ)] ![(5577652031701/50000000000000 : ℝ), (18862563465519/50000000000000 : ℝ), (12779892247681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-960899289/5000000000 : ℝ)|^4129 ≤ (5577652031701/50000000000000 : ℝ)^3105
        have hw : |(-960899289/5000000000 : ℝ)|=(960899289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4804266761/10000000000 : ℝ)|^4129 ≤ (18862563465519/50000000000000 : ℝ)^3105
        have hw : |(4804266761/10000000000 : ℝ)|=(4804266761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6037513663/10000000000 : ℝ)|^4129 ≤ (12779892247681/25000000000000 : ℝ)^3105
        have hw : |(6037513663/10000000000 : ℝ)|=(6037513663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5167848661/10000000000 : ℝ)*x 0 + (-1398831181/10000000000 : ℝ)*x 1 + (6037511567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167848661/10000000000 : ℝ)^4129 ≤ (10392069463521/25000000000000 : ℝ)^3105 := by
    have hnat : (5167848661 : ℕ)^4129*25000000000000^3105 ≤ 10392069463521^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167848661 10000000000 10392069463521 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398831181/10000000000 : ℝ)^4129 ≤ (7312176744203/100000000000000 : ℝ)^3105 := by
    have hnat : (1398831181 : ℕ)^4129*100000000000000^3105 ≤ 7312176744203^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398831181 10000000000 7312176744203 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6037511567/10000000000 : ℝ)^4129 ≤ (51119545391181/100000000000000 : ℝ)^3105 := by
    have hnat : (6037511567 : ℕ)^4129*100000000000000^3105 ≤ 51119545391181^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6037511567 10000000000 51119545391181 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167848661/10000000000 : ℝ), (-1398831181/10000000000 : ℝ), (6037511567/10000000000 : ℝ)] ![(10392069463521/25000000000000 : ℝ), (7312176744203/100000000000000 : ℝ), (51119545391181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167848661/10000000000 : ℝ)|^4129 ≤ (10392069463521/25000000000000 : ℝ)^3105
        have hw : |(5167848661/10000000000 : ℝ)|=(5167848661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1398831181/10000000000 : ℝ)|^4129 ≤ (7312176744203/100000000000000 : ℝ)^3105
        have hw : |(-1398831181/10000000000 : ℝ)|=(1398831181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6037511567/10000000000 : ℝ)|^4129 ≤ (51119545391181/100000000000000 : ℝ)^3105
        have hw : |(6037511567/10000000000 : ℝ)|=(6037511567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516784893/1000000000 : ℝ)*x 0 + (3018756311/5000000000 : ℝ)*x 1 + (-1398829059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516784893/1000000000 : ℝ)^4129 ≤ (41568280731401/100000000000000 : ℝ)^3105 := by
    have hnat : (516784893 : ℕ)^4129*100000000000000^3105 ≤ 41568280731401^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516784893 1000000000 41568280731401 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3018756311/5000000000 : ℝ)^4129 ≤ (51119557269767/100000000000000 : ℝ)^3105 := by
    have hnat : (3018756311 : ℕ)^4129*100000000000000^3105 ≤ 51119557269767^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3018756311 5000000000 51119557269767 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1398829059/10000000000 : ℝ)^4129 ≤ (3656080996797/50000000000000 : ℝ)^3105 := by
    have hnat : (1398829059 : ℕ)^4129*50000000000000^3105 ≤ 3656080996797^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398829059 10000000000 3656080996797 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516784893/1000000000 : ℝ), (3018756311/5000000000 : ℝ), (-1398829059/10000000000 : ℝ)] ![(41568280731401/100000000000000 : ℝ), (51119557269767/100000000000000 : ℝ), (3656080996797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516784893/1000000000 : ℝ)|^4129 ≤ (41568280731401/100000000000000 : ℝ)^3105
        have hw : |(516784893/1000000000 : ℝ)|=(516784893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3018756311/5000000000 : ℝ)|^4129 ≤ (51119557269767/100000000000000 : ℝ)^3105
        have hw : |(3018756311/5000000000 : ℝ)|=(3018756311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1398829059/10000000000 : ℝ)|^4129 ≤ (3656080996797/50000000000000 : ℝ)^3105
        have hw : |(-1398829059/10000000000 : ℝ)|=(1398829059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s0_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2108913069/5000000000 : ℝ)*x 0 + (350599341/625000000 : ℝ)*x 1 + (3193081797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108913069/5000000000 : ℝ)^4129 ≤ (15864136001567/50000000000000 : ℝ)^3105 := by
    have hnat : (2108913069 : ℕ)^4129*50000000000000^3105 ≤ 15864136001567^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108913069 5000000000 15864136001567 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350599341/625000000 : ℝ)^4129 ≤ (46358661966043/100000000000000 : ℝ)^3105 := by
    have hnat : (350599341 : ℕ)^4129*100000000000000^3105 ≤ 46358661966043^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350599341 625000000 46358661966043 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193081797/10000000000 : ℝ)^4129 ≤ (5478266503339/25000000000000 : ℝ)^3105 := by
    have hnat : (3193081797 : ℕ)^4129*25000000000000^3105 ≤ 5478266503339^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193081797 10000000000 5478266503339 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108913069/5000000000 : ℝ), (350599341/625000000 : ℝ), (3193081797/10000000000 : ℝ)] ![(15864136001567/50000000000000 : ℝ), (46358661966043/100000000000000 : ℝ), (5478266503339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108913069/5000000000 : ℝ)|^4129 ≤ (15864136001567/50000000000000 : ℝ)^3105
        have hw : |(2108913069/5000000000 : ℝ)|=(2108913069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350599341/625000000 : ℝ)|^4129 ≤ (46358661966043/100000000000000 : ℝ)^3105
        have hw : |(350599341/625000000 : ℝ)|=(350599341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193081797/10000000000 : ℝ)|^4129 ≤ (5478266503339/25000000000000 : ℝ)^3105
        have hw : |(3193081797/10000000000 : ℝ)|=(3193081797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (23/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28113/100000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8257/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8257 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8257*1^2048 ≤ 0^2048*1^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8257/2048 : ℝ) ≤ (62165587462012121/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8257 ≤ (62165587462012121/2500000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8257*2500000000000000000^2048 ≤ 62165587462012121^2048*5^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 62165587462012121 2500000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (62165587462012121/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8257 := by
      have hnat : (1 : ℕ)^2048*1^8257 ≤ 1^8257*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2562165587462012121/2500000000000000000 : ℝ) ≤ (2012221563267051/2000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (2562165587462012121/2500000000000000000 : ℝ)^2048 ≤ (2012221563267051/2000000000000000 : ℝ)^8257 := by
      have hnat : (2562165587462012121 : ℕ)^2048*2000000000000000^8257 ≤ 2012221563267051^8257*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2562165587462012121 2500000000000000000 2012221563267051 2000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012221563267051/2000000000000000 : ℝ)) (X := (2562165587462012121/2500000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1312165587462012121/1250000000000000000 : ℝ) ≤ (1012221563267051/1000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (1312165587462012121/1250000000000000000 : ℝ)^2048 ≤ (1012221563267051/1000000000000000 : ℝ)^8257 := by
      have hnat : (1312165587462012121 : ℕ)^2048*1000000000000000^8257 ≤ 1012221563267051^8257*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1312165587462012121 1250000000000000000 1012221563267051 1000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012221563267051/1000000000000000 : ℝ)) (X := (1312165587462012121/1250000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12221563267051/800000000000000 : ℝ)*(0 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12221563267051/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(62165587462012121/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12221563267051/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (1 : ℝ)+(12221563267051/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012221563267051/2000000000000000 : ℝ) by norm_num, show 1+(62165587462012121/2500000000000000000 : ℝ)+(0 : ℝ)=(2562165587462012121/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(62165587462012121/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12221563267051/800000000000000 : ℝ)*(2/5 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12221563267051/800000000000000 : ℝ)*(2/5 : ℝ)=(1012221563267051/1000000000000000 : ℝ) by norm_num, show 1+2*(62165587462012121/2500000000000000000 : ℝ)=(1312165587462012121/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12221563267051/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12221563267051/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12221563267051/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12221563267051/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12221563267051/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12221563267051/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1916421847/10000000000 : ℝ)*X 0 0+(6072299149/10000000000 : ℝ)*X 0 1+(4770657089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5521131011/10000000000 : ℝ)*X 1 0+(-2665683623/10000000000 : ℝ)*X 1 1+(4770655723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5521129073/10000000000 : ℝ)*X 2 0+(4770656881/10000000000 : ℝ)*X 2 1+(-1332842341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2103645963/5000000000 : ℝ)*X 0 0+(3124921691/10000000000 : ℝ)*X 0 1+(2837723893/5000000000 : ℝ)*X 0 2+(2103645963/5000000000 : ℝ)*X 1 0+(3124921691/10000000000 : ℝ)*X 1 1+(2837723893/5000000000 : ℝ)*X 1 2+(2103645963/5000000000 : ℝ)*X 2 0+(3124921691/10000000000 : ℝ)*X 2 1+(2837723893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-960899289/5000000000 : ℝ)*X 0 0+(4804266761/10000000000 : ℝ)*X 0 1+(6037513663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5167848661/10000000000 : ℝ)*X 1 0+(-1398831181/10000000000 : ℝ)*X 1 1+(6037511567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((516784893/1000000000 : ℝ)*X 2 0+(3018756311/5000000000 : ℝ)*X 2 1+(-1398829059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2108913069/5000000000 : ℝ)*X 0 0+(350599341/625000000 : ℝ)*X 0 1+(3193081797/10000000000 : ℝ)*X 0 2+(2108913069/5000000000 : ℝ)*X 1 0+(350599341/625000000 : ℝ)*X 1 1+(3193081797/10000000000 : ℝ)*X 1 2+(2108913069/5000000000 : ℝ)*X 2 0+(350599341/625000000 : ℝ)*X 2 1+(3193081797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3273531147842824756347/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47903629/50000000000000 : ℝ)*(base1) + (18415789/100000000000000 : ℝ)*(base16) + (42726281/2500000000000 : ℝ)*(base19) + (728896761/50000000000000 : ℝ)*(base23) + (35098033/12500000000000 : ℝ)*(upper3) + (36260912382001/6250000000000 : ℝ)*(major0) + (36260912382001/6250000000000 : ℝ)*(major1) + (36260912382001/6250000000000 : ℝ)*(major2) + (38413282608797/5000000000000 : ℝ)*(sp0) + (384133704314087/50000000000000 : ℝ)*(sp1) + (768267678301681/100000000000000 : ℝ)*(sp2) + (9801937868083/2500000000000 : ℝ)*(sp3) + (1789863261/50000000000000 : ℝ)*(sp4) + (446272567/20000000000000 : ℝ)*(sp7) + (196039920946707/50000000000000 : ℝ)*(f.failure) + (768269136095203/100000000000000 : ℝ)*(f.sum) + (5518967114051/2500000000000000000000000000 : ℝ)*base65 + (963972160949/5000000000000000000000000000 : ℝ)*base68 + (4939624944051/5000000000000000000000000000 : ℝ)*base69 + (20078091429051/5000000000000000000000000000 : ℝ)*base71 + (8376070054051/2500000000000000000000000000 : ℝ)*base73 + (29652469664051/5000000000000000000000000000 : ℝ)*base75 + (11107252434051/5000000000000000000000000000 : ℝ)*base77 + (22628494544051/5000000000000000000000000000 : ℝ)*base79 + (5648004816551/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5746919/1000000000000000000000 : ℝ)*base89 + (5746919/1000000000000000000000 : ℝ)*base91 + (5746919/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (209810934602525744603529/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282916523/25000000000000 : ℝ)*(base19) + (1257073537/100000000000000 : ℝ)*(base23) + (170559/781250000000 : ℝ)*(base39) + (9701873/6250000000000 : ℝ)*(base45) + (123233641/100000000000000 : ℝ)*(upper3) + (261507407/100000000000000 : ℝ)*(upper5) + (61234341899859/10000000000000 : ℝ)*(major0) + (61234341899859/10000000000000 : ℝ)*(major1) + (612343397167037/100000000000000 : ℝ)*(major2) + (11339329/1250000000000 : ℝ)*(sp2) + (101358403696123/12500000000000 : ℝ)*(sp4) + (202716524475723/25000000000000 : ℝ)*(sp5) + (810865087180679/100000000000000 : ℝ)*(sp6) + (25863713234637/6250000000000 : ℝ)*(sp7) + (25863713234637/6250000000000 : ℝ)*(f.failure) + (101358406425067/12500000000000 : ℝ)*(f.sum) + (72193588335977/80000000000000000000000000000 : ℝ)*base65 + (273196455317887/80000000000000000000000000000 : ℝ)*base67 + (8180944917809/8000000000000000000000000000 : ℝ)*base69 + (218463836757887/80000000000000000000000000000 : ℝ)*base71 + (41627080144023/80000000000000000000000000000 : ℝ)*base74 + (37047157941809/8000000000000000000000000000 : ℝ)*base75 + (39078673637809/8000000000000000000000000000 : ℝ)*base77 + (99931453765809/8000000000000000000000000000 : ℝ)*base79 + (12344629353809/4000000000000000000000000000 : ℝ)*base81 + (887271/125000000000000000000 : ℝ)*base90 + (887271/125000000000000000000 : ℝ)*base92 + (362729/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (23/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_s1_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-425325419/2000000000 : ℝ)*x 0 + (1144520263/2000000000 : ℝ)*x 1 + (623217141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425325419/2000000000 : ℝ)^4129 ≤ (2552702611043/20000000000000 : ℝ)^3105 := by
    have hnat : (425325419 : ℕ)^4129*20000000000000^3105 ≤ 2552702611043^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425325419 2000000000 2552702611043 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144520263/2000000000 : ℝ)^4129 ≤ (47604727932829/100000000000000 : ℝ)^3105 := by
    have hnat : (1144520263 : ℕ)^4129*100000000000000^3105 ≤ 47604727932829^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144520263 2000000000 47604727932829 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623217141/1250000000 : ℝ)^4129 ≤ (39631758994247/100000000000000 : ℝ)^3105 := by
    have hnat : (623217141 : ℕ)^4129*100000000000000^3105 ≤ 39631758994247^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623217141 1250000000 39631758994247 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425325419/2000000000 : ℝ), (1144520263/2000000000 : ℝ), (623217141/1250000000 : ℝ)] ![(2552702611043/20000000000000 : ℝ), (47604727932829/100000000000000 : ℝ), (39631758994247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425325419/2000000000 : ℝ)|^4129 ≤ (2552702611043/20000000000000 : ℝ)^3105
        have hw : |(-425325419/2000000000 : ℝ)|=(425325419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144520263/2000000000 : ℝ)|^4129 ≤ (47604727932829/100000000000000 : ℝ)^3105
        have hw : |(1144520263/2000000000 : ℝ)|=(1144520263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(623217141/1250000000 : ℝ)|^4129 ≤ (39631758994247/100000000000000 : ℝ)^3105
        have hw : |(623217141/1250000000 : ℝ)|=(623217141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084673431/2000000000 : ℝ)*x 0 + (-2525881659/10000000000 : ℝ)*x 1 + (4985737447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084673431/2000000000 : ℝ)^4129 ≤ (44323434659069/100000000000000 : ℝ)^3105 := by
    have hnat : (1084673431 : ℕ)^4129*100000000000000^3105 ≤ 44323434659069^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084673431 2000000000 44323434659069 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2525881659/10000000000 : ℝ)^4129 ≤ (16044802955471/100000000000000 : ℝ)^3105 := by
    have hnat : (2525881659 : ℕ)^4129*100000000000000^3105 ≤ 16044802955471^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525881659 10000000000 16044802955471 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4985737447/10000000000 : ℝ)^4129 ≤ (31705409893/80000000000 : ℝ)^3105 := by
    have hnat : (4985737447 : ℕ)^4129*80000000000^3105 ≤ 31705409893^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985737447 10000000000 31705409893 80000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084673431/2000000000 : ℝ), (-2525881659/10000000000 : ℝ), (4985737447/10000000000 : ℝ)] ![(44323434659069/100000000000000 : ℝ), (16044802955471/100000000000000 : ℝ), (31705409893/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084673431/2000000000 : ℝ)|^4129 ≤ (44323434659069/100000000000000 : ℝ)^3105
        have hw : |(1084673431/2000000000 : ℝ)|=(1084673431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2525881659/10000000000 : ℝ)|^4129 ≤ (16044802955471/100000000000000 : ℝ)^3105
        have hw : |(-2525881659/10000000000 : ℝ)|=(2525881659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4985737447/10000000000 : ℝ)|^4129 ≤ (31705409893/80000000000 : ℝ)^3105
        have hw : |(4985737447/10000000000 : ℝ)|=(4985737447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5423367721/10000000000 : ℝ)*x 0 + (4985736803/10000000000 : ℝ)*x 1 + (-1262940869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5423367721/10000000000 : ℝ)^4129 ≤ (44323440810329/100000000000000 : ℝ)^3105 := by
    have hnat : (5423367721 : ℕ)^4129*100000000000000^3105 ≤ 44323440810329^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423367721 10000000000 44323440810329 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4985736803/10000000000 : ℝ)^4129 ≤ (39631755558821/100000000000000 : ℝ)^3105 := by
    have hnat : (4985736803 : ℕ)^4129*100000000000000^3105 ≤ 39631755558821^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985736803 10000000000 39631755558821 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262940869/5000000000 : ℝ)^4129 ≤ (4011200905697/25000000000000 : ℝ)^3105 := by
    have hnat : (1262940869 : ℕ)^4129*25000000000000^3105 ≤ 4011200905697^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262940869 5000000000 4011200905697 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5423367721/10000000000 : ℝ), (4985736803/10000000000 : ℝ), (-1262940869/5000000000 : ℝ)] ![(44323440810329/100000000000000 : ℝ), (39631755558821/100000000000000 : ℝ), (4011200905697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5423367721/10000000000 : ℝ)|^4129 ≤ (44323440810329/100000000000000 : ℝ)^3105
        have hw : |(5423367721/10000000000 : ℝ)|=(5423367721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4985736803/10000000000 : ℝ)|^4129 ≤ (39631755558821/100000000000000 : ℝ)^3105
        have hw : |(4985736803/10000000000 : ℝ)|=(4985736803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1262940869/5000000000 : ℝ)|^4129 ≤ (4011200905697/25000000000000 : ℝ)^3105
        have hw : |(-1262940869/5000000000 : ℝ)|=(1262940869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161942573/5000000000 : ℝ)*x 0 + (366234907/1000000000 : ℝ)*x 1 + (5106212203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161942573/5000000000 : ℝ)^4129 ≤ (4099197637273/12500000000000 : ℝ)^3105 := by
    have hnat : (2161942573 : ℕ)^4129*12500000000000^3105 ≤ 4099197637273^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161942573 5000000000 4099197637273 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366234907/1000000000 : ℝ)^4129 ≤ (26296125949383/100000000000000 : ℝ)^3105 := by
    have hnat : (366234907 : ℕ)^4129*100000000000000^3105 ≤ 26296125949383^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366234907 1000000000 26296125949383 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5106212203/10000000000 : ℝ)^4129 ≤ (40910292932639/100000000000000 : ℝ)^3105 := by
    have hnat : (5106212203 : ℕ)^4129*100000000000000^3105 ≤ 40910292932639^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106212203 10000000000 40910292932639 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161942573/5000000000 : ℝ), (366234907/1000000000 : ℝ), (5106212203/10000000000 : ℝ)] ![(4099197637273/12500000000000 : ℝ), (26296125949383/100000000000000 : ℝ), (40910292932639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161942573/5000000000 : ℝ)|^4129 ≤ (4099197637273/12500000000000 : ℝ)^3105
        have hw : |(2161942573/5000000000 : ℝ)|=(2161942573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(366234907/1000000000 : ℝ)|^4129 ≤ (26296125949383/100000000000000 : ℝ)^3105
        have hw : |(366234907/1000000000 : ℝ)|=(366234907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5106212203/10000000000 : ℝ)|^4129 ≤ (40910292932639/100000000000000 : ℝ)^3105
        have hw : |(5106212203/10000000000 : ℝ)|=(5106212203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127550789/10000000000 : ℝ)*x 0 + (2498048257/5000000000 : ℝ)*x 1 + (5712029231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127550789/10000000000 : ℝ)^4129 ≤ (2554177133467/20000000000000 : ℝ)^3105 := by
    have hnat : (2127550789 : ℕ)^4129*20000000000000^3105 ≤ 2554177133467^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127550789 10000000000 2554177133467 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498048257/5000000000 : ℝ)^4129 ≤ (9935325204621/25000000000000 : ℝ)^3105 := by
    have hnat : (2498048257 : ℕ)^4129*25000000000000^3105 ≤ 9935325204621^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498048257 5000000000 9935325204621 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5712029231/10000000000 : ℝ)^4129 ≤ (47487813505743/100000000000000 : ℝ)^3105 := by
    have hnat : (5712029231 : ℕ)^4129*100000000000000^3105 ≤ 47487813505743^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712029231 10000000000 47487813505743 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127550789/10000000000 : ℝ), (2498048257/5000000000 : ℝ), (5712029231/10000000000 : ℝ)] ![(2554177133467/20000000000000 : ℝ), (9935325204621/25000000000000 : ℝ), (47487813505743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127550789/10000000000 : ℝ)|^4129 ≤ (2554177133467/20000000000000 : ℝ)^3105
        have hw : |(-2127550789/10000000000 : ℝ)|=(2127550789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498048257/5000000000 : ℝ)|^4129 ≤ (9935325204621/25000000000000 : ℝ)^3105
        have hw : |(2498048257/5000000000 : ℝ)|=(2498048257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5712029231/10000000000 : ℝ)|^4129 ≤ (47487813505743/100000000000000 : ℝ)^3105
        have hw : |(5712029231/10000000000 : ℝ)|=(5712029231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047038681/2000000000 : ℝ)*x 0 + (-899793849/5000000000 : ℝ)*x 1 + (1428007731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047038681/2000000000 : ℝ)^4129 ≤ (21145082042213/50000000000000 : ℝ)^3105 := by
    have hnat : (1047038681 : ℕ)^4129*50000000000000^3105 ≤ 21145082042213^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047038681 2000000000 21145082042213 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899793849/5000000000 : ℝ)^4129 ≤ (2044400734941/20000000000000 : ℝ)^3105 := by
    have hnat : (899793849 : ℕ)^4129*20000000000000^3105 ≤ 2044400734941^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899793849 5000000000 2044400734941 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1428007731/2500000000 : ℝ)^4129 ≤ (47487832222561/100000000000000 : ℝ)^3105 := by
    have hnat : (1428007731 : ℕ)^4129*100000000000000^3105 ≤ 47487832222561^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1428007731 2500000000 47487832222561 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047038681/2000000000 : ℝ), (-899793849/5000000000 : ℝ), (1428007731/2500000000 : ℝ)] ![(21145082042213/50000000000000 : ℝ), (2044400734941/20000000000000 : ℝ), (47487832222561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047038681/2000000000 : ℝ)|^4129 ≤ (21145082042213/50000000000000 : ℝ)^3105
        have hw : |(1047038681/2000000000 : ℝ)|=(1047038681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-899793849/5000000000 : ℝ)|^4129 ≤ (2044400734941/20000000000000 : ℝ)^3105
        have hw : |(-899793849/5000000000 : ℝ)|=(899793849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1428007731/2500000000 : ℝ)|^4129 ≤ (47487832222561/100000000000000 : ℝ)^3105
        have hw : |(1428007731/2500000000 : ℝ)|=(1428007731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5235191377/10000000000 : ℝ)*x 0 + (5712033163/10000000000 : ℝ)*x 1 + (-899793653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5235191377/10000000000 : ℝ)^4129 ≤ (10572535574853/25000000000000 : ℝ)^3105 := by
    have hnat : (5235191377 : ℕ)^4129*25000000000000^3105 ≤ 10572535574853^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5235191377 10000000000 10572535574853 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5712033163/10000000000 : ℝ)^4129 ≤ (23743928487819/50000000000000 : ℝ)^3105 := by
    have hnat : (5712033163 : ℕ)^4129*50000000000000^3105 ≤ 23743928487819^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5712033163 10000000000 23743928487819 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899793653/5000000000 : ℝ)^4129 ≤ (10222000713747/100000000000000 : ℝ)^3105 := by
    have hnat : (899793653 : ℕ)^4129*100000000000000^3105 ≤ 10222000713747^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899793653 5000000000 10222000713747 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5235191377/10000000000 : ℝ), (5712033163/10000000000 : ℝ), (-899793653/5000000000 : ℝ)] ![(10572535574853/25000000000000 : ℝ), (23743928487819/50000000000000 : ℝ), (10222000713747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5235191377/10000000000 : ℝ)|^4129 ≤ (10572535574853/25000000000000 : ℝ)^3105
        have hw : |(5235191377/10000000000 : ℝ)|=(5235191377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5712033163/10000000000 : ℝ)|^4129 ≤ (23743928487819/50000000000000 : ℝ)^3105
        have hw : |(5712033163/10000000000 : ℝ)|=(5712033163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899793653/5000000000 : ℝ)|^4129 ≤ (10222000713747/100000000000000 : ℝ)^3105
        have hw : |(-899793653/5000000000 : ℝ)|=(899793653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s1_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4325691141/10000000000 : ℝ)*x 0 + (2542954919/5000000000 : ℝ)*x 1 + (3683061309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325691141/10000000000 : ℝ)^4129 ≤ (3281179673777/10000000000000 : ℝ)^3105 := by
    have hnat : (4325691141 : ℕ)^4129*10000000000000^3105 ≤ 3281179673777^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325691141 10000000000 3281179673777 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542954919/5000000000 : ℝ)^4129 ≤ (40694131326737/100000000000000 : ℝ)^3105 := by
    have hnat : (2542954919 : ℕ)^4129*100000000000000^3105 ≤ 40694131326737^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542954919 5000000000 40694131326737 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3683061309/10000000000 : ℝ)^4129 ≤ (13247035960603/50000000000000 : ℝ)^3105 := by
    have hnat : (3683061309 : ℕ)^4129*50000000000000^3105 ≤ 13247035960603^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3683061309 10000000000 13247035960603 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325691141/10000000000 : ℝ), (2542954919/5000000000 : ℝ), (3683061309/10000000000 : ℝ)] ![(3281179673777/10000000000000 : ℝ), (40694131326737/100000000000000 : ℝ), (13247035960603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325691141/10000000000 : ℝ)|^4129 ≤ (3281179673777/10000000000000 : ℝ)^3105
        have hw : |(4325691141/10000000000 : ℝ)|=(4325691141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542954919/5000000000 : ℝ)|^4129 ≤ (40694131326737/100000000000000 : ℝ)^3105
        have hw : |(2542954919/5000000000 : ℝ)|=(2542954919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3683061309/10000000000 : ℝ)|^4129 ≤ (13247035960603/50000000000000 : ℝ)^3105
        have hw : |(3683061309/10000000000 : ℝ)|=(3683061309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5199/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (23/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (23/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (23/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (23/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (23/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (23/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (23/25000 : ℝ) ^ (8257/2048 : ℝ) ≤ (14345879/25000000000000000000 : ℝ) := by
    have hpowers : (23/25000 : ℝ)^8257 ≤ (14345879/25000000000000000000 : ℝ)^2048 := by
      have hnat : (23 : ℕ)^8257*25000000000000000000^2048 ≤ 14345879^2048*25000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23 25000 14345879 25000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23/25000 : ℝ)) (X := (14345879/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28113/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (4799853905910459/800000000000000000 : ℝ) := by
    have hpowers : (28113/100000 : ℝ)^8257 ≤ (4799853905910459/800000000000000000 : ℝ)^2048 := by
      have hnat : (28113 : ℕ)^8257*800000000000000000^2048 ≤ 4799853905910459^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28113 100000 4799853905910459 800000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28113/100000 : ℝ)) (X := (4799853905910459/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000000014345879/12500000000000000000 : ℝ) ≤ (10000000000002847/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (12500000000014345879/12500000000000000000 : ℝ)^2048 ≤ (10000000000002847/10000000000000000 : ℝ)^8257 := by
      have hnat : (12500000000014345879 : ℕ)^2048*10000000000000000^8257 ≤ 10000000000002847^8257*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000000014345879 12500000000000000000 10000000000002847 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000002847/10000000000000000 : ℝ)) (X := (12500000000014345879/12500000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100599981738296190891/100000000000000000000 : ℝ) ≤ (2503712003106879/2500000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (100599981738296190891/100000000000000000000 : ℝ)^2048 ≤ (2503712003106879/2500000000000000 : ℝ)^8257 := by
      have hnat : (100599981738296190891 : ℕ)^2048*2500000000000000^8257 ≤ 2503712003106879^8257*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100599981738296190891 100000000000000000000 2503712003106879 2500000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503712003106879/2500000000000000 : ℝ)) (X := (100599981738296190891/100000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (404799853905910459/400000000000000000 : ℝ) ≤ (2005939204970437/2000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (404799853905910459/400000000000000000 : ℝ)^2048 ≤ (2005939204970437/2000000000000000 : ℝ)^8257 := by
      have hnat : (404799853905910459 : ℕ)^2048*2000000000000000^8257 ≤ 2005939204970437^8257*400000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        404799853905910459 400000000000000000 2005939204970437 2000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005939204970437/2000000000000000 : ℝ)) (X := (404799853905910459/400000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14345879/25000000000000000000 : ℝ) ≤ ((280207267965793636691/280210000000000000000 : ℝ)+2*(14848012424669/2802100000000000 : ℝ)*(23/25000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (280207267965793636691/280210000000000000000 : ℝ)+2*(14848012424669/2802100000000000 : ℝ)*(23/25000 : ℝ)=(10000000000002847/10000000000000000 : ℝ) by norm_num, show 1+2*(14345879/25000000000000000000 : ℝ)=(12500000000014345879/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4799853905910459/800000000000000000 : ℝ)+(14345879/25000000000000000000 : ℝ) ≤ ((280207267965793636691/280210000000000000000 : ℝ)+(14848012424669/2802100000000000 : ℝ)*((28113/100000 : ℝ)+(23/25000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (280207267965793636691/280210000000000000000 : ℝ)+(14848012424669/2802100000000000 : ℝ)*((28113/100000 : ℝ)+(23/25000 : ℝ))=(2503712003106879/2500000000000000 : ℝ) by norm_num, show 1+(4799853905910459/800000000000000000 : ℝ)+(14345879/25000000000000000000 : ℝ)=(100599981738296190891/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4799853905910459/800000000000000000 : ℝ) ≤ ((280207267965793636691/280210000000000000000 : ℝ)+2*(14848012424669/2802100000000000 : ℝ)*(28113/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (280207267965793636691/280210000000000000000 : ℝ)+2*(14848012424669/2802100000000000 : ℝ)*(28113/100000 : ℝ)=(2005939204970437/2000000000000000 : ℝ) by norm_num, show 1+2*(4799853905910459/800000000000000000 : ℝ)=(404799853905910459/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (280207267965793636691/280210000000000000000 : ℝ)*(X 1 0+X 2 0)+(14848012424669/2802100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (23/25000 : ℝ)) (hi := (28113/100000 : ℝ)) (c := (280207267965793636691/280210000000000000000 : ℝ)) (alpha := (14848012424669/2802100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (280207267965793636691/280210000000000000000 : ℝ)*(X 0 1+X 2 1)+(14848012424669/2802100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (23/25000 : ℝ)) (hi := (28113/100000 : ℝ)) (c := (280207267965793636691/280210000000000000000 : ℝ)) (alpha := (14848012424669/2802100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (280207267965793636691/280210000000000000000 : ℝ)*(X 0 2+X 1 2)+(14848012424669/2802100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (23/25000 : ℝ)) (hi := (28113/100000 : ℝ)) (c := (280207267965793636691/280210000000000000000 : ℝ)) (alpha := (14848012424669/2802100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-425325419/2000000000 : ℝ)*X 0 0+(1144520263/2000000000 : ℝ)*X 0 1+(623217141/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1084673431/2000000000 : ℝ)*X 1 0+(-2525881659/10000000000 : ℝ)*X 1 1+(4985737447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5423367721/10000000000 : ℝ)*X 2 0+(4985736803/10000000000 : ℝ)*X 2 1+(-1262940869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161942573/5000000000 : ℝ)*X 0 0+(366234907/1000000000 : ℝ)*X 0 1+(5106212203/10000000000 : ℝ)*X 0 2+(2161942573/5000000000 : ℝ)*X 1 0+(366234907/1000000000 : ℝ)*X 1 1+(5106212203/10000000000 : ℝ)*X 1 2+(2161942573/5000000000 : ℝ)*X 2 0+(366234907/1000000000 : ℝ)*X 2 1+(5106212203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2127550789/10000000000 : ℝ)*X 0 0+(2498048257/5000000000 : ℝ)*X 0 1+(5712029231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1047038681/2000000000 : ℝ)*X 1 0+(-899793849/5000000000 : ℝ)*X 1 1+(1428007731/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5235191377/10000000000 : ℝ)*X 2 0+(5712033163/10000000000 : ℝ)*X 2 1+(-899793653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325691141/10000000000 : ℝ)*X 0 0+(2542954919/5000000000 : ℝ)*X 0 1+(3683061309/10000000000 : ℝ)*X 0 2+(4325691141/10000000000 : ℝ)*X 1 0+(2542954919/5000000000 : ℝ)*X 1 1+(3683061309/10000000000 : ℝ)*X 1 2+(4325691141/10000000000 : ℝ)*X 2 0+(2542954919/5000000000 : ℝ)*X 2 1+(3683061309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14177664440096340621603495609/2001500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63740683/50000000000000 : ℝ)*(base1) + (1539894633/100000000000000 : ℝ)*(base19) + (13452221/800000000000 : ℝ)*(base23) + (158437109/100000000000000 : ℝ)*(upper3) + (170503023/100000000000000 : ℝ)*(upper5) + (1024855927330323/100000000000000 : ℝ)*(major0) + (1024855927330323/100000000000000 : ℝ)*(major1) + (1024855927330323/100000000000000 : ℝ)*(major2) + (1357109740082113/100000000000000 : ℝ)*(sp0) + (339279060879759/25000000000000 : ℝ)*(sp1) + (339279025471511/25000000000000 : ℝ)*(sp2) + (346294983157339/50000000000000 : ℝ)*(sp3) + (4085406461/50000000000000 : ℝ)*(sp4) + (3741333599/100000000000000 : ℝ)*(sp7) + (692593835129643/100000000000000 : ℝ)*(f.failure) + (135711778341367/10000000000000 : ℝ)*(f.sum) + (149888510291417/140105000000000000000000000000 : ℝ)*base65 + (310853564955393381193/28021000000000000000000000000000000 : ℝ)*base67 + (215735657100227381193/28021000000000000000000000000000000 : ℝ)*base69 + (244431098584251381193/28021000000000000000000000000000000 : ℝ)*base71 + (603525600969797/140105000000000000000000000000 : ℝ)*base73 + (305592653252661381193/28021000000000000000000000000000000 : ℝ)*base75 + (334369453766227381193/28021000000000000000000000000000000 : ℝ)*base77 + (224808224101984381193/28021000000000000000000000000000000 : ℝ)*base79 + (2169536784239/70052500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (17103969/2000000000000000000000 : ℝ)*base90 + (17103969/2000000000000000000000 : ℝ)*base92 + (17103969/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2811275751727015195679780289/700525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (342689901/12500000000000 : ℝ)*(base19) + (2665044063/100000000000000 : ℝ)*(base23) + (220590509/100000000000000 : ℝ)*(upper2) + (108090541/25000000000000 : ℝ)*(upper3) + (549469137/100000000000000 : ℝ)*(upper5) + (52740313736531/5000000000000 : ℝ)*(major0) + (52740313736531/5000000000000 : ℝ)*(major1) + (52740313736531/5000000000000 : ℝ)*(major2) + (6744294027/50000000000000 : ℝ)*(sp1) + (14691494987/100000000000000 : ℝ)*(sp2) + (69838912342797/5000000000000 : ℝ)*(sp4) + (698381008374339/50000000000000 : ℝ)*(sp5) + (139676089031689/10000000000000 : ℝ)*(sp6) + (14256683376707/2000000000000 : ℝ)*(sp7) + (14256683376707/2000000000000 : ℝ)*(f.failure) + (69838912342797/5000000000000 : ℝ)*(f.sum) + (30920662019267/14010500000000000000000000000 : ℝ)*base66 + (10804311668150441079/1401050000000000000000000000000000 : ℝ)*base68 + (5477363813421941079/1401050000000000000000000000000000 : ℝ)*base70 + (5933145021142941079/1401050000000000000000000000000000 : ℝ)*base72 + (5377590347543/14010500000000000000000000000 : ℝ)*base73 + (4819983405615441079/1401050000000000000000000000000000 : ℝ)*base76 + (10216907510999791079/1401050000000000000000000000000000 : ℝ)*base78 + (4836870500844991079/1401050000000000000000000000000000 : ℝ)*base80 + (1423910576421/875656250000000000000000000 : ℝ)*base81 + (56919/40000000000000000000 : ℝ)*base89 + (56919/40000000000000000000 : ℝ)*base91 + (56919/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (23/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5199/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_s2_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092051127/5000000000 : ℝ)*x 0 + (5526120169/10000000000 : ℝ)*x 1 + (5145754421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092051127/5000000000 : ℝ)^4129 ≤ (6612129747023/50000000000000 : ℝ)^3105 := by
    have hnat : (1092051127 : ℕ)^4129*50000000000000^3105 ≤ 6612129747023^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092051127 5000000000 6612129747023 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526120169/10000000000 : ℝ)^4129 ≤ (177514154483/390625000000 : ℝ)^3105 := by
    have hnat : (5526120169 : ℕ)^4129*390625000000^3105 ≤ 177514154483^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526120169 10000000000 177514154483 390625000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5145754421/10000000000 : ℝ)^4129 ≤ (2583257308777/6250000000000 : ℝ)^3105 := by
    have hnat : (5145754421 : ℕ)^4129*6250000000000^3105 ≤ 2583257308777^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145754421 10000000000 2583257308777 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092051127/5000000000 : ℝ), (5526120169/10000000000 : ℝ), (5145754421/10000000000 : ℝ)] ![(6612129747023/50000000000000 : ℝ), (177514154483/390625000000 : ℝ), (2583257308777/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092051127/5000000000 : ℝ)|^4129 ≤ (6612129747023/50000000000000 : ℝ)^3105
        have hw : |(-1092051127/5000000000 : ℝ)|=(1092051127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526120169/10000000000 : ℝ)|^4129 ≤ (177514154483/390625000000 : ℝ)^3105
        have hw : |(5526120169/10000000000 : ℝ)|=(5526120169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5145754421/10000000000 : ℝ)|^4129 ≤ (2583257308777/6250000000000 : ℝ)^3105
        have hw : |(5145754421/10000000000 : ℝ)|=(5145754421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537725041/1000000000 : ℝ)*x 0 + (-2382474523/10000000000 : ℝ)*x 1 + (5145755723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537725041/1000000000 : ℝ)^4129 ≤ (43822944221487/100000000000000 : ℝ)^3105 := by
    have hnat : (537725041 : ℕ)^4129*100000000000000^3105 ≤ 43822944221487^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537725041 1000000000 43822944221487 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2382474523/10000000000 : ℝ)^4129 ≤ (14844924921541/100000000000000 : ℝ)^3105 := by
    have hnat : (2382474523 : ℕ)^4129*100000000000000^3105 ≤ 14844924921541^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382474523 10000000000 14844924921541 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5145755723/10000000000 : ℝ)^4129 ≤ (20666065423707/50000000000000 : ℝ)^3105 := by
    have hnat : (5145755723 : ℕ)^4129*50000000000000^3105 ≤ 20666065423707^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145755723 10000000000 20666065423707 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537725041/1000000000 : ℝ), (-2382474523/10000000000 : ℝ), (5145755723/10000000000 : ℝ)] ![(43822944221487/100000000000000 : ℝ), (14844924921541/100000000000000 : ℝ), (20666065423707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537725041/1000000000 : ℝ)|^4129 ≤ (43822944221487/100000000000000 : ℝ)^3105
        have hw : |(537725041/1000000000 : ℝ)|=(537725041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2382474523/10000000000 : ℝ)|^4129 ≤ (14844924921541/100000000000000 : ℝ)^3105
        have hw : |(-2382474523/10000000000 : ℝ)|=(2382474523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5145755723/10000000000 : ℝ)|^4129 ≤ (20666065423707/50000000000000 : ℝ)^3105
        have hw : |(5145755723/10000000000 : ℝ)|=(5145755723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377250473/10000000000 : ℝ)*x 0 + (5145755653/10000000000 : ℝ)*x 1 + (-238247453/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377250473/10000000000 : ℝ)^4129 ≤ (21911472452121/50000000000000 : ℝ)^3105 := by
    have hnat : (5377250473 : ℕ)^4129*50000000000000^3105 ≤ 21911472452121^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377250473 10000000000 21911472452121 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5145755653/10000000000 : ℝ)^4129 ≤ (20666065049863/50000000000000 : ℝ)^3105 := by
    have hnat : (5145755653 : ℕ)^4129*50000000000000^3105 ≤ 20666065049863^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145755653 10000000000 20666065049863 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238247453/1000000000 : ℝ)^4129 ≤ (7422462489771/50000000000000 : ℝ)^3105 := by
    have hnat : (238247453 : ℕ)^4129*50000000000000^3105 ≤ 7422462489771^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238247453 1000000000 7422462489771 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377250473/10000000000 : ℝ), (5145755653/10000000000 : ℝ), (-238247453/1000000000 : ℝ)] ![(21911472452121/50000000000000 : ℝ), (20666065049863/50000000000000 : ℝ), (7422462489771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377250473/10000000000 : ℝ)|^4129 ≤ (21911472452121/50000000000000 : ℝ)^3105
        have hw : |(5377250473/10000000000 : ℝ)|=(5377250473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5145755653/10000000000 : ℝ)|^4129 ≤ (20666065049863/50000000000000 : ℝ)^3105
        have hw : |(5145755653/10000000000 : ℝ)|=(5145755653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238247453/1000000000 : ℝ)|^4129 ≤ (7422462489771/50000000000000 : ℝ)^3105
        have hw : |(-238247453/1000000000 : ℝ)|=(238247453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1090775843/2500000000 : ℝ)*x 0 + (400649893/1000000000 : ℝ)*x 1 + (2375902893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090775843/2500000000 : ℝ)^4129 ≤ (33189707386731/100000000000000 : ℝ)^3105 := by
    have hnat : (1090775843 : ℕ)^4129*100000000000000^3105 ≤ 33189707386731^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090775843 2500000000 33189707386731 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400649893/1000000000 : ℝ)^4129 ≤ (14815989200153/50000000000000 : ℝ)^3105 := by
    have hnat : (400649893 : ℕ)^4129*50000000000000^3105 ≤ 14815989200153^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400649893 1000000000 14815989200153 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2375902893/5000000000 : ℝ)^4129 ≤ (3717831420191/10000000000000 : ℝ)^3105 := by
    have hnat : (2375902893 : ℕ)^4129*10000000000000^3105 ≤ 3717831420191^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375902893 5000000000 3717831420191 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090775843/2500000000 : ℝ), (400649893/1000000000 : ℝ), (2375902893/5000000000 : ℝ)] ![(33189707386731/100000000000000 : ℝ), (14815989200153/50000000000000 : ℝ), (3717831420191/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090775843/2500000000 : ℝ)|^4129 ≤ (33189707386731/100000000000000 : ℝ)^3105
        have hw : |(1090775843/2500000000 : ℝ)|=(1090775843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400649893/1000000000 : ℝ)|^4129 ≤ (14815989200153/50000000000000 : ℝ)^3105
        have hw : |(400649893/1000000000 : ℝ)|=(400649893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2375902893/5000000000 : ℝ)|^4129 ≤ (3717831420191/10000000000000 : ℝ)^3105
        have hw : |(2375902893/5000000000 : ℝ)|=(2375902893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184228221/10000000000 : ℝ)*x 0 + (32178281/62500000 : ℝ)*x 1 + (5523320807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184228221/10000000000 : ℝ)^4129 ≤ (13225273738381/100000000000000 : ℝ)^3105 := by
    have hnat : (2184228221 : ℕ)^4129*100000000000000^3105 ≤ 13225273738381^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184228221 10000000000 13225273738381 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32178281/62500000 : ℝ)^4129 ≤ (41361712372931/100000000000000 : ℝ)^3105 := by
    have hnat : (32178281 : ℕ)^4129*100000000000000^3105 ≤ 41361712372931^3105*62500000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32178281 62500000 41361712372931 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5523320807/10000000000 : ℝ)^4129 ≤ (4541301387483/10000000000000 : ℝ)^3105 := by
    have hnat : (5523320807 : ℕ)^4129*10000000000000^3105 ≤ 4541301387483^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523320807 10000000000 4541301387483 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184228221/10000000000 : ℝ), (32178281/62500000 : ℝ), (5523320807/10000000000 : ℝ)] ![(13225273738381/100000000000000 : ℝ), (41361712372931/100000000000000 : ℝ), (4541301387483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184228221/10000000000 : ℝ)|^4129 ≤ (13225273738381/100000000000000 : ℝ)^3105
        have hw : |(-2184228221/10000000000 : ℝ)|=(2184228221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32178281/62500000 : ℝ)|^4129 ≤ (41361712372931/100000000000000 : ℝ)^3105
        have hw : |(32178281/62500000 : ℝ)|=(32178281/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5523320807/10000000000 : ℝ)|^4129 ≤ (4541301387483/10000000000000 : ℝ)^3105
        have hw : |(5523320807/10000000000 : ℝ)|=(5523320807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264062441/500000000 : ℝ)*x 0 + (-100245537/500000000 : ℝ)*x 1 + (5523320891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264062441/500000000 : ℝ)^4129 ≤ (42785613054341/100000000000000 : ℝ)^3105 := by
    have hnat : (264062441 : ℕ)^4129*100000000000000^3105 ≤ 42785613054341^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264062441 500000000 42785613054341 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100245537/500000000 : ℝ)^4129 ≤ (11801372141801/100000000000000 : ℝ)^3105 := by
    have hnat : (100245537 : ℕ)^4129*100000000000000^3105 ≤ 11801372141801^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100245537 500000000 11801372141801 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5523320891/10000000000 : ℝ)^4129 ≤ (45413014793253/100000000000000 : ℝ)^3105 := by
    have hnat : (5523320891 : ℕ)^4129*100000000000000^3105 ≤ 45413014793253^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523320891 10000000000 45413014793253 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264062441/500000000 : ℝ), (-100245537/500000000 : ℝ), (5523320891/10000000000 : ℝ)] ![(42785613054341/100000000000000 : ℝ), (11801372141801/100000000000000 : ℝ), (45413014793253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264062441/500000000 : ℝ)|^4129 ≤ (42785613054341/100000000000000 : ℝ)^3105
        have hw : |(264062441/500000000 : ℝ)|=(264062441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100245537/500000000 : ℝ)|^4129 ≤ (11801372141801/100000000000000 : ℝ)^3105
        have hw : |(-100245537/500000000 : ℝ)|=(100245537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5523320891/10000000000 : ℝ)|^4129 ≤ (45413014793253/100000000000000 : ℝ)^3105
        have hw : |(5523320891/10000000000 : ℝ)|=(5523320891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660156133/1250000000 : ℝ)*x 0 + (5523320727/10000000000 : ℝ)*x 1 + (-2004910633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660156133/1250000000 : ℝ)^4129 ≤ (42785615683/100000000000 : ℝ)^3105 := by
    have hnat : (660156133 : ℕ)^4129*100000000000^3105 ≤ 42785615683^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660156133 1250000000 42785615683 100000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523320727/10000000000 : ℝ)^4129 ≤ (22706506500071/50000000000000 : ℝ)^3105 := by
    have hnat : (5523320727 : ℕ)^4129*50000000000000^3105 ≤ 22706506500071^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523320727 10000000000 22706506500071 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004910633/10000000000 : ℝ)^4129 ≤ (11801371304263/100000000000000 : ℝ)^3105 := by
    have hnat : (2004910633 : ℕ)^4129*100000000000000^3105 ≤ 11801371304263^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004910633 10000000000 11801371304263 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660156133/1250000000 : ℝ), (5523320727/10000000000 : ℝ), (-2004910633/10000000000 : ℝ)] ![(42785615683/100000000000 : ℝ), (22706506500071/50000000000000 : ℝ), (11801371304263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660156133/1250000000 : ℝ)|^4129 ≤ (42785615683/100000000000 : ℝ)^3105
        have hw : |(660156133/1250000000 : ℝ)|=(660156133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523320727/10000000000 : ℝ)|^4129 ≤ (22706506500071/50000000000000 : ℝ)^3105
        have hw : |(5523320727/10000000000 : ℝ)|=(5523320727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2004910633/10000000000 : ℝ)|^4129 ≤ (11801371304263/100000000000000 : ℝ)^3105
        have hw : |(-2004910633/10000000000 : ℝ)|=(2004910633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4363348711/10000000000 : ℝ)*x 0 + (2373191519/5000000000 : ℝ)*x 1 + (2005990439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363348711/10000000000 : ℝ)^4129 ≤ (1037255911199/3125000000000 : ℝ)^3105 := by
    have hnat : (4363348711 : ℕ)^4129*3125000000000^3105 ≤ 1037255911199^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363348711 10000000000 1037255911199 3125000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2373191519/5000000000 : ℝ)^4129 ≤ (7424380947939/20000000000000 : ℝ)^3105 := by
    have hnat : (2373191519 : ℕ)^4129*20000000000000^3105 ≤ 7424380947939^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373191519 5000000000 7424380947939 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005990439/5000000000 : ℝ)^4129 ≤ (29685906082161/100000000000000 : ℝ)^3105 := by
    have hnat : (2005990439 : ℕ)^4129*100000000000000^3105 ≤ 29685906082161^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005990439 5000000000 29685906082161 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363348711/10000000000 : ℝ), (2373191519/5000000000 : ℝ), (2005990439/5000000000 : ℝ)] ![(1037255911199/3125000000000 : ℝ), (7424380947939/20000000000000 : ℝ), (29685906082161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363348711/10000000000 : ℝ)|^4129 ≤ (1037255911199/3125000000000 : ℝ)^3105
        have hw : |(4363348711/10000000000 : ℝ)|=(4363348711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2373191519/5000000000 : ℝ)|^4129 ≤ (7424380947939/20000000000000 : ℝ)^3105
        have hw : |(2373191519/5000000000 : ℝ)|=(2373191519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005990439/5000000000 : ℝ)|^4129 ≤ (29685906082161/100000000000000 : ℝ)^3105
        have hw : |(2005990439/5000000000 : ℝ)|=(2005990439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_8 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-19725521/2000000000 : ℝ)*x 0 + (1185658819/2000000000 : ℝ)*x 1 + (1482028243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19725521/2000000000 : ℝ)^4129 ≤ (21499973461/10000000000000 : ℝ)^3105 := by
    have hnat : (19725521 : ℕ)^4129*10000000000000^3105 ≤ 21499973461^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19725521 2000000000 21499973461 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1185658819/2000000000 : ℝ)^4129 ≤ (12473378415321/25000000000000 : ℝ)^3105 := by
    have hnat : (1185658819 : ℕ)^4129*25000000000000^3105 ≤ 12473378415321^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185658819 2000000000 12473378415321 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482028243/2500000000 : ℝ)^4129 ≤ (24945743294951/50000000000000 : ℝ)^3105 := by
    have hnat : (1482028243 : ℕ)^4129*50000000000000^3105 ≤ 24945743294951^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482028243 2500000000 24945743294951 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19725521/2000000000 : ℝ), (1185658819/2000000000 : ℝ), (1482028243/2500000000 : ℝ)] ![(21499973461/10000000000000 : ℝ), (12473378415321/25000000000000 : ℝ), (24945743294951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19725521/2000000000 : ℝ)|^4129 ≤ (21499973461/10000000000000 : ℝ)^3105
        have hw : |(-19725521/2000000000 : ℝ)|=(19725521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1185658819/2000000000 : ℝ)|^4129 ≤ (12473378415321/25000000000000 : ℝ)^3105
        have hw : |(1185658819/2000000000 : ℝ)|=(1185658819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1482028243/2500000000 : ℝ)|^4129 ≤ (24945743294951/50000000000000 : ℝ)^3105
        have hw : |(1482028243/2500000000 : ℝ)|=(1482028243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_9 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (396636089/5000000000 : ℝ)*x 0 + (-39789053/80000000 : ℝ)*x 1 + (1639397679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396636089/5000000000 : ℝ)^4129 ≤ (687847157107/20000000000000 : ℝ)^3105 := by
    have hnat : (396636089 : ℕ)^4129*20000000000000^3105 ≤ 687847157107^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396636089 5000000000 687847157107 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39789053/80000000 : ℝ)^4129 ≤ (39503848528073/100000000000000 : ℝ)^3105 := by
    have hnat : (39789053 : ℕ)^4129*100000000000000^3105 ≤ 39503848528073^3105*80000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39789053 80000000 39503848528073 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639397679/2500000000 : ℝ)^4129 ≤ (57056915675623/100000000000000 : ℝ)^3105 := by
    have hnat : (1639397679 : ℕ)^4129*100000000000000^3105 ≤ 57056915675623^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639397679 2500000000 57056915675623 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(396636089/5000000000 : ℝ), (-39789053/80000000 : ℝ), (1639397679/2500000000 : ℝ)] ![(687847157107/20000000000000 : ℝ), (39503848528073/100000000000000 : ℝ), (57056915675623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(396636089/5000000000 : ℝ)|^4129 ≤ (687847157107/20000000000000 : ℝ)^3105
        have hw : |(396636089/5000000000 : ℝ)|=(396636089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39789053/80000000 : ℝ)|^4129 ≤ (39503848528073/100000000000000 : ℝ)^3105
        have hw : |(-39789053/80000000 : ℝ)|=(39789053/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1639397679/2500000000 : ℝ)|^4129 ≤ (57056915675623/100000000000000 : ℝ)^3105
        have hw : |(1639397679/2500000000 : ℝ)|=(1639397679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_10 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (197973239/2500000000 : ℝ)*x 0 + (6554037073/10000000000 : ℝ)*x 1 + (-1244569021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197973239/2500000000 : ℝ)^4129 ≤ (3431286417463/100000000000000 : ℝ)^3105 := by
    have hnat : (197973239 : ℕ)^4129*100000000000000^3105 ≤ 3431286417463^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197973239 2500000000 3431286417463 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6554037073/10000000000 : ℝ)^4129 ≤ (14253950596107/25000000000000 : ℝ)^3105 := by
    have hnat : (6554037073 : ℕ)^4129*25000000000000^3105 ≤ 14253950596107^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6554037073 10000000000 14253950596107 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244569021/2500000000 : ℝ)^4129 ≤ (1977645559219/5000000000000 : ℝ)^3105 := by
    have hnat : (1244569021 : ℕ)^4129*5000000000000^3105 ≤ 1977645559219^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244569021 2500000000 1977645559219 5000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(197973239/2500000000 : ℝ), (6554037073/10000000000 : ℝ), (-1244569021/2500000000 : ℝ)] ![(3431286417463/100000000000000 : ℝ), (14253950596107/25000000000000 : ℝ), (1977645559219/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(197973239/2500000000 : ℝ)|^4129 ≤ (3431286417463/100000000000000 : ℝ)^3105
        have hw : |(197973239/2500000000 : ℝ)|=(197973239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6554037073/10000000000 : ℝ)|^4129 ≤ (14253950596107/25000000000000 : ℝ)^3105
        have hw : |(6554037073/10000000000 : ℝ)|=(6554037073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1244569021/2500000000 : ℝ)|^4129 ≤ (1977645559219/5000000000000 : ℝ)^3105
        have hw : |(-1244569021/2500000000 : ℝ)|=(1244569021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s2_11 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420579763/10000000000 : ℝ)*x 0 + (2934844071/5000000000 : ℝ)*x 1 + (1468396917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420579763/10000000000 : ℝ)^4129 ≤ (1479130246431/100000000000000 : ℝ)^3105 := by
    have hnat : (420579763 : ℕ)^4129*100000000000000^3105 ≤ 1479130246431^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420579763 10000000000 1479130246431 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934844071/5000000000 : ℝ)^4129 ≤ (24619341311481/50000000000000 : ℝ)^3105 := by
    have hnat : (2934844071 : ℕ)^4129*50000000000000^3105 ≤ 24619341311481^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934844071 5000000000 24619341311481 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1468396917/2500000000 : ℝ)^4129 ≤ (24641093555509/50000000000000 : ℝ)^3105 := by
    have hnat : (1468396917 : ℕ)^4129*50000000000000^3105 ≤ 24641093555509^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468396917 2500000000 24641093555509 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420579763/10000000000 : ℝ), (2934844071/5000000000 : ℝ), (1468396917/2500000000 : ℝ)] ![(1479130246431/100000000000000 : ℝ), (24619341311481/50000000000000 : ℝ), (24641093555509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420579763/10000000000 : ℝ)|^4129 ≤ (1479130246431/100000000000000 : ℝ)^3105
        have hw : |(420579763/10000000000 : ℝ)|=(420579763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934844071/5000000000 : ℝ)|^4129 ≤ (24619341311481/50000000000000 : ℝ)^3105
        have hw : |(2934844071/5000000000 : ℝ)|=(2934844071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1468396917/2500000000 : ℝ)|^4129 ≤ (24641093555509/50000000000000 : ℝ)^3105
        have hw : |(1468396917/2500000000 : ℝ)|=(1468396917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5199/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8707/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2093/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5199/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5199/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5199/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5199/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5199/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5199/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5207/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (33464705745951/5000000000000000000 : ℝ) := by
    have hpowers : (5207/100000 : ℝ)^8257 ≤ (33464705745951/5000000000000000000 : ℝ)^2048 := by
      have hnat : (5207 : ℕ)^8257*5000000000000000000^2048 ≤ 33464705745951^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5207 100000 33464705745951 5000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5207/100000 : ℝ)) (X := (33464705745951/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5199/25000 : ℝ) ^ (8257/2048 : ℝ) ≤ (35587959041444907/20000000000000000000 : ℝ) := by
    have hpowers : (5199/25000 : ℝ)^8257 ≤ (35587959041444907/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5199 : ℕ)^8257*20000000000000000000^2048 ≤ 35587959041444907^2048*25000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5199 25000 35587959041444907 20000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5199/25000 : ℝ)) (X := (35587959041444907/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500033464705745951/2500000000000000000 : ℝ) ≤ (2000006640220171/2000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (2500033464705745951/2500000000000000000 : ℝ)^2048 ≤ (2000006640220171/2000000000000000 : ℝ)^8257 := by
      have hnat : (2500033464705745951 : ℕ)^2048*2000000000000000^8257 ≤ 2000006640220171^8257*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500033464705745951 2500000000000000000 2000006640220171 2000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000006640220171/2000000000000000 : ℝ)) (X := (2500033464705745951/2500000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20035721817864428711/20000000000000000000 : ℝ) ≤ (5002213552299129/5000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (20035721817864428711/20000000000000000000 : ℝ)^2048 ≤ (5002213552299129/5000000000000000 : ℝ)^8257 := by
      have hnat : (20035721817864428711 : ℕ)^2048*5000000000000000^8257 ≤ 5002213552299129^8257*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20035721817864428711 20000000000000000000 5002213552299129 5000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002213552299129/5000000000000000 : ℝ)) (X := (20035721817864428711/20000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10035587959041444907/10000000000000000000 : ℝ) ≤ (10008821008095661/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (10035587959041444907/10000000000000000000 : ℝ)^2048 ≤ (10008821008095661/10000000000000000 : ℝ)^8257 := by
      have hnat : (10035587959041444907 : ℕ)^2048*10000000000000000^8257 ≤ 10008821008095661^8257*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10035587959041444907 10000000000000000000 10008821008095661 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008821008095661/10000000000000000 : ℝ)) (X := (10035587959041444907/10000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(33464705745951/5000000000000000000 : ℝ) ≤ ((22263537065848467679/22270000000000000000 : ℝ)+2*(627700499629/222700000000000 : ℝ)*(5207/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (22263537065848467679/22270000000000000000 : ℝ)+2*(627700499629/222700000000000 : ℝ)*(5207/100000 : ℝ)=(2000006640220171/2000000000000000 : ℝ) by norm_num, show 1+2*(33464705745951/5000000000000000000 : ℝ)=(2500033464705745951/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35587959041444907/20000000000000000000 : ℝ)+(33464705745951/5000000000000000000 : ℝ) ≤ ((22263537065848467679/22270000000000000000 : ℝ)+(627700499629/222700000000000 : ℝ)*((5199/25000 : ℝ)+(5207/100000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (22263537065848467679/22270000000000000000 : ℝ)+(627700499629/222700000000000 : ℝ)*((5199/25000 : ℝ)+(5207/100000 : ℝ))=(5002213552299129/5000000000000000 : ℝ) by norm_num, show 1+(35587959041444907/20000000000000000000 : ℝ)+(33464705745951/5000000000000000000 : ℝ)=(20035721817864428711/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35587959041444907/20000000000000000000 : ℝ) ≤ ((22263537065848467679/22270000000000000000 : ℝ)+2*(627700499629/222700000000000 : ℝ)*(5199/25000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (22263537065848467679/22270000000000000000 : ℝ)+2*(627700499629/222700000000000 : ℝ)*(5199/25000 : ℝ)=(10008821008095661/10000000000000000 : ℝ) by norm_num, show 1+2*(35587959041444907/20000000000000000000 : ℝ)=(10035587959041444907/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22263537065848467679/22270000000000000000 : ℝ)*(X 1 0+X 2 0)+(627700499629/222700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (5207/100000 : ℝ)) (hi := (5199/25000 : ℝ)) (c := (22263537065848467679/22270000000000000000 : ℝ)) (alpha := (627700499629/222700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22263537065848467679/22270000000000000000 : ℝ)*(X 0 1+X 2 1)+(627700499629/222700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (5207/100000 : ℝ)) (hi := (5199/25000 : ℝ)) (c := (22263537065848467679/22270000000000000000 : ℝ)) (alpha := (627700499629/222700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22263537065848467679/22270000000000000000 : ℝ)*(X 0 2+X 1 2)+(627700499629/222700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (5207/100000 : ℝ)) (hi := (5199/25000 : ℝ)) (c := (22263537065848467679/22270000000000000000 : ℝ)) (alpha := (627700499629/222700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092051127/5000000000 : ℝ)*X 0 0+(5526120169/10000000000 : ℝ)*X 0 1+(5145754421/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537725041/1000000000 : ℝ)*X 1 0+(-2382474523/10000000000 : ℝ)*X 1 1+(5145755723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377250473/10000000000 : ℝ)*X 2 0+(5145755653/10000000000 : ℝ)*X 2 1+(-238247453/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090775843/2500000000 : ℝ)*X 0 0+(400649893/1000000000 : ℝ)*X 0 1+(2375902893/5000000000 : ℝ)*X 0 2+(1090775843/2500000000 : ℝ)*X 1 0+(400649893/1000000000 : ℝ)*X 1 1+(2375902893/5000000000 : ℝ)*X 1 2+(1090775843/2500000000 : ℝ)*X 2 0+(400649893/1000000000 : ℝ)*X 2 1+(2375902893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184228221/10000000000 : ℝ)*X 0 0+(32178281/62500000 : ℝ)*X 0 1+(5523320807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264062441/500000000 : ℝ)*X 1 0+(-100245537/500000000 : ℝ)*X 1 1+(5523320891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660156133/1250000000 : ℝ)*X 2 0+(5523320727/10000000000 : ℝ)*X 2 1+(-2004910633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363348711/10000000000 : ℝ)*X 0 0+(2373191519/5000000000 : ℝ)*X 0 1+(2005990439/5000000000 : ℝ)*X 0 2+(4363348711/10000000000 : ℝ)*X 1 0+(2373191519/5000000000 : ℝ)*X 1 1+(2005990439/5000000000 : ℝ)*X 1 2+(4363348711/10000000000 : ℝ)*X 2 0+(2373191519/5000000000 : ℝ)*X 2 1+(2005990439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-19725521/2000000000 : ℝ)*X 0 0+(1185658819/2000000000 : ℝ)*X 0 1+(1482028243/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((396636089/5000000000 : ℝ)*X 1 0+(-39789053/80000000 : ℝ)*X 1 1+(1639397679/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((197973239/2500000000 : ℝ)*X 2 0+(6554037073/10000000000 : ℝ)*X 2 1+(-1244569021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((420579763/10000000000 : ℝ)*X 0 0+(2934844071/5000000000 : ℝ)*X 0 1+(1468396917/2500000000 : ℝ)*X 0 2+(420579763/10000000000 : ℝ)*X 1 0+(2934844071/5000000000 : ℝ)*X 1 1+(1468396917/2500000000 : ℝ)*X 1 2+(420579763/10000000000 : ℝ)*X 2 0+(2934844071/5000000000 : ℝ)*X 2 1+(1468396917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3406657581714866520829595853/1113500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1985406522530031/100000000000000 : ℝ)*(major0) + (1985406522530031/100000000000000 : ℝ)*(major1) + (1985406522530031/100000000000000 : ℝ)*(major2) + (1314532389824639/50000000000000 : ℝ)*(sp0) + (328634405343361/12500000000000 : ℝ)*(sp1) + (105162995571067/4000000000000 : ℝ)*(sp2) + (67086459976213/5000000000000 : ℝ)*(sp3) + (2073070219/12500000000000 : ℝ)*(sp4) + (6350101849/100000000000000 : ℝ)*(sp5) + (6674538681/100000000000000 : ℝ)*(sp6) + (1213594219/100000000000000 : ℝ)*(sp8) + (984956513/100000000000000 : ℝ)*(sp9) + (1013989893/100000000000000 : ℝ)*(sp10) + (291437519/25000000000000 : ℝ)*(sp11) + (1341730365274337/100000000000000 : ℝ)*(f.failure) + (2629082577805249/100000000000000 : ℝ)*(f.sum) + (5864089982321/2783750000000000000000000000 : ℝ)*base65 + (13406757986587268049/2227000000000000000000000000000000 : ℝ)*base67 + (8992896100614268049/2227000000000000000000000000000000 : ℝ)*base69 + (3808194718553731951/2227000000000000000000000000000000 : ℝ)*base72 + (38466661733647/5567500000000000000000000000 : ℝ)*base73 + (3799793666152731951/2227000000000000000000000000000000 : ℝ)*base76 + (17529877061035268049/2227000000000000000000000000000000 : ℝ)*base77 + (11618736779499268049/2227000000000000000000000000000000 : ℝ)*base79 + (3174059198809/695937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10877629/2000000000000000000000 : ℝ)*base89 + (10877629/2000000000000000000000 : ℝ)*base91 + (10877629/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1461227959812576251608768143/278375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1007443345966861/50000000000000 : ℝ)*(major0) + (1007443345966861/50000000000000 : ℝ)*(major1) + (1007443345966861/50000000000000 : ℝ)*(major2) + (55055513/100000000000000 : ℝ)*(sp0) + (34168029/6250000000000 : ℝ)*(sp1) + (63397709/20000000000000 : ℝ)*(sp3) + (2668119520785683/100000000000000 : ℝ)*(sp4) + (106724779175947/4000000000000 : ℝ)*(sp5) + (333514986604179/12500000000000 : ℝ)*(sp6) + (68082611065741/5000000000000 : ℝ)*(sp7) + (33931077/5000000000000 : ℝ)*(sp8) + (228375597/100000000000000 : ℝ)*(sp9) + (45203663/12500000000000 : ℝ)*(sp10) + (416130173/100000000000000 : ℝ)*(sp11) + (680826477216769/50000000000000 : ℝ)*(f.failure) + (166757515903921/6250000000000 : ℝ)*(f.sum) + (3501362901219/1391875000000000000000000000 : ℝ)*base66 + (3526345475304985619/1113500000000000000000000000000000 : ℝ)*base67 + (98599964807514381/1113500000000000000000000000000000 : ℝ)*base70 + (5932396818692985619/1113500000000000000000000000000000 : ℝ)*base71 + (3841883747473/11135000000000000000000000000 : ℝ)*base73 + (3191725374439985619/1113500000000000000000000000000000 : ℝ)*base75 + (5370228231501985619/1113500000000000000000000000000000 : ℝ)*base77 + (1342285844588485619/1113500000000000000000000000000000 : ℝ)*base79 + (1232646514977/695937500000000000000000000 : ℝ)*base82 + (6209373/1000000000000000000000 : ℝ)*base89 + (6209373/1000000000000000000000 : ℝ)*base91 + (6209373/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5199/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1065_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1065_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1065_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1065_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

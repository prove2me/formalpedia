-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1672_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:14.107279+00:00
-- url     : https://prove2.me/submissions/a0ce60bc-60fa-401c-b55b-0513c4005458

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
theorem support_rectangle_w1672_s3_0 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1559810977/10000000000 : ℝ)*x 0 + (108822989/200000000 : ℝ)*x 1 + (1296281743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1559810977/10000000000 : ℝ)^5007 ≤ (9674236773257/100000000000000 : ℝ)^3983 := by
    have hnat : (1559810977 : ℕ)^5007*100000000000000^3983 ≤ 9674236773257^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559810977 10000000000 9674236773257 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108822989/200000000 : ℝ)^5007 ≤ (46530601460781/100000000000000 : ℝ)^3983 := by
    have hnat : (108822989 : ℕ)^5007*100000000000000^3983 ≤ 46530601460781^3983*200000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108822989 200000000 46530601460781 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296281743/2500000000 : ℝ)^5007 ≤ (43795161751843/100000000000000 : ℝ)^3983 := by
    have hnat : (1296281743 : ℕ)^5007*100000000000000^3983 ≤ 43795161751843^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296281743 2500000000 43795161751843 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1559810977/10000000000 : ℝ), (108822989/200000000 : ℝ), (1296281743/2500000000 : ℝ)] ![(9674236773257/100000000000000 : ℝ), (46530601460781/100000000000000 : ℝ), (43795161751843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1559810977/10000000000 : ℝ)|^5007 ≤ (9674236773257/100000000000000 : ℝ)^3983
        have hw : |(-1559810977/10000000000 : ℝ)|=(1559810977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108822989/200000000 : ℝ)|^5007 ≤ (46530601460781/100000000000000 : ℝ)^3983
        have hw : |(108822989/200000000 : ℝ)|=(108822989/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296281743/2500000000 : ℝ)|^5007 ≤ (43795161751843/100000000000000 : ℝ)^3983
        have hw : |(1296281743/2500000000 : ℝ)|=(1296281743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_1 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344403721/10000000000 : ℝ)*x 0 + (-67659921/400000000 : ℝ)*x 1 + (2592563497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344403721/10000000000 : ℝ)^5007 ≤ (45492956163071/100000000000000 : ℝ)^3983 := by
    have hnat : (5344403721 : ℕ)^5007*100000000000000^3983 ≤ 45492956163071^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344403721 10000000000 45492956163071 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67659921/400000000 : ℝ)^5007 ≤ (5355940920169/50000000000000 : ℝ)^3983 := by
    have hnat : (67659921 : ℕ)^5007*50000000000000^3983 ≤ 5355940920169^3983*400000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67659921 400000000 5355940920169 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592563497/5000000000 : ℝ)^5007 ≤ (8759032397087/20000000000000 : ℝ)^3983 := by
    have hnat : (2592563497 : ℕ)^5007*20000000000000^3983 ≤ 8759032397087^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592563497 5000000000 8759032397087 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344403721/10000000000 : ℝ), (-67659921/400000000 : ℝ), (2592563497/5000000000 : ℝ)] ![(45492956163071/100000000000000 : ℝ), (5355940920169/50000000000000 : ℝ), (8759032397087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344403721/10000000000 : ℝ)|^5007 ≤ (45492956163071/100000000000000 : ℝ)^3983
        have hw : |(5344403721/10000000000 : ℝ)|=(5344403721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-67659921/400000000 : ℝ)|^5007 ≤ (5355940920169/50000000000000 : ℝ)^3983
        have hw : |(-67659921/400000000 : ℝ)|=(67659921/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592563497/5000000000 : ℝ)|^5007 ≤ (8759032397087/20000000000000 : ℝ)^3983
        have hw : |(2592563497/5000000000 : ℝ)|=(2592563497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_2 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344403723/10000000000 : ℝ)*x 0 + (1296281741/2500000000 : ℝ)*x 1 + (-1691498063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344403723/10000000000 : ℝ)^5007 ≤ (45492956184473/100000000000000 : ℝ)^3983 := by
    have hnat : (5344403723 : ℕ)^5007*100000000000000^3983 ≤ 45492956184473^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344403723 10000000000 45492956184473 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296281741/2500000000 : ℝ)^5007 ≤ (43795161666901/100000000000000 : ℝ)^3983 := by
    have hnat : (1296281741 : ℕ)^5007*100000000000000^3983 ≤ 43795161666901^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296281741 2500000000 43795161666901 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691498063/10000000000 : ℝ)^5007 ≤ (10711882142851/100000000000000 : ℝ)^3983 := by
    have hnat : (1691498063 : ℕ)^5007*100000000000000^3983 ≤ 10711882142851^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691498063 10000000000 10711882142851 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344403723/10000000000 : ℝ), (1296281741/2500000000 : ℝ), (-1691498063/10000000000 : ℝ)] ![(45492956184473/100000000000000 : ℝ), (43795161666901/100000000000000 : ℝ), (10711882142851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344403723/10000000000 : ℝ)|^5007 ≤ (45492956184473/100000000000000 : ℝ)^3983
        have hw : |(5344403723/10000000000 : ℝ)|=(5344403723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296281741/2500000000 : ℝ)|^5007 ≤ (43795161666901/100000000000000 : ℝ)^3983
        have hw : |(1296281741/2500000000 : ℝ)|=(1296281741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1691498063/10000000000 : ℝ)|^5007 ≤ (10711882142851/100000000000000 : ℝ)^3983
        have hw : |(-1691498063/10000000000 : ℝ)|=(1691498063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_3 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4164180797/10000000000 : ℝ)*x 0 + (95839043/250000000 : ℝ)*x 1 + (2257174297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164180797/10000000000 : ℝ)^5007 ≤ (33244011984493/100000000000000 : ℝ)^3983 := by
    have hnat : (4164180797 : ℕ)^5007*100000000000000^3983 ≤ 33244011984493^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164180797 10000000000 33244011984493 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95839043/250000000 : ℝ)^5007 ≤ (29960545421557/100000000000000 : ℝ)^3983 := by
    have hnat : (95839043 : ℕ)^5007*100000000000000^3983 ≤ 29960545421557^3983*250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95839043 250000000 29960545421557 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257174297/5000000000 : ℝ)^5007 ≤ (3679544256663/10000000000000 : ℝ)^3983 := by
    have hnat : (2257174297 : ℕ)^5007*10000000000000^3983 ≤ 3679544256663^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257174297 5000000000 3679544256663 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164180797/10000000000 : ℝ), (95839043/250000000 : ℝ), (2257174297/5000000000 : ℝ)] ![(33244011984493/100000000000000 : ℝ), (29960545421557/100000000000000 : ℝ), (3679544256663/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164180797/10000000000 : ℝ)|^5007 ≤ (33244011984493/100000000000000 : ℝ)^3983
        have hw : |(4164180797/10000000000 : ℝ)|=(4164180797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95839043/250000000 : ℝ)|^5007 ≤ (29960545421557/100000000000000 : ℝ)^3983
        have hw : |(95839043/250000000 : ℝ)|=(95839043/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2257174297/5000000000 : ℝ)|^5007 ≤ (3679544256663/10000000000000 : ℝ)^3983
        have hw : |(2257174297/5000000000 : ℝ)|=(2257174297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_4 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-389968093/2500000000 : ℝ)*x 0 + (5187083177/10000000000 : ℝ)*x 1 + (271958631/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389968093/2500000000 : ℝ)^5007 ≤ (9674715455399/100000000000000 : ℝ)^3983 := by
    have hnat : (389968093 : ℕ)^5007*100000000000000^3983 ≤ 9674715455399^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389968093 2500000000 9674715455399 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187083177/10000000000 : ℝ)^5007 ≤ (43815933327799/100000000000000 : ℝ)^3983 := by
    have hnat : (5187083177 : ℕ)^5007*100000000000000^3983 ≤ 43815933327799^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187083177 10000000000 43815933327799 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271958631/500000000 : ℝ)^5007 ≤ (2906834449783/6250000000000 : ℝ)^3983 := by
    have hnat : (271958631 : ℕ)^5007*6250000000000^3983 ≤ 2906834449783^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271958631 500000000 2906834449783 6250000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389968093/2500000000 : ℝ), (5187083177/10000000000 : ℝ), (271958631/500000000 : ℝ)] ![(9674715455399/100000000000000 : ℝ), (43815933327799/100000000000000 : ℝ), (2906834449783/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389968093/2500000000 : ℝ)|^5007 ≤ (9674715455399/100000000000000 : ℝ)^3983
        have hw : |(-389968093/2500000000 : ℝ)|=(389968093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187083177/10000000000 : ℝ)|^5007 ≤ (43815933327799/100000000000000 : ℝ)^3983
        have hw : |(5187083177/10000000000 : ℝ)|=(5187083177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271958631/500000000 : ℝ)|^5007 ≤ (2906834449783/6250000000000 : ℝ)^3983
        have hw : |(271958631/500000000 : ℝ)|=(271958631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_5 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275849761/10000000000 : ℝ)*x 0 + (-1437452399/10000000000 : ℝ)*x 1 + (5439172631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275849761/10000000000 : ℝ)^5007 ≤ (11190148565099/25000000000000 : ℝ)^3983 := by
    have hnat : (5275849761 : ℕ)^5007*25000000000000^3983 ≤ 11190148565099^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275849761 10000000000 11190148565099 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1437452399/10000000000 : ℝ)^5007 ≤ (8730054413553/100000000000000 : ℝ)^3983 := by
    have hnat : (1437452399 : ℕ)^5007*100000000000000^3983 ≤ 8730054413553^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437452399 10000000000 8730054413553 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439172631/10000000000 : ℝ)^5007 ≤ (2906834457173/6250000000000 : ℝ)^3983 := by
    have hnat : (5439172631 : ℕ)^5007*6250000000000^3983 ≤ 2906834457173^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439172631 10000000000 2906834457173 6250000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275849761/10000000000 : ℝ), (-1437452399/10000000000 : ℝ), (5439172631/10000000000 : ℝ)] ![(11190148565099/25000000000000 : ℝ), (8730054413553/100000000000000 : ℝ), (2906834457173/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275849761/10000000000 : ℝ)|^5007 ≤ (11190148565099/25000000000000 : ℝ)^3983
        have hw : |(5275849761/10000000000 : ℝ)|=(5275849761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1437452399/10000000000 : ℝ)|^5007 ≤ (8730054413553/100000000000000 : ℝ)^3983
        have hw : |(-1437452399/10000000000 : ℝ)|=(1437452399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439172631/10000000000 : ℝ)|^5007 ≤ (2906834457173/6250000000000 : ℝ)^3983
        have hw : |(5439172631/10000000000 : ℝ)|=(5439172631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_6 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275849777/10000000000 : ℝ)*x 0 + (679896577/1250000000 : ℝ)*x 1 + (-1437452397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275849777/10000000000 : ℝ)^5007 ≤ (44760594431039/100000000000000 : ℝ)^3983 := by
    have hnat : (5275849777 : ℕ)^5007*100000000000000^3983 ≤ 44760594431039^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275849777 10000000000 44760594431039 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679896577/1250000000 : ℝ)^5007 ≤ (46509351153531/100000000000000 : ℝ)^3983 := by
    have hnat : (679896577 : ℕ)^5007*100000000000000^3983 ≤ 46509351153531^3983*1250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679896577 1250000000 46509351153531 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437452397/10000000000 : ℝ)^5007 ≤ (2182513599571/25000000000000 : ℝ)^3983 := by
    have hnat : (1437452397 : ℕ)^5007*25000000000000^3983 ≤ 2182513599571^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437452397 10000000000 2182513599571 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275849777/10000000000 : ℝ), (679896577/1250000000 : ℝ), (-1437452397/10000000000 : ℝ)] ![(44760594431039/100000000000000 : ℝ), (46509351153531/100000000000000 : ℝ), (2182513599571/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275849777/10000000000 : ℝ)|^5007 ≤ (44760594431039/100000000000000 : ℝ)^3983
        have hw : |(5275849777/10000000000 : ℝ)|=(5275849777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679896577/1250000000 : ℝ)|^5007 ≤ (46509351153531/100000000000000 : ℝ)^3983
        have hw : |(679896577/1250000000 : ℝ)|=(679896577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1437452397/10000000000 : ℝ)|^5007 ≤ (2182513599571/25000000000000 : ℝ)^3983
        have hw : |(-1437452397/10000000000 : ℝ)|=(1437452397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s3_7 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166573761/400000000 : ℝ)*x 0 + (225457343/500000000 : ℝ)*x 1 + (767763651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166573761/400000000 : ℝ)^5007 ≤ (33245650113067/100000000000000 : ℝ)^3983 := by
    have hnat : (166573761 : ℕ)^5007*100000000000000^3983 ≤ 33245650113067^3983*400000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166573761 400000000 33245650113067 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225457343/500000000 : ℝ)^5007 ≤ (18371076019923/50000000000000 : ℝ)^3983 := by
    have hnat : (225457343 : ℕ)^5007*50000000000000^3983 ≤ 18371076019923^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225457343 500000000 18371076019923 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767763651/2000000000 : ℝ)^5007 ≤ (3751524729359/12500000000000 : ℝ)^3983 := by
    have hnat : (767763651 : ℕ)^5007*12500000000000^3983 ≤ 3751524729359^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767763651 2000000000 3751524729359 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166573761/400000000 : ℝ), (225457343/500000000 : ℝ), (767763651/2000000000 : ℝ)] ![(33245650113067/100000000000000 : ℝ), (18371076019923/50000000000000 : ℝ), (3751524729359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166573761/400000000 : ℝ)|^5007 ≤ (33245650113067/100000000000000 : ℝ)^3983
        have hw : |(166573761/400000000 : ℝ)|=(166573761/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225457343/500000000 : ℝ)|^5007 ≤ (18371076019923/50000000000000 : ℝ)^3983
        have hw : |(225457343/500000000 : ℝ)|=(225457343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(767763651/2000000000 : ℝ)|^5007 ≤ (3751524729359/12500000000000 : ℝ)^3983
        have hw : |(767763651/2000000000 : ℝ)|=(767763651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1672_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1347/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8113/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1073/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1073/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1073/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1073/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1073/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1073/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1073/10000 : ℝ) ^ (5003/1024 : ℝ) ≤ (917762206321431/50000000000000000000 : ℝ) := by
    have hpowers : (1073/10000 : ℝ)^5003 ≤ (917762206321431/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1073 : ℕ)^5003*50000000000000000000^1024 ≤ 917762206321431^1024*10000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1073 10000 917762206321431 50000000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1073/10000 : ℝ)) (X := (917762206321431/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16277/100000 : ℝ) ^ (5003/1024 : ℝ) ≤ (3514759509550017/25000000000000000000 : ℝ) := by
    have hpowers : (16277/100000 : ℝ)^5003 ≤ (3514759509550017/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16277 : ℕ)^5003*25000000000000000000^1024 ≤ 3514759509550017^1024*100000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16277 100000 3514759509550017 25000000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16277/100000 : ℝ)) (X := (3514759509550017/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000917762206321431/25000000000000000000 : ℝ) ≤ (5000037568450139/5000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (25000917762206321431/25000000000000000000 : ℝ)^1024 ≤ (5000037568450139/5000000000000000 : ℝ)^5003 := by
      have hnat : (25000917762206321431 : ℕ)^1024*5000000000000000^5003 ≤ 5000037568450139^5003*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000917762206321431 25000000000000000000 5000037568450139 5000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000037568450139/5000000000000000 : ℝ)) (X := (25000917762206321431/25000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001589456245084293/10000000000000000000 : ℝ) ≤ (2500081326220747/2500000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (10001589456245084293/10000000000000000000 : ℝ)^1024 ≤ (2500081326220747/2500000000000000 : ℝ)^5003 := by
      have hnat : (10001589456245084293 : ℕ)^1024*2500000000000000^5003 ≤ 2500081326220747^5003*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001589456245084293 10000000000000000000 2500081326220747 2500000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500081326220747/2500000000000000 : ℝ)) (X := (10001589456245084293/10000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503514759509550017/12500000000000000000 : ℝ) ≤ (5000287736432849/5000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (12503514759509550017/12500000000000000000 : ℝ)^1024 ≤ (5000287736432849/5000000000000000 : ℝ)^5003 := by
      have hnat : (12503514759509550017 : ℕ)^1024*5000000000000000^5003 ≤ 5000287736432849^5003*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503514759509550017 12500000000000000000 5000287736432849 5000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000287736432849/5000000000000000 : ℝ)) (X := (12503514759509550017/12500000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(917762206321431/50000000000000000000 : ℝ) ≤ ((9244174696579480911/9245000000000000000 : ℝ)+2*(8338932757/18490000000000 : ℝ)*(1073/10000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (9244174696579480911/9245000000000000000 : ℝ)+2*(8338932757/18490000000000 : ℝ)*(1073/10000 : ℝ)=(5000037568450139/5000000000000000 : ℝ) by norm_num, show 1+2*(917762206321431/50000000000000000000 : ℝ)=(25000917762206321431/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3514759509550017/25000000000000000000 : ℝ)+(917762206321431/50000000000000000000 : ℝ) ≤ ((9244174696579480911/9245000000000000000 : ℝ)+(8338932757/18490000000000 : ℝ)*((16277/100000 : ℝ)+(1073/10000 : ℝ)))^(5003/1024 : ℝ) := by
    rw [show (9244174696579480911/9245000000000000000 : ℝ)+(8338932757/18490000000000 : ℝ)*((16277/100000 : ℝ)+(1073/10000 : ℝ))=(2500081326220747/2500000000000000 : ℝ) by norm_num, show 1+(3514759509550017/25000000000000000000 : ℝ)+(917762206321431/50000000000000000000 : ℝ)=(10001589456245084293/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3514759509550017/25000000000000000000 : ℝ) ≤ ((9244174696579480911/9245000000000000000 : ℝ)+2*(8338932757/18490000000000 : ℝ)*(16277/100000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (9244174696579480911/9245000000000000000 : ℝ)+2*(8338932757/18490000000000 : ℝ)*(16277/100000 : ℝ)=(5000287736432849/5000000000000000 : ℝ) by norm_num, show 1+2*(3514759509550017/25000000000000000000 : ℝ)=(12503514759509550017/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9244174696579480911/9245000000000000000 : ℝ)*(X 1 0+X 2 0)+(8338932757/18490000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (1073/10000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (9244174696579480911/9245000000000000000 : ℝ)) (alpha := (8338932757/18490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9244174696579480911/9245000000000000000 : ℝ)*(X 0 1+X 2 1)+(8338932757/18490000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (1073/10000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (9244174696579480911/9245000000000000000 : ℝ)) (alpha := (8338932757/18490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9244174696579480911/9245000000000000000 : ℝ)*(X 0 2+X 1 2)+(8338932757/18490000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (1073/10000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (9244174696579480911/9245000000000000000 : ℝ)) (alpha := (8338932757/18490000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1559810977/10000000000 : ℝ)*X 0 0+(108822989/200000000 : ℝ)*X 0 1+(1296281743/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344403721/10000000000 : ℝ)*X 1 0+(-67659921/400000000 : ℝ)*X 1 1+(2592563497/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344403723/10000000000 : ℝ)*X 2 0+(1296281741/2500000000 : ℝ)*X 2 1+(-1691498063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4164180797/10000000000 : ℝ)*X 0 0+(95839043/250000000 : ℝ)*X 0 1+(2257174297/5000000000 : ℝ)*X 0 2+(4164180797/10000000000 : ℝ)*X 1 0+(95839043/250000000 : ℝ)*X 1 1+(2257174297/5000000000 : ℝ)*X 1 2+(4164180797/10000000000 : ℝ)*X 2 0+(95839043/250000000 : ℝ)*X 2 1+(2257174297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-389968093/2500000000 : ℝ)*X 0 0+(5187083177/10000000000 : ℝ)*X 0 1+(271958631/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275849761/10000000000 : ℝ)*X 1 0+(-1437452399/10000000000 : ℝ)*X 1 1+(5439172631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5275849777/10000000000 : ℝ)*X 2 0+(679896577/1250000000 : ℝ)*X 2 1+(-1437452397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((166573761/400000000 : ℝ)*X 0 0+(225457343/500000000 : ℝ)*X 0 1+(767763651/2000000000 : ℝ)*X 0 2+(166573761/400000000 : ℝ)*X 1 0+(225457343/500000000 : ℝ)*X 1 1+(767763651/2000000000 : ℝ)*X 1 2+(166573761/400000000 : ℝ)*X 2 0+(225457343/500000000 : ℝ)*X 2 1+(767763651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146500849528747342414290123/46225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29669773/6250000000000 : ℝ)*(base19) + (22021663/5000000000000 : ℝ)*(base23) + (19103461/100000000000000 : ℝ)*(lower2) + (45569761/50000000000000 : ℝ)*(upper3) + (35221423/100000000000000 : ℝ)*(upper5) + (268740638721277/10000000000000 : ℝ)*(major0) + (268740638721277/10000000000000 : ℝ)*(major1) + (268740638721277/10000000000000 : ℝ)*(major2) + (1952956892176733/50000000000000 : ℝ)*(sp0) + (3905919057556983/100000000000000 : ℝ)*(sp1) + (3905919091840091/100000000000000 : ℝ)*(sp2) + (1468890531690681/100000000000000 : ℝ)*(sp3) + (1149583977/20000000000000 : ℝ)*(sp4) + (2604818201/100000000000000 : ℝ)*(sp7) + (734446568254441/50000000000000 : ℝ)*(f.failure) + (3905919532273351/100000000000000 : ℝ)*(f.sum) + (240484576703/92450000000000000000000000 : ℝ)*base65 + (350218573820706653/92450000000000000000000000000000 : ℝ)*base68 + (536260044355906653/92450000000000000000000000000000 : ℝ)*base70 + (618294636970706653/92450000000000000000000000000000 : ℝ)*base72 + (115490763227/369800000000000000000000000 : ℝ)*base73 + (874873465208406653/92450000000000000000000000000000 : ℝ)*base76 + (446922387843206653/92450000000000000000000000000000 : ℝ)*base78 + (337418444109256653/92450000000000000000000000000000 : ℝ)*base80 + (48870274049/115562500000000000000000000 : ℝ)*base82 + (224417/125000000000000000000 : ℝ)*base90 + (224417/125000000000000000000 : ℝ)*base92 + (224417/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122357766105634924122745869/23112500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (758569769/100000000000000 : ℝ)*(base19) + (414462733/50000000000000 : ℝ)*(base23) + (111322699/100000000000000 : ℝ)*(upper3) + (163619/625000000000 : ℝ)*(lower4) + (111557789/100000000000000 : ℝ)*(upper5) + (136466284611669/5000000000000 : ℝ)*(major0) + (136466284611669/5000000000000 : ℝ)*(major1) + (136466284611669/5000000000000 : ℝ)*(major2) + (2352051881/25000000000000 : ℝ)*(sp1) + (10078136889/100000000000000 : ℝ)*(sp2) + (1983422826568283/50000000000000 : ℝ)*(sp4) + (495854435794909/12500000000000 : ℝ)*(sp5) + (396683474607421/10000000000000 : ℝ)*(sp6) + (1491805554863241/100000000000000 : ℝ)*(sp7) + (1491805554863241/100000000000000 : ℝ)*(f.failure) + (1983422826568283/50000000000000 : ℝ)*(f.sum) + (3983795587257/1849000000000000000000000000 : ℝ)*base66 + (158862476343400459/46225000000000000000000000000000 : ℝ)*base67 + (401656333540475459/46225000000000000000000000000000 : ℝ)*base69 + (251627158624125459/46225000000000000000000000000000 : ℝ)*base71 + (650252434719/231125000000000000000000000 : ℝ)*base73 + (538770566384675459/46225000000000000000000000000000 : ℝ)*base75 + (261701521980900459/46225000000000000000000000000000 : ℝ)*base77 + (260989302250250459/46225000000000000000000000000000 : ℝ)*base79 + (2835465300049/924500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1930017/250000000000000000000 : ℝ)*base90 + (1930017/250000000000000000000 : ℝ)*base92 + (1930017/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1672_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1672_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1672_s4_0 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-389959451/2500000000 : ℝ)*x 0 + (1360252973/2500000000 : ℝ)*x 1 + (324077909/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (389959451/2500000000 : ℝ)^5007 ≤ (9674445936369/100000000000000 : ℝ)^3983 := by
    have hnat : (389959451 : ℕ)^5007*100000000000000^3983 ≤ 9674445936369^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389959451 2500000000 9674445936369 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360252973/2500000000 : ℝ)^5007 ≤ (23264561346911/50000000000000 : ℝ)^3983 := by
    have hnat : (1360252973 : ℕ)^5007*50000000000000^3983 ≤ 23264561346911^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360252973 2500000000 23264561346911 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324077909/625000000 : ℝ)^5007 ≤ (21898215672839/50000000000000 : ℝ)^3983 := by
    have hnat : (324077909 : ℕ)^5007*50000000000000^3983 ≤ 21898215672839^3983*625000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324077909 625000000 21898215672839 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-389959451/2500000000 : ℝ), (1360252973/2500000000 : ℝ), (324077909/625000000 : ℝ)] ![(9674445936369/100000000000000 : ℝ), (23264561346911/50000000000000 : ℝ), (21898215672839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-389959451/2500000000 : ℝ)|^5007 ≤ (9674445936369/100000000000000 : ℝ)^3983
        have hw : |(-389959451/2500000000 : ℝ)|=(389959451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360252973/2500000000 : ℝ)|^5007 ≤ (23264561346911/50000000000000 : ℝ)^3983
        have hw : |(1360252973/2500000000 : ℝ)|=(1360252973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(324077909/625000000 : ℝ)|^5007 ≤ (21898215672839/50000000000000 : ℝ)^3983
        have hw : |(324077909/625000000 : ℝ)|=(324077909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_1 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213774639/400000000 : ℝ)*x 0 + (-845694537/5000000000 : ℝ)*x 1 + (2592623361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213774639/400000000 : ℝ)^5007 ≤ (22746276127409/50000000000000 : ℝ)^3983 := by
    have hnat : (213774639 : ℕ)^5007*50000000000000^3983 ≤ 22746276127409^3983*400000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213774639 400000000 22746276127409 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845694537/5000000000 : ℝ)^5007 ≤ (1338876812589/12500000000000 : ℝ)^3983 := by
    have hnat : (845694537 : ℕ)^5007*12500000000000^3983 ≤ 1338876812589^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845694537 5000000000 1338876812589 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592623361/5000000000 : ℝ)^5007 ≤ (8759286647131/20000000000000 : ℝ)^3983 := by
    have hnat : (2592623361 : ℕ)^5007*20000000000000^3983 ≤ 8759286647131^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592623361 5000000000 8759286647131 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213774639/400000000 : ℝ), (-845694537/5000000000 : ℝ), (2592623361/5000000000 : ℝ)] ![(22746276127409/50000000000000 : ℝ), (1338876812589/12500000000000 : ℝ), (8759286647131/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213774639/400000000 : ℝ)|^5007 ≤ (22746276127409/50000000000000 : ℝ)^3983
        have hw : |(213774639/400000000 : ℝ)|=(213774639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-845694537/5000000000 : ℝ)|^5007 ≤ (1338876812589/12500000000000 : ℝ)^3983
        have hw : |(-845694537/5000000000 : ℝ)|=(845694537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592623361/5000000000 : ℝ)|^5007 ≤ (8759286647131/20000000000000 : ℝ)^3983
        have hw : |(2592623361/5000000000 : ℝ)|=(2592623361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_2 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336091463/2500000000 : ℝ)*x 0 + (324077937/625000000 : ℝ)*x 1 + (-1691388879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336091463/2500000000 : ℝ)^5007 ≤ (9098510187727/20000000000000 : ℝ)^3983 := by
    have hnat : (1336091463 : ℕ)^5007*20000000000000^3983 ≤ 9098510187727^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336091463 2500000000 9098510187727 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324077937/625000000 : ℝ)^5007 ≤ (1751857444099/4000000000000 : ℝ)^3983 := by
    have hnat : (324077937 : ℕ)^5007*4000000000000^3983 ≤ 1751857444099^3983*625000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324077937 625000000 1751857444099 4000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691388879/10000000000 : ℝ)^5007 ≤ (2677753237091/25000000000000 : ℝ)^3983 := by
    have hnat : (1691388879 : ℕ)^5007*25000000000000^3983 ≤ 2677753237091^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691388879 10000000000 2677753237091 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336091463/2500000000 : ℝ), (324077937/625000000 : ℝ), (-1691388879/10000000000 : ℝ)] ![(9098510187727/20000000000000 : ℝ), (1751857444099/4000000000000 : ℝ), (2677753237091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336091463/2500000000 : ℝ)|^5007 ≤ (9098510187727/20000000000000 : ℝ)^3983
        have hw : |(1336091463/2500000000 : ℝ)|=(1336091463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324077937/625000000 : ℝ)|^5007 ≤ (1751857444099/4000000000000 : ℝ)^3983
        have hw : |(324077937/625000000 : ℝ)|=(324077937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1691388879/10000000000 : ℝ)|^5007 ≤ (2677753237091/25000000000000 : ℝ)^3983
        have hw : |(-1691388879/10000000000 : ℝ)|=(1691388879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_3 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (104104969/250000000 : ℝ)*x 0 + (958475499/2500000000 : ℝ)*x 1 + (4514004721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104104969/250000000 : ℝ)^5007 ≤ (33244192257311/100000000000000 : ℝ)^3983 := by
    have hnat : (104104969 : ℕ)^5007*100000000000000^3983 ≤ 33244192257311^3983*250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104104969 250000000 33244192257311 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958475499/2500000000 : ℝ)^5007 ≤ (3745486066587/12500000000000 : ℝ)^3983 := by
    have hnat : (958475499 : ℕ)^5007*12500000000000^3983 ≤ 3745486066587^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958475499 2500000000 3745486066587 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514004721/10000000000 : ℝ)^5007 ≤ (18395959591027/50000000000000 : ℝ)^3983 := by
    have hnat : (4514004721 : ℕ)^5007*50000000000000^3983 ≤ 18395959591027^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514004721 10000000000 18395959591027 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104104969/250000000 : ℝ), (958475499/2500000000 : ℝ), (4514004721/10000000000 : ℝ)] ![(33244192257311/100000000000000 : ℝ), (3745486066587/12500000000000 : ℝ), (18395959591027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104104969/250000000 : ℝ)|^5007 ≤ (33244192257311/100000000000000 : ℝ)^3983
        have hw : |(104104969/250000000 : ℝ)|=(104104969/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958475499/2500000000 : ℝ)|^5007 ≤ (3745486066587/12500000000000 : ℝ)^3983
        have hw : |(958475499/2500000000 : ℝ)|=(958475499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514004721/10000000000 : ℝ)|^5007 ≤ (18395959591027/50000000000000 : ℝ)^3983
        have hw : |(4514004721/10000000000 : ℝ)|=(4514004721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_4 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-779949597/5000000000 : ℝ)*x 0 + (5187199533/10000000000 : ℝ)*x 1 + (5439038219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (779949597/5000000000 : ℝ)^5007 ≤ (2418731145411/25000000000000 : ℝ)^3983 := by
    have hnat : (779949597 : ℕ)^5007*25000000000000^3983 ≤ 2418731145411^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779949597 5000000000 2418731145411 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187199533/10000000000 : ℝ)^5007 ≤ (21908584447221/50000000000000 : ℝ)^3983 := by
    have hnat : (5187199533 : ℕ)^5007*50000000000000^3983 ≤ 21908584447221^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187199533 10000000000 21908584447221 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439038219/10000000000 : ℝ)^5007 ≤ (46507906502609/100000000000000 : ℝ)^3983 := by
    have hnat : (5439038219 : ℕ)^5007*100000000000000^3983 ≤ 46507906502609^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439038219 10000000000 46507906502609 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-779949597/5000000000 : ℝ), (5187199533/10000000000 : ℝ), (5439038219/10000000000 : ℝ)] ![(2418731145411/25000000000000 : ℝ), (21908584447221/50000000000000 : ℝ), (46507906502609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-779949597/5000000000 : ℝ)|^5007 ≤ (2418731145411/25000000000000 : ℝ)^3983
        have hw : |(-779949597/5000000000 : ℝ)|=(779949597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187199533/10000000000 : ℝ)|^5007 ≤ (21908584447221/50000000000000 : ℝ)^3983
        have hw : |(5187199533/10000000000 : ℝ)|=(5187199533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439038219/10000000000 : ℝ)|^5007 ≤ (46507906502609/100000000000000 : ℝ)^3983
        have hw : |(5439038219/10000000000 : ℝ)|=(5439038219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_5 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275881489/10000000000 : ℝ)*x 0 + (-718798071/5000000000 : ℝ)*x 1 + (2719519527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275881489/10000000000 : ℝ)^5007 ≤ (44760932647451/100000000000000 : ℝ)^3983 := by
    have hnat : (5275881489 : ℕ)^5007*100000000000000^3983 ≤ 44760932647451^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275881489 10000000000 44760932647451 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718798071/5000000000 : ℝ)^5007 ≤ (8731151859277/100000000000000 : ℝ)^3983 := by
    have hnat : (718798071 : ℕ)^5007*100000000000000^3983 ≤ 8731151859277^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718798071 5000000000 8731151859277 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719519527/5000000000 : ℝ)^5007 ≤ (5813489434763/12500000000000 : ℝ)^3983 := by
    have hnat : (2719519527 : ℕ)^5007*12500000000000^3983 ≤ 5813489434763^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719519527 5000000000 5813489434763 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275881489/10000000000 : ℝ), (-718798071/5000000000 : ℝ), (2719519527/5000000000 : ℝ)] ![(44760932647451/100000000000000 : ℝ), (8731151859277/100000000000000 : ℝ), (5813489434763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275881489/10000000000 : ℝ)|^5007 ≤ (44760932647451/100000000000000 : ℝ)^3983
        have hw : |(5275881489/10000000000 : ℝ)|=(5275881489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-718798071/5000000000 : ℝ)|^5007 ≤ (8731151859277/100000000000000 : ℝ)^3983
        have hw : |(-718798071/5000000000 : ℝ)|=(718798071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719519527/5000000000 : ℝ)|^5007 ≤ (5813489434763/12500000000000 : ℝ)^3983
        have hw : |(2719519527/5000000000 : ℝ)|=(2719519527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_6 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318970069/2500000000 : ℝ)*x 0 + (5439040127/10000000000 : ℝ)*x 1 + (-1437596327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318970069/2500000000 : ℝ)^5007 ≤ (44760919710493/100000000000000 : ℝ)^3983 := by
    have hnat : (1318970069 : ℕ)^5007*100000000000000^3983 ≤ 44760919710493^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318970069 2500000000 44760919710493 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439040127/10000000000 : ℝ)^5007 ≤ (23253963505943/50000000000000 : ℝ)^3983 := by
    have hnat : (5439040127 : ℕ)^5007*50000000000000^3983 ≤ 23253963505943^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439040127 10000000000 23253963505943 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437596327/10000000000 : ℝ)^5007 ≤ (8731153271729/100000000000000 : ℝ)^3983 := by
    have hnat : (1437596327 : ℕ)^5007*100000000000000^3983 ≤ 8731153271729^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437596327 10000000000 8731153271729 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318970069/2500000000 : ℝ), (5439040127/10000000000 : ℝ), (-1437596327/10000000000 : ℝ)] ![(44760919710493/100000000000000 : ℝ), (23253963505943/50000000000000 : ℝ), (8731153271729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318970069/2500000000 : ℝ)|^5007 ≤ (44760919710493/100000000000000 : ℝ)^3983
        have hw : |(1318970069/2500000000 : ℝ)|=(1318970069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439040127/10000000000 : ℝ)|^5007 ≤ (23253963505943/50000000000000 : ℝ)^3983
        have hw : |(5439040127/10000000000 : ℝ)|=(5439040127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1437596327/10000000000 : ℝ)|^5007 ≤ (8731153271729/100000000000000 : ℝ)^3983
        have hw : |(-1437596327/10000000000 : ℝ)|=(1437596327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_s4_7 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2082181239/5000000000 : ℝ)*x 0 + (901762483/2000000000 : ℝ)*x 1 + (1919573989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082181239/5000000000 : ℝ)^5007 ≤ (33245835305289/100000000000000 : ℝ)^3983 := by
    have hnat : (2082181239 : ℕ)^5007*100000000000000^3983 ≤ 33245835305289^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082181239 5000000000 33245835305289 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901762483/2000000000 : ℝ)^5007 ≤ (18369363135477/50000000000000 : ℝ)^3983 := by
    have hnat : (901762483 : ℕ)^5007*50000000000000^3983 ≤ 18369363135477^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901762483 2000000000 18369363135477 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919573989/5000000000 : ℝ)^5007 ≤ (30015438406101/100000000000000 : ℝ)^3983 := by
    have hnat : (1919573989 : ℕ)^5007*100000000000000^3983 ≤ 30015438406101^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919573989 5000000000 30015438406101 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082181239/5000000000 : ℝ), (901762483/2000000000 : ℝ), (1919573989/5000000000 : ℝ)] ![(33245835305289/100000000000000 : ℝ), (18369363135477/50000000000000 : ℝ), (30015438406101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082181239/5000000000 : ℝ)|^5007 ≤ (33245835305289/100000000000000 : ℝ)^3983
        have hw : |(2082181239/5000000000 : ℝ)|=(2082181239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901762483/2000000000 : ℝ)|^5007 ≤ (18369363135477/50000000000000 : ℝ)^3983
        have hw : |(901762483/2000000000 : ℝ)|=(901762483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1919573989/5000000000 : ℝ)|^5007 ≤ (30015438406101/100000000000000 : ℝ)^3983
        have hw : |(1919573989/5000000000 : ℝ)|=(1919573989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1672_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5389/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16223/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8113/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1347/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8113/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1347/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8113/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1347/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8113/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1347/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8113/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1347/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8113/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1347/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1347/12500 : ℝ) ^ (5003/1024 : ℝ) ≤ (117143234403071/6250000000000000000 : ℝ) := by
    have hpowers : (1347/12500 : ℝ)^5003 ≤ (117143234403071/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1347 : ℕ)^5003*6250000000000000000^1024 ≤ 117143234403071^1024*12500^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1347 12500 117143234403071 6250000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1347/12500 : ℝ)) (X := (117143234403071/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8113/50000 : ℝ) ^ (5003/1024 : ℝ) ≤ (13845124575754529/100000000000000000000 : ℝ) := by
    have hpowers : (8113/50000 : ℝ)^5003 ≤ (13845124575754529/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8113 : ℕ)^5003*100000000000000000000^1024 ≤ 13845124575754529^1024*50000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8113 50000 13845124575754529 100000000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8113/50000 : ℝ)) (X := (13845124575754529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125117143234403071/3125000000000000000 : ℝ) ≤ (5000038361905719/5000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (3125117143234403071/3125000000000000000 : ℝ)^1024 ≤ (5000038361905719/5000000000000000 : ℝ)^5003 := by
      have hnat : (3125117143234403071 : ℕ)^1024*5000000000000000^5003 ≤ 5000038361905719^5003*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125117143234403071 3125000000000000000 5000038361905719 5000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038361905719/5000000000000000 : ℝ)) (X := (3125117143234403071/3125000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003143883265240733/20000000000000000000 : ℝ) ≤ (1000032172049187/1000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (20003143883265240733/20000000000000000000 : ℝ)^1024 ≤ (1000032172049187/1000000000000000 : ℝ)^5003 := by
      have hnat : (20003143883265240733 : ℕ)^1024*1000000000000000^5003 ≤ 1000032172049187^5003*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003143883265240733 20000000000000000000 1000032172049187 1000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000032172049187/1000000000000000 : ℝ)) (X := (20003143883265240733/20000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013845124575754529/50000000000000000000 : ℝ) ≤ (5000283358586151/5000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (50013845124575754529/50000000000000000000 : ℝ)^1024 ≤ (5000283358586151/5000000000000000 : ℝ)^5003 := by
      have hnat : (50013845124575754529 : ℕ)^1024*5000000000000000^5003 ≤ 5000283358586151^5003*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013845124575754529 50000000000000000000 5000283358586151 5000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000283358586151/5000000000000000 : ℝ)) (X := (50013845124575754529/50000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(117143234403071/6250000000000000000 : ℝ) ≤ ((13623784494078916659/13625000000000000000 : ℝ)+2*(15312292527/34062500000000 : ℝ)*(1347/12500 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (13623784494078916659/13625000000000000000 : ℝ)+2*(15312292527/34062500000000 : ℝ)*(1347/12500 : ℝ)=(5000038361905719/5000000000000000 : ℝ) by norm_num, show 1+2*(117143234403071/6250000000000000000 : ℝ)=(3125117143234403071/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13845124575754529/100000000000000000000 : ℝ)+(117143234403071/6250000000000000000 : ℝ) ≤ ((13623784494078916659/13625000000000000000 : ℝ)+(15312292527/34062500000000 : ℝ)*((8113/50000 : ℝ)+(1347/12500 : ℝ)))^(5003/1024 : ℝ) := by
    rw [show (13623784494078916659/13625000000000000000 : ℝ)+(15312292527/34062500000000 : ℝ)*((8113/50000 : ℝ)+(1347/12500 : ℝ))=(1000032172049187/1000000000000000 : ℝ) by norm_num, show 1+(13845124575754529/100000000000000000000 : ℝ)+(117143234403071/6250000000000000000 : ℝ)=(20003143883265240733/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13845124575754529/100000000000000000000 : ℝ) ≤ ((13623784494078916659/13625000000000000000 : ℝ)+2*(15312292527/34062500000000 : ℝ)*(8113/50000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (13623784494078916659/13625000000000000000 : ℝ)+2*(15312292527/34062500000000 : ℝ)*(8113/50000 : ℝ)=(5000283358586151/5000000000000000 : ℝ) by norm_num, show 1+2*(13845124575754529/100000000000000000000 : ℝ)=(50013845124575754529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13623784494078916659/13625000000000000000 : ℝ)*(X 1 0+X 2 0)+(15312292527/34062500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (1347/12500 : ℝ)) (hi := (8113/50000 : ℝ)) (c := (13623784494078916659/13625000000000000000 : ℝ)) (alpha := (15312292527/34062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13623784494078916659/13625000000000000000 : ℝ)*(X 0 1+X 2 1)+(15312292527/34062500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (1347/12500 : ℝ)) (hi := (8113/50000 : ℝ)) (c := (13623784494078916659/13625000000000000000 : ℝ)) (alpha := (15312292527/34062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13623784494078916659/13625000000000000000 : ℝ)*(X 0 2+X 1 2)+(15312292527/34062500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (1347/12500 : ℝ)) (hi := (8113/50000 : ℝ)) (c := (13623784494078916659/13625000000000000000 : ℝ)) (alpha := (15312292527/34062500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-389959451/2500000000 : ℝ)*X 0 0+(1360252973/2500000000 : ℝ)*X 0 1+(324077909/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213774639/400000000 : ℝ)*X 1 0+(-845694537/5000000000 : ℝ)*X 1 1+(2592623361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336091463/2500000000 : ℝ)*X 2 0+(324077937/625000000 : ℝ)*X 2 1+(-1691388879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((104104969/250000000 : ℝ)*X 0 0+(958475499/2500000000 : ℝ)*X 0 1+(4514004721/10000000000 : ℝ)*X 0 2+(104104969/250000000 : ℝ)*X 1 0+(958475499/2500000000 : ℝ)*X 1 1+(4514004721/10000000000 : ℝ)*X 1 2+(104104969/250000000 : ℝ)*X 2 0+(958475499/2500000000 : ℝ)*X 2 1+(4514004721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-779949597/5000000000 : ℝ)*X 0 0+(5187199533/10000000000 : ℝ)*X 0 1+(5439038219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275881489/10000000000 : ℝ)*X 1 0+(-718798071/5000000000 : ℝ)*X 1 1+(2719519527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1318970069/2500000000 : ℝ)*X 2 0+(5439040127/10000000000 : ℝ)*X 2 1+(-1437596327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2082181239/5000000000 : ℝ)*X 0 0+(901762483/2000000000 : ℝ)*X 0 1+(1919573989/5000000000 : ℝ)*X 0 2+(2082181239/5000000000 : ℝ)*X 1 0+(901762483/2000000000 : ℝ)*X 1 1+(1919573989/5000000000 : ℝ)*X 1 2+(2082181239/5000000000 : ℝ)*X 2 0+(901762483/2000000000 : ℝ)*X 2 1+(1919573989/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143969630828684541867279/13625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63319803/5000000000000 : ℝ)*(base19) + (1037673269/100000000000000 : ℝ)*(base23) + (74146451/100000000000000 : ℝ)*(lower2) + (199390633/100000000000000 : ℝ)*(upper3) + (24831821/10000000000000 : ℝ)*(upper5) + (336265510563473/12500000000000 : ℝ)*(major0) + (336265510563473/12500000000000 : ℝ)*(major1) + (336265510563473/12500000000000 : ℝ)*(major2) + (30545705622687/781250000000 : ℝ)*(sp0) + (3909867964231489/100000000000000 : ℝ)*(sp1) + (97746704823857/2500000000000 : ℝ)*(sp2) + (1470372385451643/100000000000000 : ℝ)*(sp3) + (4727730903/25000000000000 : ℝ)*(sp4) + (1240143417/20000000000000 : ℝ)*(sp7) + (183797323271091/12500000000000 : ℝ)*(f.failure) + (3909869230627549/100000000000000 : ℝ)*(f.sum) + (22505077986797/6812500000000000000000000000 : ℝ)*base65 + (508566865180940793/170312500000000000000000000000000 : ℝ)*base68 + (1187087354184684207/170312500000000000000000000000000 : ℝ)*base69 + (349566925653434207/170312500000000000000000000000000 : ℝ)*base71 + (931857447219/13625000000000000000000000000 : ℝ)*base73 + (1173171997600309207/170312500000000000000000000000000 : ℝ)*base75 + (364733881479378293/170312500000000000000000000000000 : ℝ)*base78 + (423963390287190793/170312500000000000000000000000000 : ℝ)*base80 + (69177846139219/13625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (405467/31250000000000000000 : ℝ)*base90 + (405467/31250000000000000000 : ℝ)*base92 + (405467/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40715450826503676666650157/10644531250000000000000000000000 : ℝ) := by norm_num
    linear_combination (87800279/10000000000000 : ℝ)*(base19) + (232867087/100000000000000 : ℝ)*(base23) + (185650973/50000000000000 : ℝ)*(lower1) + (360710781/100000000000000 : ℝ)*(upper3) + (6909661/6250000000000 : ℝ)*(lower4) + (3354333/10000000000000 : ℝ)*(upper5) + (341502991457989/12500000000000 : ℝ)*(major0) + (341502991457989/12500000000000 : ℝ)*(major1) + (341502991457989/12500000000000 : ℝ)*(major2) + (4487590633/100000000000000 : ℝ)*(sp2) + (1985383683330163/50000000000000 : ℝ)*(sp4) + (794153297731507/20000000000000 : ℝ)*(sp5) + (1985381323101303/50000000000000 : ℝ)*(sp6) + (1493280369167109/100000000000000 : ℝ)*(sp7) + (1493280369167109/100000000000000 : ℝ)*(f.failure) + (1985383683330163/50000000000000 : ℝ)*(f.sum) + (34443009477629/6812500000000000000000000000 : ℝ)*base66 + (2119465237870873749/170312500000000000000000000000000 : ℝ)*base68 + (2049802146194311249/170312500000000000000000000000000 : ℝ)*base70 + (5081662815864623749/170312500000000000000000000000000 : ℝ)*base72 + (21563960374367/13625000000000000000000000000 : ℝ)*base73 + (13041354725580688751/170312500000000000000000000000000 : ℝ)*base75 + (770813974166186249/170312500000000000000000000000000 : ℝ)*base78 + (1523332169527123749/170312500000000000000000000000000 : ℝ)*base80 + (85032981589633/13625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (672067/250000000000000000000 : ℝ)*base89 + (672067/250000000000000000000 : ℝ)*base91 + (672067/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1672_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1347/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1672_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1672_box_0 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-654746071/5000000000 : ℝ)*x 0 + (5402707557/10000000000 : ℝ)*x 1 + (2701353977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654746071/5000000000 : ℝ)^5007 ≤ (3882277281837/50000000000000 : ℝ)^3983 := by
    have hnat : (654746071 : ℕ)^5007*50000000000000^3983 ≤ 3882277281837^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654746071 5000000000 3882277281837 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402707557/10000000000 : ℝ)^5007 ≤ (11529430145379/25000000000000 : ℝ)^3983 := by
    have hnat : (5402707557 : ℕ)^5007*25000000000000^3983 ≤ 11529430145379^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402707557 10000000000 11529430145379 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701353977/5000000000 : ℝ)^5007 ≤ (1152943121039/2500000000000 : ℝ)^3983 := by
    have hnat : (2701353977 : ℕ)^5007*2500000000000^3983 ≤ 1152943121039^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701353977 5000000000 1152943121039 2500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-654746071/5000000000 : ℝ), (5402707557/10000000000 : ℝ), (2701353977/5000000000 : ℝ)] ![(3882277281837/50000000000000 : ℝ), (11529430145379/25000000000000 : ℝ), (1152943121039/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-654746071/5000000000 : ℝ)|^5007 ≤ (3882277281837/50000000000000 : ℝ)^3983
        have hw : |(-654746071/5000000000 : ℝ)|=(654746071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402707557/10000000000 : ℝ)|^5007 ≤ (11529430145379/25000000000000 : ℝ)^3983
        have hw : |(5402707557/10000000000 : ℝ)|=(5402707557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701353977/5000000000 : ℝ)|^5007 ≤ (1152943121039/2500000000000 : ℝ)^3983
        have hw : |(2701353977/5000000000 : ℝ)|=(2701353977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_1 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250638539/10000000000 : ℝ)*x 0 + (-761647987/5000000000 : ℝ)*x 1 + (5402707777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250638539/10000000000 : ℝ)^5007 ≤ (44491875843707/100000000000000 : ℝ)^3983 := by
    have hnat : (5250638539 : ℕ)^5007*100000000000000^3983 ≤ 44491875843707^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250638539 10000000000 44491875843707 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (761647987/5000000000 : ℝ)^5007 ≤ (9390401206673/100000000000000 : ℝ)^3983 := by
    have hnat : (761647987 : ℕ)^5007*100000000000000^3983 ≤ 9390401206673^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761647987 5000000000 9390401206673 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402707777/10000000000 : ℝ)^5007 ≤ (23058861471123/50000000000000 : ℝ)^3983 := by
    have hnat : (5402707777 : ℕ)^5007*50000000000000^3983 ≤ 23058861471123^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402707777 10000000000 23058861471123 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250638539/10000000000 : ℝ), (-761647987/5000000000 : ℝ), (5402707777/10000000000 : ℝ)] ![(44491875843707/100000000000000 : ℝ), (9390401206673/100000000000000 : ℝ), (23058861471123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250638539/10000000000 : ℝ)|^5007 ≤ (44491875843707/100000000000000 : ℝ)^3983
        have hw : |(5250638539/10000000000 : ℝ)|=(5250638539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-761647987/5000000000 : ℝ)|^5007 ≤ (9390401206673/100000000000000 : ℝ)^3983
        have hw : |(-761647987/5000000000 : ℝ)|=(761647987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402707777/10000000000 : ℝ)|^5007 ≤ (23058861471123/50000000000000 : ℝ)^3983
        have hw : |(5402707777/10000000000 : ℝ)|=(5402707777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_2 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250636619/10000000000 : ℝ)*x 0 + (2701354709/5000000000 : ℝ)*x 1 + (-76164817/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250636619/10000000000 : ℝ)^5007 ≤ (8898371078329/20000000000000 : ℝ)^3983 := by
    have hnat : (5250636619 : ℕ)^5007*20000000000000^3983 ≤ 8898371078329^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250636619 10000000000 8898371078329 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701354709/5000000000 : ℝ)^5007 ≤ (46117740551147/100000000000000 : ℝ)^3983 := by
    have hnat : (2701354709 : ℕ)^5007*100000000000000^3983 ≤ 46117740551147^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701354709 5000000000 46117740551147 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76164817/500000000 : ℝ)^5007 ≤ (9390404042947/100000000000000 : ℝ)^3983 := by
    have hnat : (76164817 : ℕ)^5007*100000000000000^3983 ≤ 9390404042947^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76164817 500000000 9390404042947 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250636619/10000000000 : ℝ), (2701354709/5000000000 : ℝ), (-76164817/500000000 : ℝ)] ![(8898371078329/20000000000000 : ℝ), (46117740551147/100000000000000 : ℝ), (9390404042947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250636619/10000000000 : ℝ)|^5007 ≤ (8898371078329/20000000000000 : ℝ)^3983
        have hw : |(5250636619/10000000000 : ℝ)|=(5250636619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701354709/5000000000 : ℝ)|^5007 ≤ (46117740551147/100000000000000 : ℝ)^3983
        have hw : |(2701354709/5000000000 : ℝ)|=(2701354709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76164817/500000000 : ℝ)|^5007 ≤ (9390404042947/100000000000000 : ℝ)^3983
        have hw : |(-76164817/500000000 : ℝ)|=(76164817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_3 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1109910191/2500000000 : ℝ)*x 0 + (2019077761/5000000000 : ℝ)*x 1 + (4038153927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109910191/2500000000 : ℝ)^5007 ≤ (9007900085961/25000000000000 : ℝ)^3983 := by
    have hnat : (1109910191 : ℕ)^5007*25000000000000^3983 ≤ 9007900085961^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109910191 2500000000 9007900085961 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2019077761/5000000000 : ℝ)^5007 ≤ (3198420775933/10000000000000 : ℝ)^3983 := by
    have hnat : (2019077761 : ℕ)^5007*10000000000000^3983 ≤ 3198420775933^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019077761 5000000000 3198420775933 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4038153927/10000000000 : ℝ)^5007 ≤ (31984191878233/100000000000000 : ℝ)^3983 := by
    have hnat : (4038153927 : ℕ)^5007*100000000000000^3983 ≤ 31984191878233^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038153927 10000000000 31984191878233 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1109910191/2500000000 : ℝ), (2019077761/5000000000 : ℝ), (4038153927/10000000000 : ℝ)] ![(9007900085961/25000000000000 : ℝ), (3198420775933/10000000000000 : ℝ), (31984191878233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1109910191/2500000000 : ℝ)|^5007 ≤ (9007900085961/25000000000000 : ℝ)^3983
        have hw : |(1109910191/2500000000 : ℝ)|=(1109910191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2019077761/5000000000 : ℝ)|^5007 ≤ (3198420775933/10000000000000 : ℝ)^3983
        have hw : |(2019077761/5000000000 : ℝ)|=(2019077761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4038153927/10000000000 : ℝ)|^5007 ≤ (31984191878233/100000000000000 : ℝ)^3983
        have hw : |(4038153927/10000000000 : ℝ)|=(4038153927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_4 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-28448491/156250000 : ℝ)*x 0 + (5216149643/10000000000 : ℝ)*x 1 + (5216149627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28448491/156250000 : ℝ)^5007 ≤ (2350077297549/20000000000000 : ℝ)^3983 := by
    have hnat : (28448491 : ℕ)^5007*20000000000000^3983 ≤ 2350077297549^3983*156250000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28448491 156250000 2350077297549 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216149643/10000000000 : ℝ)^5007 ≤ (44124806835291/100000000000000 : ℝ)^3983 := by
    have hnat : (5216149643 : ℕ)^5007*100000000000000^3983 ≤ 44124806835291^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216149643 10000000000 44124806835291 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216149627/10000000000 : ℝ)^5007 ≤ (8824961333029/20000000000000 : ℝ)^3983 := by
    have hnat : (5216149627 : ℕ)^5007*20000000000000^3983 ≤ 8824961333029^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216149627 10000000000 8824961333029 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-28448491/156250000 : ℝ), (5216149643/10000000000 : ℝ), (5216149627/10000000000 : ℝ)] ![(2350077297549/20000000000000 : ℝ), (44124806835291/100000000000000 : ℝ), (8824961333029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-28448491/156250000 : ℝ)|^5007 ≤ (2350077297549/20000000000000 : ℝ)^3983
        have hw : |(-28448491/156250000 : ℝ)|=(28448491/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216149643/10000000000 : ℝ)|^5007 ≤ (44124806835291/100000000000000 : ℝ)^3983
        have hw : |(5216149643/10000000000 : ℝ)|=(5216149643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216149627/10000000000 : ℝ)|^5007 ≤ (8824961333029/20000000000000 : ℝ)^3983
        have hw : |(5216149627/10000000000 : ℝ)|=(5216149627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_5 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075663029/2000000000 : ℝ)*x 0 + (-801939597/5000000000 : ℝ)*x 1 + (5216149823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075663029/2000000000 : ℝ)^5007 ≤ (45856127653317/100000000000000 : ℝ)^3983 := by
    have hnat : (1075663029 : ℕ)^5007*100000000000000^3983 ≤ 45856127653317^3983*2000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075663029 2000000000 45856127653317 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801939597/5000000000 : ℝ)^5007 ≤ (10019063583163/100000000000000 : ℝ)^3983 := by
    have hnat : (801939597 : ℕ)^5007*100000000000000^3983 ≤ 10019063583163^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801939597 5000000000 10019063583163 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216149823/10000000000 : ℝ)^5007 ≤ (22062404374713/50000000000000 : ℝ)^3983 := by
    have hnat : (5216149823 : ℕ)^5007*50000000000000^3983 ≤ 22062404374713^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216149823 10000000000 22062404374713 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075663029/2000000000 : ℝ), (-801939597/5000000000 : ℝ), (5216149823/10000000000 : ℝ)] ![(45856127653317/100000000000000 : ℝ), (10019063583163/100000000000000 : ℝ), (22062404374713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075663029/2000000000 : ℝ)|^5007 ≤ (45856127653317/100000000000000 : ℝ)^3983
        have hw : |(1075663029/2000000000 : ℝ)|=(1075663029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-801939597/5000000000 : ℝ)|^5007 ≤ (10019063583163/100000000000000 : ℝ)^3983
        have hw : |(-801939597/5000000000 : ℝ)|=(801939597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216149823/10000000000 : ℝ)|^5007 ≤ (22062404374713/50000000000000 : ℝ)^3983
        have hw : |(5216149823/10000000000 : ℝ)|=(5216149823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_6 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378315401/10000000000 : ℝ)*x 0 + (2608074721/5000000000 : ℝ)*x 1 + (-5012123/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378315401/10000000000 : ℝ)^5007 ≤ (9171226079431/20000000000000 : ℝ)^3983 := by
    have hnat : (5378315401 : ℕ)^5007*20000000000000^3983 ≤ 9171226079431^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378315401 10000000000 9171226079431 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608074721/5000000000 : ℝ)^5007 ≤ (551560058723/1250000000000 : ℝ)^3983 := by
    have hnat : (2608074721 : ℕ)^5007*1250000000000^3983 ≤ 551560058723^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608074721 5000000000 551560058723 1250000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5012123/31250000 : ℝ)^5007 ≤ (5009532443361/50000000000000 : ℝ)^3983 := by
    have hnat : (5012123 : ℕ)^5007*50000000000000^3983 ≤ 5009532443361^3983*31250000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012123 31250000 5009532443361 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378315401/10000000000 : ℝ), (2608074721/5000000000 : ℝ), (-5012123/31250000 : ℝ)] ![(9171226079431/20000000000000 : ℝ), (551560058723/1250000000000 : ℝ), (5009532443361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378315401/10000000000 : ℝ)|^5007 ≤ (9171226079431/20000000000000 : ℝ)^3983
        have hw : |(5378315401/10000000000 : ℝ)|=(5378315401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608074721/5000000000 : ℝ)|^5007 ≤ (551560058723/1250000000000 : ℝ)^3983
        have hw : |(2608074721/5000000000 : ℝ)|=(2608074721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5012123/31250000 : ℝ)|^5007 ≤ (5009532443361/50000000000000 : ℝ)^3983
        have hw : |(-5012123/31250000 : ℝ)|=(5012123/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_7 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1940955381/5000000000 : ℝ)*x 0 + (4316703509/10000000000 : ℝ)*x 1 + (4316703439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1940955381/5000000000 : ℝ)^5007 ≤ (30436322759623/100000000000000 : ℝ)^3983 := by
    have hnat : (1940955381 : ℕ)^5007*100000000000000^3983 ≤ 30436322759623^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1940955381 5000000000 30436322759623 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316703509/10000000000 : ℝ)^5007 ≤ (34781838970861/100000000000000 : ℝ)^3983 := by
    have hnat : (4316703509 : ℕ)^5007*100000000000000^3983 ≤ 34781838970861^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316703509 10000000000 34781838970861 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316703439/10000000000 : ℝ)^5007 ≤ (3478183826183/10000000000000 : ℝ)^3983 := by
    have hnat : (4316703439 : ℕ)^5007*10000000000000^3983 ≤ 3478183826183^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316703439 10000000000 3478183826183 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1940955381/5000000000 : ℝ), (4316703509/10000000000 : ℝ), (4316703439/10000000000 : ℝ)] ![(30436322759623/100000000000000 : ℝ), (34781838970861/100000000000000 : ℝ), (3478183826183/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1940955381/5000000000 : ℝ)|^5007 ≤ (30436322759623/100000000000000 : ℝ)^3983
        have hw : |(1940955381/5000000000 : ℝ)|=(1940955381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316703509/10000000000 : ℝ)|^5007 ≤ (34781838970861/100000000000000 : ℝ)^3983
        have hw : |(4316703509/10000000000 : ℝ)|=(4316703509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316703439/10000000000 : ℝ)|^5007 ≤ (3478183826183/10000000000000 : ℝ)^3983
        have hw : |(4316703439/10000000000 : ℝ)|=(4316703439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_8 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-171149979/1000000000 : ℝ)*x 0 + (2540742701/5000000000 : ℝ)*x 1 + (678986287/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171149979/1000000000 : ℝ)^5007 ≤ (2717838750967/25000000000000 : ℝ)^3983 := by
    have hnat : (171149979 : ℕ)^5007*25000000000000^3983 ≤ 2717838750967^3983*1000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171149979 1000000000 2717838750967 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540742701/5000000000 : ℝ)^5007 ≤ (42697559215437/100000000000000 : ℝ)^3983 := by
    have hnat : (2540742701 : ℕ)^5007*100000000000000^3983 ≤ 42697559215437^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540742701 5000000000 42697559215437 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678986287/1250000000 : ℝ)^5007 ≤ (4643108577197/10000000000000 : ℝ)^3983 := by
    have hnat : (678986287 : ℕ)^5007*10000000000000^3983 ≤ 4643108577197^3983*1250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678986287 1250000000 4643108577197 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-171149979/1000000000 : ℝ), (2540742701/5000000000 : ℝ), (678986287/1250000000 : ℝ)] ![(2717838750967/25000000000000 : ℝ), (42697559215437/100000000000000 : ℝ), (4643108577197/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-171149979/1000000000 : ℝ)|^5007 ≤ (2717838750967/25000000000000 : ℝ)^3983
        have hw : |(-171149979/1000000000 : ℝ)|=(171149979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2540742701/5000000000 : ℝ)|^5007 ≤ (42697559215437/100000000000000 : ℝ)^3983
        have hw : |(2540742701/5000000000 : ℝ)|=(2540742701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678986287/1250000000 : ℝ)|^5007 ≤ (4643108577197/10000000000000 : ℝ)^3983
        have hw : |(678986287/1250000000 : ℝ)|=(678986287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_9 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230669989/10000000000 : ℝ)*x 0 + (-1510279241/10000000000 : ℝ)*x 1 + (5431890389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230669989/10000000000 : ℝ)^5007 ≤ (44279272620893/100000000000000 : ℝ)^3983 := by
    have hnat : (5230669989 : ℕ)^5007*100000000000000^3983 ≤ 44279272620893^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230669989 10000000000 44279272620893 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1510279241/10000000000 : ℝ)^5007 ≤ (2322410147821/25000000000000 : ℝ)^3983 := by
    have hnat : (1510279241 : ℕ)^5007*25000000000000^3983 ≤ 2322410147821^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510279241 10000000000 2322410147821 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431890389/10000000000 : ℝ)^5007 ≤ (23215543385649/50000000000000 : ℝ)^3983 := by
    have hnat : (5431890389 : ℕ)^5007*50000000000000^3983 ≤ 23215543385649^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431890389 10000000000 23215543385649 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230669989/10000000000 : ℝ), (-1510279241/10000000000 : ℝ), (5431890389/10000000000 : ℝ)] ![(44279272620893/100000000000000 : ℝ), (2322410147821/25000000000000 : ℝ), (23215543385649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230669989/10000000000 : ℝ)|^5007 ≤ (44279272620893/100000000000000 : ℝ)^3983
        have hw : |(5230669989/10000000000 : ℝ)|=(5230669989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1510279241/10000000000 : ℝ)|^5007 ≤ (2322410147821/25000000000000 : ℝ)^3983
        have hw : |(-1510279241/10000000000 : ℝ)|=(1510279241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431890389/10000000000 : ℝ)|^5007 ≤ (23215543385649/50000000000000 : ℝ)^3983
        have hw : |(5431890389/10000000000 : ℝ)|=(5431890389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_10 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230670037/10000000000 : ℝ)*x 0 + (6789863/12500000 : ℝ)*x 1 + (-37756979/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230670037/10000000000 : ℝ)^5007 ≤ (22139636565847/50000000000000 : ℝ)^3983 := by
    have hnat : (5230670037 : ℕ)^5007*50000000000000^3983 ≤ 22139636565847^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230670037 10000000000 22139636565847 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6789863/12500000 : ℝ)^5007 ≤ (46431086889499/100000000000000 : ℝ)^3983 := by
    have hnat : (6789863 : ℕ)^5007*100000000000000^3983 ≤ 46431086889499^3983*12500000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6789863 12500000 46431086889499 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37756979/250000000 : ℝ)^5007 ≤ (9289639964967/100000000000000 : ℝ)^3983 := by
    have hnat : (37756979 : ℕ)^5007*100000000000000^3983 ≤ 9289639964967^3983*250000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37756979 250000000 9289639964967 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230670037/10000000000 : ℝ), (6789863/12500000 : ℝ), (-37756979/250000000 : ℝ)] ![(22139636565847/50000000000000 : ℝ), (46431086889499/100000000000000 : ℝ), (9289639964967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230670037/10000000000 : ℝ)|^5007 ≤ (22139636565847/50000000000000 : ℝ)^3983
        have hw : |(5230670037/10000000000 : ℝ)|=(5230670037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6789863/12500000 : ℝ)|^5007 ≤ (46431086889499/100000000000000 : ℝ)^3983
        have hw : |(6789863/12500000 : ℝ)|=(6789863/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37756979/250000000 : ℝ)|^5007 ≤ (9289639964967/100000000000000 : ℝ)^3983
        have hw : |(-37756979/250000000 : ℝ)|=(37756979/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_11 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2262257933/5000000000 : ℝ)*x 0 + (998625821/2500000000 : ℝ)*x 1 + (3994503001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2262257933/5000000000 : ℝ)^5007 ≤ (4612456178399/12500000000000 : ℝ)^3983 := by
    have hnat : (2262257933 : ℕ)^5007*12500000000000^3983 ≤ 4612456178399^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262257933 5000000000 4612456178399 12500000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998625821/2500000000 : ℝ)^5007 ≤ (7887544171001/25000000000000 : ℝ)^3983 := by
    have hnat : (998625821 : ℕ)^5007*25000000000000^3983 ≤ 7887544171001^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998625821 2500000000 7887544171001 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3994503001/10000000000 : ℝ)^5007 ≤ (7887543468523/25000000000000 : ℝ)^3983 := by
    have hnat : (3994503001 : ℕ)^5007*25000000000000^3983 ≤ 7887543468523^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3994503001 10000000000 7887543468523 25000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2262257933/5000000000 : ℝ), (998625821/2500000000 : ℝ), (3994503001/10000000000 : ℝ)] ![(4612456178399/12500000000000 : ℝ), (7887544171001/25000000000000 : ℝ), (7887543468523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2262257933/5000000000 : ℝ)|^5007 ≤ (4612456178399/12500000000000 : ℝ)^3983
        have hw : |(2262257933/5000000000 : ℝ)|=(2262257933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(998625821/2500000000 : ℝ)|^5007 ≤ (7887544171001/25000000000000 : ℝ)^3983
        have hw : |(998625821/2500000000 : ℝ)|=(998625821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3994503001/10000000000 : ℝ)|^5007 ≤ (7887543468523/25000000000000 : ℝ)^3983
        have hw : |(3994503001/10000000000 : ℝ)|=(3994503001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_12 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8854241/62500000 : ℝ)*x 0 + (1383095853/2500000000 : ℝ)*x 1 + (259819409/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8854241/62500000 : ℝ)^5007 ≤ (4285874264083/50000000000000 : ℝ)^3983 := by
    have hnat : (8854241 : ℕ)^5007*50000000000000^3983 ≤ 4285874264083^3983*62500000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8854241 62500000 4285874264083 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383095853/2500000000 : ℝ)^5007 ≤ (47513487230797/100000000000000 : ℝ)^3983 := by
    have hnat : (1383095853 : ℕ)^5007*100000000000000^3983 ≤ 47513487230797^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383095853 2500000000 47513487230797 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259819409/500000000 : ℝ)^5007 ≤ (8782952845469/20000000000000 : ℝ)^3983 := by
    have hnat : (259819409 : ℕ)^5007*20000000000000^3983 ≤ 8782952845469^3983*500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259819409 500000000 8782952845469 20000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8854241/62500000 : ℝ), (1383095853/2500000000 : ℝ), (259819409/500000000 : ℝ)] ![(4285874264083/50000000000000 : ℝ), (47513487230797/100000000000000 : ℝ), (8782952845469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8854241/62500000 : ℝ)|^5007 ≤ (4285874264083/50000000000000 : ℝ)^3983
        have hw : |(-8854241/62500000 : ℝ)|=(8854241/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383095853/2500000000 : ℝ)|^5007 ≤ (47513487230797/100000000000000 : ℝ)^3983
        have hw : |(1383095853/2500000000 : ℝ)|=(1383095853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259819409/500000000 : ℝ)|^5007 ≤ (8782952845469/20000000000000 : ℝ)^3983
        have hw : |(259819409/500000000 : ℝ)|=(259819409/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_13 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21061917/39062500 : ℝ)*x 0 + (-1612140657/10000000000 : ℝ)*x 1 + (2598194239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21061917/39062500 : ℝ)^5007 ≤ (46001250751781/100000000000000 : ℝ)^3983 := by
    have hnat : (21061917 : ℕ)^5007*100000000000000^3983 ≤ 46001250751781^3983*39062500^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21061917 39062500 46001250751781 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1612140657/10000000000 : ℝ)^5007 ≤ (10083981836429/100000000000000 : ℝ)^3983 := by
    have hnat : (1612140657 : ℕ)^5007*100000000000000^3983 ≤ 10083981836429^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612140657 10000000000 10083981836429 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598194239/5000000000 : ℝ)^5007 ≤ (43914767393211/100000000000000 : ℝ)^3983 := by
    have hnat : (2598194239 : ℕ)^5007*100000000000000^3983 ≤ 43914767393211^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598194239 5000000000 43914767393211 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21061917/39062500 : ℝ), (-1612140657/10000000000 : ℝ), (2598194239/5000000000 : ℝ)] ![(46001250751781/100000000000000 : ℝ), (10083981836429/100000000000000 : ℝ), (43914767393211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21061917/39062500 : ℝ)|^5007 ≤ (46001250751781/100000000000000 : ℝ)^3983
        have hw : |(21061917/39062500 : ℝ)|=(21061917/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1612140657/10000000000 : ℝ)|^5007 ≤ (10083981836429/100000000000000 : ℝ)^3983
        have hw : |(-1612140657/10000000000 : ℝ)|=(1612140657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598194239/5000000000 : ℝ)|^5007 ≤ (43914767393211/100000000000000 : ℝ)^3983
        have hw : |(2598194239/5000000000 : ℝ)|=(2598194239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_14 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391850751/10000000000 : ℝ)*x 0 + (25981943/50000000 : ℝ)*x 1 + (-806070247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391850751/10000000000 : ℝ)^5007 ≤ (718769542829/1562500000000 : ℝ)^3983 := by
    have hnat : (5391850751 : ℕ)^5007*1562500000000^3983 ≤ 718769542829^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391850751 10000000000 718769542829 1562500000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25981943/50000000 : ℝ)^5007 ≤ (43914768689303/100000000000000 : ℝ)^3983 := by
    have hnat : (25981943 : ℕ)^5007*100000000000000^3983 ≤ 43914768689303^3983*50000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25981943 50000000 43914768689303 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806070247/5000000000 : ℝ)^5007 ≤ (630248784671/6250000000000 : ℝ)^3983 := by
    have hnat : (806070247 : ℕ)^5007*6250000000000^3983 ≤ 630248784671^3983*5000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806070247 5000000000 630248784671 6250000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391850751/10000000000 : ℝ), (25981943/50000000 : ℝ), (-806070247/5000000000 : ℝ)] ![(718769542829/1562500000000 : ℝ), (43914768689303/100000000000000 : ℝ), (630248784671/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391850751/10000000000 : ℝ)|^5007 ≤ (718769542829/1562500000000 : ℝ)^3983
        have hw : |(5391850751/10000000000 : ℝ)|=(5391850751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25981943/50000000 : ℝ)|^5007 ≤ (43914768689303/100000000000000 : ℝ)^3983
        have hw : |(25981943/50000000 : ℝ)|=(25981943/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-806070247/5000000000 : ℝ)|^5007 ≤ (630248784671/6250000000000 : ℝ)^3983
        have hw : |(-806070247/5000000000 : ℝ)|=(806070247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1672_box_15 (p : ℝ) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3821204191/10000000000 : ℝ)*x 0 + (1086538561/2500000000 : ℝ)*x 1 + (4346153967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3821204191/10000000000 : ℝ)^5007 ≤ (29839188084321/100000000000000 : ℝ)^3983 := by
    have hnat : (3821204191 : ℕ)^5007*100000000000000^3983 ≤ 29839188084321^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3821204191 10000000000 29839188084321 100000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086538561/2500000000 : ℝ)^5007 ≤ (3508040735277/10000000000000 : ℝ)^3983 := by
    have hnat : (1086538561 : ℕ)^5007*10000000000000^3983 ≤ 3508040735277^3983*2500000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086538561 2500000000 3508040735277 10000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4346153967/10000000000 : ℝ)^5007 ≤ (17540202271061/50000000000000 : ℝ)^3983 := by
    have hnat : (4346153967 : ℕ)^5007*50000000000000^3983 ≤ 17540202271061^3983*10000000000^5007 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346153967 10000000000 17540202271061 50000000000000 5007 3983 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5007/1024 : ℝ)) 5007 3983 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3821204191/10000000000 : ℝ), (1086538561/2500000000 : ℝ), (4346153967/10000000000 : ℝ)] ![(29839188084321/100000000000000 : ℝ), (3508040735277/10000000000000 : ℝ), (17540202271061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3821204191/10000000000 : ℝ)|^5007 ≤ (29839188084321/100000000000000 : ℝ)^3983
        have hw : |(3821204191/10000000000 : ℝ)|=(3821204191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086538561/2500000000 : ℝ)|^5007 ≤ (3508040735277/10000000000000 : ℝ)^3983
        have hw : |(1086538561/2500000000 : ℝ)|=(1086538561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4346153967/10000000000 : ℝ)|^5007 ≤ (17540202271061/50000000000000 : ℝ)^3983
        have hw : |(4346153967/10000000000 : ℝ)|=(4346153967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1672_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16291/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58863/100000 : ℝ) ∧ (81587/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44217/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16223/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16223/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5389/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16223/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16223/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5389/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16223/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16223/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5389/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5389/50000 : ℝ) ^ (5003/1024 : ℝ) ≤ (468997984425581/25000000000000000000 : ℝ) := by
    have hpowers : (5389/50000 : ℝ)^5003 ≤ (468997984425581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5389 : ℕ)^5003*25000000000000000000^1024 ≤ 468997984425581^1024*50000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5389 50000 468997984425581 25000000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5389/50000 : ℝ)) (X := (468997984425581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16223/100000 : ℝ) ^ (5003/1024 : ℝ) ≤ (345815563172263/2500000000000000000 : ℝ) := by
    have hpowers : (16223/100000 : ℝ)^5003 ≤ (345815563172263/2500000000000000000 : ℝ)^1024 := by
      have hnat : (16223 : ℕ)^5003*2500000000000000000^1024 ≤ 345815563172263^1024*100000^5003 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16223 100000 345815563172263 2500000000000000000 5003 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16223/100000 : ℝ)) (X := (345815563172263/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500468997984425581/12500000000000000000 : ℝ) ≤ (10000076793407273/10000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (12500468997984425581/12500000000000000000 : ℝ)^1024 ≤ (10000076793407273/10000000000000000 : ℝ)^5003 := by
      have hnat : (12500468997984425581 : ℕ)^1024*10000000000000000^5003 ≤ 10000076793407273^5003*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500468997984425581 12500000000000000000 10000076793407273 10000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000076793407273/10000000000000000 : ℝ)) (X := (12500468997984425581/12500000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003927153616148211/25000000000000000000 : ℝ) ≤ (400012859977201/400000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (25003927153616148211/25000000000000000000 : ℝ)^1024 ≤ (400012859977201/400000000000000 : ℝ)^5003 := by
      have hnat : (25003927153616148211 : ℕ)^1024*400000000000000^5003 ≤ 400012859977201^5003*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003927153616148211 25000000000000000000 400012859977201 400000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400012859977201/400000000000000 : ℝ)) (X := (25003927153616148211/25000000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250345815563172263/1250000000000000000 : ℝ) ≤ (10000566205452777/10000000000000000 : ℝ) ^ (5003/1024 : ℝ) := by
    have hpowers : (1250345815563172263/1250000000000000000 : ℝ)^1024 ≤ (10000566205452777/10000000000000000 : ℝ)^5003 := by
      have hnat : (1250345815563172263 : ℕ)^1024*10000000000000000^5003 ≤ 10000566205452777^5003*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250345815563172263 1250000000000000000 10000566205452777 10000000000000000 1024 5003 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000566205452777/10000000000000000 : ℝ)) (X := (1250345815563172263/1250000000000000000 : ℝ)) (by norm_num) 5003 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(468997984425581/25000000000000000000 : ℝ) ≤ ((54445143257076159373/54450000000000000000 : ℝ)+2*(7647063211/17015625000000 : ℝ)*(5389/50000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (54445143257076159373/54450000000000000000 : ℝ)+2*(7647063211/17015625000000 : ℝ)*(5389/50000 : ℝ)=(10000076793407273/10000000000000000 : ℝ) by norm_num, show 1+2*(468997984425581/25000000000000000000 : ℝ)=(12500468997984425581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(345815563172263/2500000000000000000 : ℝ)+(468997984425581/25000000000000000000 : ℝ) ≤ ((54445143257076159373/54450000000000000000 : ℝ)+(7647063211/17015625000000 : ℝ)*((16223/100000 : ℝ)+(5389/50000 : ℝ)))^(5003/1024 : ℝ) := by
    rw [show (54445143257076159373/54450000000000000000 : ℝ)+(7647063211/17015625000000 : ℝ)*((16223/100000 : ℝ)+(5389/50000 : ℝ))=(400012859977201/400000000000000 : ℝ) by norm_num, show 1+(345815563172263/2500000000000000000 : ℝ)+(468997984425581/25000000000000000000 : ℝ)=(25003927153616148211/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(345815563172263/2500000000000000000 : ℝ) ≤ ((54445143257076159373/54450000000000000000 : ℝ)+2*(7647063211/17015625000000 : ℝ)*(16223/100000 : ℝ))^(5003/1024 : ℝ) := by
    rw [show (54445143257076159373/54450000000000000000 : ℝ)+2*(7647063211/17015625000000 : ℝ)*(16223/100000 : ℝ)=(10000566205452777/10000000000000000 : ℝ) by norm_num, show 1+2*(345815563172263/2500000000000000000 : ℝ)=(1250345815563172263/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54445143257076159373/54450000000000000000 : ℝ)*(X 1 0+X 2 0)+(7647063211/17015625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (16223/100000 : ℝ)) (c := (54445143257076159373/54450000000000000000 : ℝ)) (alpha := (7647063211/17015625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54445143257076159373/54450000000000000000 : ℝ)*(X 0 1+X 2 1)+(7647063211/17015625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (16223/100000 : ℝ)) (c := (54445143257076159373/54450000000000000000 : ℝ)) (alpha := (7647063211/17015625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54445143257076159373/54450000000000000000 : ℝ)*(X 0 2+X 1 2)+(7647063211/17015625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5003/1024 : ℝ)) (lo := (5389/50000 : ℝ)) (hi := (16223/100000 : ℝ)) (c := (54445143257076159373/54450000000000000000 : ℝ)) (alpha := (7647063211/17015625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-654746071/5000000000 : ℝ)*X 0 0+(5402707557/10000000000 : ℝ)*X 0 1+(2701353977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250638539/10000000000 : ℝ)*X 1 0+(-761647987/5000000000 : ℝ)*X 1 1+(5402707777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250636619/10000000000 : ℝ)*X 2 0+(2701354709/5000000000 : ℝ)*X 2 1+(-76164817/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1109910191/2500000000 : ℝ)*X 0 0+(2019077761/5000000000 : ℝ)*X 0 1+(4038153927/10000000000 : ℝ)*X 0 2+(1109910191/2500000000 : ℝ)*X 1 0+(2019077761/5000000000 : ℝ)*X 1 1+(4038153927/10000000000 : ℝ)*X 1 2+(1109910191/2500000000 : ℝ)*X 2 0+(2019077761/5000000000 : ℝ)*X 2 1+(4038153927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-28448491/156250000 : ℝ)*X 0 0+(5216149643/10000000000 : ℝ)*X 0 1+(5216149627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1075663029/2000000000 : ℝ)*X 1 0+(-801939597/5000000000 : ℝ)*X 1 1+(5216149823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5378315401/10000000000 : ℝ)*X 2 0+(2608074721/5000000000 : ℝ)*X 2 1+(-5012123/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1940955381/5000000000 : ℝ)*X 0 0+(4316703509/10000000000 : ℝ)*X 0 1+(4316703439/10000000000 : ℝ)*X 0 2+(1940955381/5000000000 : ℝ)*X 1 0+(4316703509/10000000000 : ℝ)*X 1 1+(4316703439/10000000000 : ℝ)*X 1 2+(1940955381/5000000000 : ℝ)*X 2 0+(4316703509/10000000000 : ℝ)*X 2 1+(4316703439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-171149979/1000000000 : ℝ)*X 0 0+(2540742701/5000000000 : ℝ)*X 0 1+(678986287/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230669989/10000000000 : ℝ)*X 1 0+(-1510279241/10000000000 : ℝ)*X 1 1+(5431890389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230670037/10000000000 : ℝ)*X 2 0+(6789863/12500000 : ℝ)*X 2 1+(-37756979/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2262257933/5000000000 : ℝ)*X 0 0+(998625821/2500000000 : ℝ)*X 0 1+(3994503001/10000000000 : ℝ)*X 0 2+(2262257933/5000000000 : ℝ)*X 1 0+(998625821/2500000000 : ℝ)*X 1 1+(3994503001/10000000000 : ℝ)*X 1 2+(2262257933/5000000000 : ℝ)*X 2 0+(998625821/2500000000 : ℝ)*X 2 1+(3994503001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-8854241/62500000 : ℝ)*X 0 0+(1383095853/2500000000 : ℝ)*X 0 1+(259819409/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((21061917/39062500 : ℝ)*X 1 0+(-1612140657/10000000000 : ℝ)*X 1 1+(2598194239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5391850751/10000000000 : ℝ)*X 2 0+(25981943/50000000 : ℝ)*X 2 1+(-806070247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3821204191/10000000000 : ℝ)*X 0 0+(1086538561/2500000000 : ℝ)*X 0 1+(4346153967/10000000000 : ℝ)*X 0 2+(3821204191/10000000000 : ℝ)*X 1 0+(1086538561/2500000000 : ℝ)*X 1 1+(4346153967/10000000000 : ℝ)*X 1 2+(3821204191/10000000000 : ℝ)*X 2 0+(1086538561/2500000000 : ℝ)*X 2 1+(4346153967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1672_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16291/25000 : ℝ) ≤ (-591342273363779593775247082512113/907500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1102101/25000000000000 : ℝ)*(upper1) + (6781067/20000000000000 : ℝ)*(upper3) + (5999481/20000000000000 : ℝ)*(upper5) + (1800498242632619/100000000000000 : ℝ)*(major0) + (1800498242632619/100000000000000 : ℝ)*(major1) + (1800498242632619/100000000000000 : ℝ)*(major2) + (4315429913/100000000000000 : ℝ)*(sp2) + (228541711/20000000000000 : ℝ)*(sp3) + (659648364707407/25000000000000 : ℝ)*(sp4) + (1319292224493773/50000000000000 : ℝ)*(sp5) + (2638589330865043/100000000000000 : ℝ)*(sp6) + (7688455134897/781250000000 : ℝ)*(sp7) + (11716583/6250000000000 : ℝ)*(sp8) + (919730741/10000000000000 : ℝ)*(sp13) + (98412339997537/10000000000000 : ℝ)*(f.failure) + (659648411573739/25000000000000 : ℝ)*(f.sum) + (17864858134253/6806250000000000000000000000 : ℝ)*base66 + (2704051276905687543/605000000000000000000000000000000 : ℝ)*base67 + (13785477120689312457/605000000000000000000000000000000 : ℝ)*base70 + (2685926143834312457/605000000000000000000000000000000 : ℝ)*base72 + (1889285779109/850781250000000000000000000 : ℝ)*base73 + (4466493019559312457/605000000000000000000000000000000 : ℝ)*base76 + (2560905858334312457/605000000000000000000000000000000 : ℝ)*base78 + (161471029005687543/605000000000000000000000000000000 : ℝ)*base79 + (46848369827537/27225000000000000000000000000 : ℝ)*base82 + (174569/25000000000000000000 : ℝ)*base90 + (174569/25000000000000000000 : ℝ)*base92 + (174569/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58863/100000 : ℝ) ≤ (2670999492291293810315801221/4537500000000000000000000000 : ℝ) := by norm_num
    linear_combination (253443707/100000000000000 : ℝ)*(lower0) + (12223711/20000000000000 : ℝ)*(upper1) + (366381053/100000000000000 : ℝ)*(upper2) + (50557373/100000000000000 : ℝ)*(upper3) + (236752309662013/12500000000000 : ℝ)*(major0) + (236752309662013/12500000000000 : ℝ)*(major1) + (236752309662013/12500000000000 : ℝ)*(major2) + (170823337318147/6250000000000 : ℝ)*(sp0) + (1366587614987119/50000000000000 : ℝ)*(sp1) + (2733162824734377/100000000000000 : ℝ)*(sp2) + (1035236536332107/100000000000000 : ℝ)*(sp3) + (620261993/5000000000000 : ℝ)*(sp6) + (880189387/25000000000000 : ℝ)*(sp7) + (916441943/50000000000000 : ℝ)*(sp12) + (207048011417931/20000000000000 : ℝ)*(f.failure) + (1366587614987119/50000000000000 : ℝ)*(f.sum) + (16883618904323/6806250000000000000000000000 : ℝ)*base66 + (177825430588149761/75625000000000000000000000000000 : ℝ)*base67 + (482857193916225239/75625000000000000000000000000000 : ℝ)*base70 + (163434629789350239/75625000000000000000000000000000 : ℝ)*base72 + (60850257745529/13612500000000000000000000000 : ℝ)*base73 + (14579732210024761/75625000000000000000000000000000 : ℝ)*base75 + (83383823452475239/75625000000000000000000000000000 : ℝ)*base78 + (783526352581899761/75625000000000000000000000000000 : ℝ)*base79 + (20782640275483/27225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (137453/50000000000000000000 : ℝ)*base89 + (137453/50000000000000000000 : ℝ)*base91 + (137453/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (81587/100000 : ℝ) ≤ (3702142004564393107139611307/4537500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14961473/100000000000000 : ℝ)*(lower3) + (7881559/20000000000000 : ℝ)*(upper4) + (7854681/20000000000000 : ℝ)*(lower5) + (991127312967541/50000000000000 : ℝ)*(major0) + (991127312967541/50000000000000 : ℝ)*(major1) + (991127312967541/50000000000000 : ℝ)*(major2) + (298812023/12500000000000 : ℝ)*(sp0) + (4153008237/25000000000000 : ℝ)*(sp1) + (29489856603/100000000000000 : ℝ)*(sp2) + (7135981069/50000000000000 : ℝ)*(sp3) + (285384170818091/10000000000000 : ℝ)*(sp8) + (570765497328829/20000000000000 : ℝ)*(sp9) + (285381460882049/10000000000000 : ℝ)*(sp10) + (270863561438009/25000000000000 : ℝ)*(sp11) + (541734258857087/50000000000000 : ℝ)*(f.failure) + (2853844098677093/100000000000000 : ℝ)*(f.sum) + (9072536507459/6806250000000000000000000000 : ℝ)*base66 + (2021915722489432023/302500000000000000000000000000000 : ℝ)*base68 + (1683727465214432023/302500000000000000000000000000000 : ℝ)*base70 + (626360231131932023/302500000000000000000000000000000 : ℝ)*base72 + (118788917989/27225000000000000000000000000 : ℝ)*base73 + (1073994998023067977/302500000000000000000000000000000 : ℝ)*base75 + (509601075843067977/302500000000000000000000000000000 : ℝ)*base77 + (84892491845567977/302500000000000000000000000000000 : ℝ)*base79 + (34806132710143/13612500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (17081/125000000000000000000 : ℝ)*base89 + (17081/125000000000000000000 : ℝ)*base91 + (17081/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-44217/50000 : ℝ) ≤ (-12159303639929367523617737614397/13750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22738107/100000000000000 : ℝ)*(lower0) + (177299/1250000000000 : ℝ)*(lower1) + (84375193/100000000000000 : ℝ)*(lower2) + (41467893/100000000000000 : ℝ)*(lower4) + (2027472711467137/100000000000000 : ℝ)*(major0) + (2027472711467137/100000000000000 : ℝ)*(major1) + (2027472711467137/100000000000000 : ℝ)*(major2) + (6867077181/100000000000000 : ℝ)*(sp0) + (16996159137/50000000000000 : ℝ)*(sp5) + (518224847/25000000000000 : ℝ)*(sp6) + (744057914778883/25000000000000 : ℝ)*(sp12) + (74405113346861/2500000000000 : ℝ)*(sp13) + (1488118226646663/50000000000000 : ℝ)*(sp14) + (554091998237359/50000000000000 : ℝ)*(sp15) + (554091998237359/50000000000000 : ℝ)*(f.failure) + (1488119263096357/50000000000000 : ℝ)*(f.sum) + (2593698714271/618750000000000000000000000 : ℝ)*base65 + (292710052124054799/55000000000000000000000000000000 : ℝ)*base67 + (117975022039054799/55000000000000000000000000000000 : ℝ)*base69 + (290473391599054799/55000000000000000000000000000000 : ℝ)*base71 + (2067781360771/618750000000000000000000000 : ℝ)*base73 + (32706189300945201/55000000000000000000000000000000 : ℝ)*base76 + (74971082379054799/55000000000000000000000000000000 : ℝ)*base77 + (314626831899054799/55000000000000000000000000000000 : ℝ)*base79 + (851452271867/1237500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (297817/125000000000000000000 : ℝ)*base89 + (297817/125000000000000000000 : ℝ)*base91 + (297817/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1672_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5389/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16291/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58863/100000 : ℝ) else (81587/100000 : ℝ) ≤ X j i ∧ X j i ≤ (44217/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1672_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1672_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16291/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58863/100000 : ℝ) else (81587/100000 : ℝ) ≤ X j i ∧ X j i ≤ (44217/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1672_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1672_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1672_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5003/1024 : ℝ) ≤ p) (hpb : p ≤ (5007/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4573863/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1073/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16291/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58863/100000 : ℝ) else (81587/100000 : ℝ) ≤ X j i ∧ X j i ≤ (44217/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1672_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

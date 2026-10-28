-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:00.08077+00:00
-- url     : https://prove2.me/submissions/87788bd1-18d4-4bb4-adaa-029ce21b8ec1

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
theorem support_rectangle_w1107_s6_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183697083/10000000000 : ℝ)*x 0 + (5394087263/10000000000 : ℝ)*x 1 + (1316189079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183697083/10000000000 : ℝ)^2075 ≤ (3316410143713/25000000000000 : ℝ)^1563 := by
    have hnat : (2183697083 : ℕ)^2075*25000000000000^1563 ≤ 3316410143713^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183697083 10000000000 3316410143713 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394087263/10000000000 : ℝ)^2075 ≤ (44065727977813/100000000000000 : ℝ)^1563 := by
    have hnat : (5394087263 : ℕ)^2075*100000000000000^1563 ≤ 44065727977813^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394087263 10000000000 44065727977813 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316189079/2500000000 : ℝ)^2075 ≤ (42668631439113/100000000000000 : ℝ)^1563 := by
    have hnat : (1316189079 : ℕ)^2075*100000000000000^1563 ≤ 42668631439113^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316189079 2500000000 42668631439113 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183697083/10000000000 : ℝ), (5394087263/10000000000 : ℝ), (1316189079/2500000000 : ℝ)] ![(3316410143713/25000000000000 : ℝ), (44065727977813/100000000000000 : ℝ), (42668631439113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183697083/10000000000 : ℝ)|^2075 ≤ (3316410143713/25000000000000 : ℝ)^1563
        have hw : |(-2183697083/10000000000 : ℝ)|=(2183697083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394087263/10000000000 : ℝ)|^2075 ≤ (44065727977813/100000000000000 : ℝ)^1563
        have hw : |(5394087263/10000000000 : ℝ)|=(5394087263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316189079/2500000000 : ℝ)|^2075 ≤ (42668631439113/100000000000000 : ℝ)^1563
        have hw : |(1316189079/2500000000 : ℝ)|=(1316189079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668122911/1250000000 : ℝ)*x 0 + (-1124655547/5000000000 : ℝ)*x 1 + (1316189077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668122911/1250000000 : ℝ)^2075 ≤ (2176698782081/5000000000000 : ℝ)^1563 := by
    have hnat : (668122911 : ℕ)^2075*5000000000000^1563 ≤ 2176698782081^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668122911 1250000000 2176698782081 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124655547/5000000000 : ℝ)^2075 ≤ (3449348248039/25000000000000 : ℝ)^1563 := by
    have hnat : (1124655547 : ℕ)^2075*25000000000000^1563 ≤ 3449348248039^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124655547 5000000000 3449348248039 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316189077/2500000000 : ℝ)^2075 ≤ (42668631353037/100000000000000 : ℝ)^1563 := by
    have hnat : (1316189077 : ℕ)^2075*100000000000000^1563 ≤ 42668631353037^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316189077 2500000000 42668631353037 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668122911/1250000000 : ℝ), (-1124655547/5000000000 : ℝ), (1316189077/2500000000 : ℝ)] ![(2176698782081/5000000000000 : ℝ), (3449348248039/25000000000000 : ℝ), (42668631353037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668122911/1250000000 : ℝ)|^2075 ≤ (2176698782081/5000000000000 : ℝ)^1563
        have hw : |(668122911/1250000000 : ℝ)|=(668122911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124655547/5000000000 : ℝ)|^2075 ≤ (3449348248039/25000000000000 : ℝ)^1563
        have hw : |(-1124655547/5000000000 : ℝ)|=(1124655547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316189077/2500000000 : ℝ)|^2075 ≤ (42668631353037/100000000000000 : ℝ)^1563
        have hw : |(1316189077/2500000000 : ℝ)|=(1316189077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53449833/100000000 : ℝ)*x 0 + (5264756307/10000000000 : ℝ)*x 1 + (-56232777/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53449833/100000000 : ℝ)^2075 ≤ (348271806171/800000000000 : ℝ)^1563 := by
    have hnat : (53449833 : ℕ)^2075*800000000000^1563 ≤ 348271806171^1563*100000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53449833 100000000 348271806171 800000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264756307/10000000000 : ℝ)^2075 ≤ (21334315671139/50000000000000 : ℝ)^1563 := by
    have hnat : (5264756307 : ℕ)^2075*50000000000000^1563 ≤ 21334315671139^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264756307 10000000000 21334315671139 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56232777/250000000 : ℝ)^2075 ≤ (3449348219537/25000000000000 : ℝ)^1563 := by
    have hnat : (56232777 : ℕ)^2075*25000000000000^1563 ≤ 3449348219537^1563*250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56232777 250000000 3449348219537 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53449833/100000000 : ℝ), (5264756307/10000000000 : ℝ), (-56232777/250000000 : ℝ)] ![(348271806171/800000000000 : ℝ), (21334315671139/50000000000000 : ℝ), (3449348219537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53449833/100000000 : ℝ)|^2075 ≤ (348271806171/800000000000 : ℝ)^1563
        have hw : |(53449833/100000000 : ℝ)|=(53449833/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264756307/10000000000 : ℝ)|^2075 ≤ (21334315671139/50000000000000 : ℝ)^1563
        have hw : |(5264756307/10000000000 : ℝ)|=(5264756307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56232777/250000000 : ℝ)|^2075 ≤ (3449348219537/25000000000000 : ℝ)^1563
        have hw : |(-56232777/250000000 : ℝ)|=(56232777/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1092401543/2500000000 : ℝ)*x 0 + (530464071/1250000000 : ℝ)*x 1 + (562405999/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092401543/2500000000 : ℝ)^2075 ≤ (16658278652179/50000000000000 : ℝ)^1563 := by
    have hnat : (1092401543 : ℕ)^2075*50000000000000^1563 ≤ 16658278652179^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092401543 2500000000 16658278652179 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530464071/1250000000 : ℝ)^2075 ≤ (3204828385537/10000000000000 : ℝ)^1563 := by
    have hnat : (530464071 : ℕ)^2075*10000000000000^1563 ≤ 3204828385537^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530464071 1250000000 3204828385537 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562405999/1250000000 : ℝ)^2075 ≤ (17317579413951/50000000000000 : ℝ)^1563 := by
    have hnat : (562405999 : ℕ)^2075*50000000000000^1563 ≤ 17317579413951^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562405999 1250000000 17317579413951 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092401543/2500000000 : ℝ), (530464071/1250000000 : ℝ), (562405999/1250000000 : ℝ)] ![(16658278652179/50000000000000 : ℝ), (3204828385537/10000000000000 : ℝ), (17317579413951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092401543/2500000000 : ℝ)|^2075 ≤ (16658278652179/50000000000000 : ℝ)^1563
        have hw : |(1092401543/2500000000 : ℝ)|=(1092401543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530464071/1250000000 : ℝ)|^2075 ≤ (3204828385537/10000000000000 : ℝ)^1563
        have hw : |(530464071/1250000000 : ℝ)|=(530464071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562405999/1250000000 : ℝ)|^2075 ≤ (17317579413951/50000000000000 : ℝ)^1563
        have hw : |(562405999/1250000000 : ℝ)|=(562405999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-545925543/2500000000 : ℝ)*x 0 + (5265082887/10000000000 : ℝ)*x 1 + (2696879743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545925543/2500000000 : ℝ)^2075 ≤ (13265681616763/100000000000000 : ℝ)^1563 := by
    have hnat : (545925543 : ℕ)^2075*100000000000000^1563 ≤ 13265681616763^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545925543 2500000000 13265681616763 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265082887/10000000000 : ℝ)^2075 ≤ (21336072597517/50000000000000 : ℝ)^1563 := by
    have hnat : (5265082887 : ℕ)^2075*50000000000000^1563 ≤ 21336072597517^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265082887 10000000000 21336072597517 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696879743/5000000000 : ℝ)^2075 ≤ (22031086584461/50000000000000 : ℝ)^1563 := by
    have hnat : (2696879743 : ℕ)^2075*50000000000000^1563 ≤ 22031086584461^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696879743 5000000000 22031086584461 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-545925543/2500000000 : ℝ), (5265082887/10000000000 : ℝ), (2696879743/5000000000 : ℝ)] ![(13265681616763/100000000000000 : ℝ), (21336072597517/50000000000000 : ℝ), (22031086584461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-545925543/2500000000 : ℝ)|^2075 ≤ (13265681616763/100000000000000 : ℝ)^1563
        have hw : |(-545925543/2500000000 : ℝ)|=(545925543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265082887/10000000000 : ℝ)|^2075 ≤ (21336072597517/50000000000000 : ℝ)^1563
        have hw : |(5265082887/10000000000 : ℝ)|=(5265082887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696879743/5000000000 : ℝ)|^2075 ≤ (22031086584461/50000000000000 : ℝ)^1563
        have hw : |(2696879743/5000000000 : ℝ)|=(2696879743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062460607/2000000000 : ℝ)*x 0 + (-1060153951/5000000000 : ℝ)*x 1 + (269687973/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062460607/2000000000 : ℝ)^2075 ≤ (21590481287741/50000000000000 : ℝ)^1563 := by
    have hnat : (1062460607 : ℕ)^2075*50000000000000^1563 ≤ 21590481287741^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062460607 2000000000 21590481287741 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060153951/5000000000 : ℝ)^2075 ≤ (6378432263091/50000000000000 : ℝ)^1563 := by
    have hnat : (1060153951 : ℕ)^2075*50000000000000^1563 ≤ 6378432263091^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060153951 5000000000 6378432263091 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269687973/500000000 : ℝ)^2075 ≤ (44062172886949/100000000000000 : ℝ)^1563 := by
    have hnat : (269687973 : ℕ)^2075*100000000000000^1563 ≤ 44062172886949^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269687973 500000000 44062172886949 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062460607/2000000000 : ℝ), (-1060153951/5000000000 : ℝ), (269687973/500000000 : ℝ)] ![(21590481287741/50000000000000 : ℝ), (6378432263091/50000000000000 : ℝ), (44062172886949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062460607/2000000000 : ℝ)|^2075 ≤ (21590481287741/50000000000000 : ℝ)^1563
        have hw : |(1062460607/2000000000 : ℝ)|=(1062460607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060153951/5000000000 : ℝ)|^2075 ≤ (6378432263091/50000000000000 : ℝ)^1563
        have hw : |(-1060153951/5000000000 : ℝ)|=(1060153951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269687973/500000000 : ℝ)|^2075 ≤ (44062172886949/100000000000000 : ℝ)^1563
        have hw : |(269687973/500000000 : ℝ)|=(269687973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328075761/2500000000 : ℝ)*x 0 + (2696879719/5000000000 : ℝ)*x 1 + (-2120307919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328075761/2500000000 : ℝ)^2075 ≤ (43180962672603/100000000000000 : ℝ)^1563 := by
    have hnat : (1328075761 : ℕ)^2075*100000000000000^1563 ≤ 43180962672603^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328075761 2500000000 43180962672603 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696879719/5000000000 : ℝ)^2075 ≤ (44062172648357/100000000000000 : ℝ)^1563 := by
    have hnat : (2696879719 : ℕ)^2075*100000000000000^1563 ≤ 44062172648357^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696879719 5000000000 44062172648357 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120307919/10000000000 : ℝ)^2075 ≤ (12756864661967/100000000000000 : ℝ)^1563 := by
    have hnat : (2120307919 : ℕ)^2075*100000000000000^1563 ≤ 12756864661967^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120307919 10000000000 12756864661967 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328075761/2500000000 : ℝ), (2696879719/5000000000 : ℝ), (-2120307919/10000000000 : ℝ)] ![(43180962672603/100000000000000 : ℝ), (44062172648357/100000000000000 : ℝ), (12756864661967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328075761/2500000000 : ℝ)|^2075 ≤ (43180962672603/100000000000000 : ℝ)^1563
        have hw : |(1328075761/2500000000 : ℝ)|=(1328075761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696879719/5000000000 : ℝ)|^2075 ≤ (44062172648357/100000000000000 : ℝ)^1563
        have hw : |(2696879719/5000000000 : ℝ)|=(2696879719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2120307919/10000000000 : ℝ)|^2075 ≤ (12756864661967/100000000000000 : ℝ)^1563
        have hw : |(-2120307919/10000000000 : ℝ)|=(2120307919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s6_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (436961617/1000000000 : ℝ)*x 0 + (2249301329/5000000000 : ℝ)*x 1 + (848872051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436961617/1000000000 : ℝ)^2075 ≤ (260286394583/781250000000 : ℝ)^1563 := by
    have hnat : (436961617 : ℕ)^2075*781250000000^1563 ≤ 260286394583^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436961617 1000000000 260286394583 781250000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249301329/5000000000 : ℝ)^2075 ≤ (34628563889873/100000000000000 : ℝ)^1563 := by
    have hnat : (2249301329 : ℕ)^2075*100000000000000^1563 ≤ 34628563889873^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249301329 5000000000 34628563889873 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848872051/2000000000 : ℝ)^2075 ≤ (4006847197703/12500000000000 : ℝ)^1563 := by
    have hnat : (848872051 : ℕ)^2075*12500000000000^1563 ≤ 4006847197703^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848872051 2000000000 4006847197703 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436961617/1000000000 : ℝ), (2249301329/5000000000 : ℝ), (848872051/2000000000 : ℝ)] ![(260286394583/781250000000 : ℝ), (34628563889873/100000000000000 : ℝ), (4006847197703/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436961617/1000000000 : ℝ)|^2075 ≤ (260286394583/781250000000 : ℝ)^1563
        have hw : |(436961617/1000000000 : ℝ)|=(436961617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249301329/5000000000 : ℝ)|^2075 ≤ (34628563889873/100000000000000 : ℝ)^1563
        have hw : |(2249301329/5000000000 : ℝ)|=(2249301329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848872051/2000000000 : ℝ)|^2075 ≤ (4006847197703/12500000000000 : ℝ)^1563
        have hw : |(848872051/2000000000 : ℝ)|=(848872051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (8299/2048 : ℝ) ≤ (14357174100212483/100000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^8299 ≤ (14357174100212483/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11263 : ℕ)^8299*100000000000000000000^2048 ≤ 14357174100212483^2048*100000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 14357174100212483 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (14357174100212483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (8299/2048 : ℝ) ≤ (35424470672161091/100000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^8299 ≤ (35424470672161091/100000000000000000000 : ℝ)^2048 := by
      have hnat : (563 : ℕ)^8299*100000000000000000000^2048 ≤ 35424470672161091^2048*4000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 35424470672161091 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (35424470672161091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014357174100212483/50000000000000000000 : ℝ) ≤ (2000141705330043/2000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50014357174100212483/50000000000000000000 : ℝ)^2048 ≤ (2000141705330043/2000000000000000 : ℝ)^8299 := by
      have hnat : (50014357174100212483 : ℕ)^2048*2000000000000000^8299 ≤ 2000141705330043^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014357174100212483 50000000000000000000 2000141705330043 2000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000141705330043/2000000000000000 : ℝ)) (X := (50014357174100212483/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024890822386186787/50000000000000000000 : ℝ) ≤ (10001228264846207/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50024890822386186787/50000000000000000000 : ℝ)^2048 ≤ (10001228264846207/10000000000000000 : ℝ)^8299 := by
      have hnat : (50024890822386186787 : ℕ)^2048*10000000000000000^8299 ≤ 10001228264846207^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024890822386186787 50000000000000000000 10001228264846207 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228264846207/10000000000000000 : ℝ)) (X := (50024890822386186787/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035424470672161091/50000000000000000000 : ℝ) ≤ (10001748003042199/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50035424470672161091/50000000000000000000 : ℝ)^2048 ≤ (10001748003042199/10000000000000000 : ℝ)^8299 := by
      have hnat : (50035424470672161091 : ℕ)^2048*10000000000000000^8299 ≤ 10001748003042199^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035424470672161091 50000000000000000000 10001748003042199 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001748003042199/10000000000000000 : ℝ)) (X := (50035424470672161091/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14357174100212483/100000000000000000000 : ℝ) ≤ ((7027571188584372197/7030000000000000000 : ℝ)+2*(64967274499/35150000000000 : ℝ)*(11263/100000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (7027571188584372197/7030000000000000000 : ℝ)+2*(64967274499/35150000000000 : ℝ)*(11263/100000 : ℝ)=(2000141705330043/2000000000000000 : ℝ) by norm_num, show 1+2*(14357174100212483/100000000000000000000 : ℝ)=(50014357174100212483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35424470672161091/100000000000000000000 : ℝ)+(14357174100212483/100000000000000000000 : ℝ) ≤ ((7027571188584372197/7030000000000000000 : ℝ)+(64967274499/35150000000000 : ℝ)*((563/4000 : ℝ)+(11263/100000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (7027571188584372197/7030000000000000000 : ℝ)+(64967274499/35150000000000 : ℝ)*((563/4000 : ℝ)+(11263/100000 : ℝ))=(10001228264846207/10000000000000000 : ℝ) by norm_num, show 1+(35424470672161091/100000000000000000000 : ℝ)+(14357174100212483/100000000000000000000 : ℝ)=(50024890822386186787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35424470672161091/100000000000000000000 : ℝ) ≤ ((7027571188584372197/7030000000000000000 : ℝ)+2*(64967274499/35150000000000 : ℝ)*(563/4000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (7027571188584372197/7030000000000000000 : ℝ)+2*(64967274499/35150000000000 : ℝ)*(563/4000 : ℝ)=(10001748003042199/10000000000000000 : ℝ) by norm_num, show 1+2*(35424470672161091/100000000000000000000 : ℝ)=(50035424470672161091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7027571188584372197/7030000000000000000 : ℝ)*(X 1 0+X 2 0)+(64967274499/35150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (7027571188584372197/7030000000000000000 : ℝ)) (alpha := (64967274499/35150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7027571188584372197/7030000000000000000 : ℝ)*(X 0 1+X 2 1)+(64967274499/35150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (7027571188584372197/7030000000000000000 : ℝ)) (alpha := (64967274499/35150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7027571188584372197/7030000000000000000 : ℝ)*(X 0 2+X 1 2)+(64967274499/35150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (7027571188584372197/7030000000000000000 : ℝ)) (alpha := (64967274499/35150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2183697083/10000000000 : ℝ)*X 0 0+(5394087263/10000000000 : ℝ)*X 0 1+(1316189079/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668122911/1250000000 : ℝ)*X 1 0+(-1124655547/5000000000 : ℝ)*X 1 1+(1316189077/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53449833/100000000 : ℝ)*X 2 0+(5264756307/10000000000 : ℝ)*X 2 1+(-56232777/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092401543/2500000000 : ℝ)*X 0 0+(530464071/1250000000 : ℝ)*X 0 1+(562405999/1250000000 : ℝ)*X 0 2+(1092401543/2500000000 : ℝ)*X 1 0+(530464071/1250000000 : ℝ)*X 1 1+(562405999/1250000000 : ℝ)*X 1 2+(1092401543/2500000000 : ℝ)*X 2 0+(530464071/1250000000 : ℝ)*X 2 1+(562405999/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-545925543/2500000000 : ℝ)*X 0 0+(5265082887/10000000000 : ℝ)*X 0 1+(2696879743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062460607/2000000000 : ℝ)*X 1 0+(-1060153951/5000000000 : ℝ)*X 1 1+(269687973/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328075761/2500000000 : ℝ)*X 2 0+(2696879719/5000000000 : ℝ)*X 2 1+(-2120307919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436961617/1000000000 : ℝ)*X 0 0+(2249301329/5000000000 : ℝ)*X 0 1+(848872051/2000000000 : ℝ)*X 0 2+(436961617/1000000000 : ℝ)*X 1 0+(2249301329/5000000000 : ℝ)*X 1 1+(848872051/2000000000 : ℝ)*X 1 2+(436961617/1000000000 : ℝ)*X 2 0+(2249301329/5000000000 : ℝ)*X 2 1+(848872051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (712061493653133258863687439/87875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658253467/100000000000000 : ℝ)*(base19) + (780159889/50000000000000 : ℝ)*(base23) + (61624023/100000000000000 : ℝ)*(lower2) + (200285417/100000000000000 : ℝ)*(upper3) + (140454447/100000000000000 : ℝ)*(upper5) + (1455698811494329/25000000000000 : ℝ)*(major0) + (1455698811494329/25000000000000 : ℝ)*(major1) + (1455698811494329/25000000000000 : ℝ)*(major2) + (7732147045278353/100000000000000 : ℝ)*(sp0) + (7732190250438531/100000000000000 : ℝ)*(sp1) + (386609517418611/5000000000000 : ℝ)*(sp2) + (48917175264779/1250000000000 : ℝ)*(sp3) + (8972682729/20000000000000 : ℝ)*(sp4) + (3036497047/12500000000000 : ℝ)*(sp7) + (489174789144837/12500000000000 : ℝ)*(f.failure) + (3866095954345999/50000000000000 : ℝ)*(f.sum) + (21318204540053/3515000000000000000000000000 : ℝ)*base65 + (289209013316529187/175750000000000000000000000000000 : ℝ)*base68 + (453682052528529187/175750000000000000000000000000000 : ℝ)*base70 + (2499587371941029187/175750000000000000000000000000000 : ℝ)*base72 + (1397425996721/1757500000000000000000000000 : ℝ)*base74 + (1856887462573970813/175750000000000000000000000000000 : ℝ)*base75 + (98409573404970813/175750000000000000000000000000000 : ℝ)*base77 + (206585526306029187/175750000000000000000000000000000 : ℝ)*base80 + (637388247299/109843750000000000000000000 : ℝ)*base81 + (275887/50000000000000000000 : ℝ)*base89 + (275887/50000000000000000000 : ℝ)*base91 + (275887/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17990311069165493324627409/1900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394126751/20000000000000 : ℝ)*(base19) + (2077419943/100000000000000 : ℝ)*(base23) + (187955421/100000000000000 : ℝ)*(upper3) + (49165251/100000000000000 : ℝ)*(lower4) + (224610821/100000000000000 : ℝ)*(upper5) + (1170467470392037/20000000000000 : ℝ)*(major0) + (1170467470392037/20000000000000 : ℝ)*(major1) + (1170467470392037/20000000000000 : ℝ)*(major2) + (54228147287/100000000000000 : ℝ)*(sp1) + (54402110437/100000000000000 : ℝ)*(sp2) + (7771421345096431/100000000000000 : ℝ)*(sp4) + (7771365146315389/100000000000000 : ℝ)*(sp5) + (7771364865566051/100000000000000 : ℝ)*(sp6) + (1966626521602219/50000000000000 : ℝ)*(sp7) + (1966626521602219/50000000000000 : ℝ)*(f.failure) + (7771421345096431/100000000000000 : ℝ)*(f.sum) + (2471713128171/351500000000000000000000000 : ℝ)*base65 + (765790642364995289/140600000000000000000000000000000 : ℝ)*base67 + (536326710471995289/140600000000000000000000000000000 : ℝ)*base69 + (2118301449026995289/140600000000000000000000000000000 : ℝ)*base71 + (555413857141/351500000000000000000000000 : ℝ)*base73 + (584458045549995289/140600000000000000000000000000000 : ℝ)*base75 + (97781770836804711/140600000000000000000000000000000 : ℝ)*base78 + (60521069155004711/140600000000000000000000000000000 : ℝ)*base80 + (3657078590643/703000000000000000000000000 : ℝ)*base81 + (1686431/200000000000000000000 : ℝ)*base90 + (1686431/200000000000000000000 : ℝ)*base92 + (1686431/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1107_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_s7_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091865507/5000000000 : ℝ)*x 0 + (539370873/1000000000 : ℝ)*x 1 + (5265112427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091865507/5000000000 : ℝ)^2075 ≤ (1326591422313/10000000000000 : ℝ)^1563 := by
    have hnat : (1091865507 : ℕ)^2075*10000000000000^1563 ≤ 1326591422313^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091865507 5000000000 1326591422313 10000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539370873/1000000000 : ℝ)^2075 ≤ (11015405679001/25000000000000 : ℝ)^1563 := by
    have hnat : (539370873 : ℕ)^2075*25000000000000^1563 ≤ 11015405679001^1563*1000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539370873 1000000000 11015405679001 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265112427/10000000000 : ℝ)^2075 ≤ (8534492607113/20000000000000 : ℝ)^1563 := by
    have hnat : (5265112427 : ℕ)^2075*20000000000000^1563 ≤ 8534492607113^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265112427 10000000000 8534492607113 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091865507/5000000000 : ℝ), (539370873/1000000000 : ℝ), (5265112427/10000000000 : ℝ)] ![(1326591422313/10000000000000 : ℝ), (11015405679001/25000000000000 : ℝ), (8534492607113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091865507/5000000000 : ℝ)|^2075 ≤ (1326591422313/10000000000000 : ℝ)^1563
        have hw : |(-1091865507/5000000000 : ℝ)|=(1091865507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539370873/1000000000 : ℝ)|^2075 ≤ (11015405679001/25000000000000 : ℝ)^1563
        have hw : |(539370873/1000000000 : ℝ)|=(539370873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265112427/10000000000 : ℝ)|^2075 ≤ (8534492607113/20000000000000 : ℝ)^1563
        have hw : |(5265112427/10000000000 : ℝ)|=(5265112427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668111001/1250000000 : ℝ)*x 0 + (-2248966959/10000000000 : ℝ)*x 1 + (5265112513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668111001/1250000000 : ℝ)^2075 ≤ (43532945394091/100000000000000 : ℝ)^1563 := by
    have hnat : (668111001 : ℕ)^2075*100000000000000^1563 ≤ 43532945394091^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668111001 1250000000 43532945394091 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248966959/10000000000 : ℝ)^2075 ≤ (6897295313923/50000000000000 : ℝ)^1563 := by
    have hnat : (2248966959 : ℕ)^2075*50000000000000^1563 ≤ 6897295313923^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248966959 10000000000 6897295313923 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265112513/10000000000 : ℝ)^2075 ≤ (42672463960897/100000000000000 : ℝ)^1563 := by
    have hnat : (5265112513 : ℕ)^2075*100000000000000^1563 ≤ 42672463960897^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265112513 10000000000 42672463960897 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668111001/1250000000 : ℝ), (-2248966959/10000000000 : ℝ), (5265112513/10000000000 : ℝ)] ![(43532945394091/100000000000000 : ℝ), (6897295313923/50000000000000 : ℝ), (42672463960897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668111001/1250000000 : ℝ)|^2075 ≤ (43532945394091/100000000000000 : ℝ)^1563
        have hw : |(668111001/1250000000 : ℝ)|=(668111001/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2248966959/10000000000 : ℝ)|^2075 ≤ (6897295313923/50000000000000 : ℝ)^1563
        have hw : |(-2248966959/10000000000 : ℝ)|=(2248966959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265112513/10000000000 : ℝ)|^2075 ≤ (42672463960897/100000000000000 : ℝ)^1563
        have hw : |(5265112513/10000000000 : ℝ)|=(5265112513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267244411/500000000 : ℝ)*x 0 + (329069523/625000000 : ℝ)*x 1 + (-2248966869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267244411/500000000 : ℝ)^2075 ≤ (21766473843203/50000000000000 : ℝ)^1563 := by
    have hnat : (267244411 : ℕ)^2075*50000000000000^1563 ≤ 21766473843203^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267244411 500000000 21766473843203 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329069523/625000000 : ℝ)^2075 ≤ (5334057800093/12500000000000 : ℝ)^1563 := by
    have hnat : (329069523 : ℕ)^2075*12500000000000^1563 ≤ 5334057800093^1563*625000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329069523 625000000 5334057800093 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248966869/10000000000 : ℝ)^2075 ≤ (551783595799/4000000000000 : ℝ)^1563 := by
    have hnat : (2248966869 : ℕ)^2075*4000000000000^1563 ≤ 551783595799^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248966869 10000000000 551783595799 4000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267244411/500000000 : ℝ), (329069523/625000000 : ℝ), (-2248966869/10000000000 : ℝ)] ![(21766473843203/50000000000000 : ℝ), (5334057800093/12500000000000 : ℝ), (551783595799/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267244411/500000000 : ℝ)|^2075 ≤ (21766473843203/50000000000000 : ℝ)^1563
        have hw : |(267244411/500000000 : ℝ)|=(267244411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329069523/625000000 : ℝ)|^2075 ≤ (5334057800093/12500000000000 : ℝ)^1563
        have hw : |(329069523/625000000 : ℝ)|=(329069523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248966869/10000000000 : ℝ)|^2075 ≤ (551783595799/4000000000000 : ℝ)^1563
        have hw : |(-2248966869/10000000000 : ℝ)|=(2248966869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4369624989/10000000000 : ℝ)*x 0 + (4244436043/10000000000 : ℝ)*x 1 + (2249259783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369624989/10000000000 : ℝ)^2075 ≤ (1665837388741/5000000000000 : ℝ)^1563 := by
    have hnat : (4369624989 : ℕ)^2075*5000000000000^1563 ≤ 1665837388741^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369624989 10000000000 1665837388741 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244436043/10000000000 : ℝ)^2075 ≤ (6411107491049/20000000000000 : ℝ)^1563 := by
    have hnat : (4244436043 : ℕ)^2075*20000000000000^1563 ≤ 6411107491049^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244436043 10000000000 6411107491049 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249259783/5000000000 : ℝ)^2075 ≤ (17313857380247/50000000000000 : ℝ)^1563 := by
    have hnat : (2249259783 : ℕ)^2075*50000000000000^1563 ≤ 17313857380247^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249259783 5000000000 17313857380247 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369624989/10000000000 : ℝ), (4244436043/10000000000 : ℝ), (2249259783/5000000000 : ℝ)] ![(1665837388741/5000000000000 : ℝ), (6411107491049/20000000000000 : ℝ), (17313857380247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369624989/10000000000 : ℝ)|^2075 ≤ (1665837388741/5000000000000 : ℝ)^1563
        have hw : |(4369624989/10000000000 : ℝ)|=(4369624989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244436043/10000000000 : ℝ)|^2075 ≤ (6411107491049/20000000000000 : ℝ)^1563
        have hw : |(4244436043/10000000000 : ℝ)|=(4244436043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249259783/5000000000 : ℝ)|^2075 ≤ (17313857380247/50000000000000 : ℝ)^1563
        have hw : |(2249259783/5000000000 : ℝ)|=(2249259783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183736083/10000000000 : ℝ)*x 0 + (1316358847/2500000000 : ℝ)*x 1 + (674173067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183736083/10000000000 : ℝ)^2075 ≤ (13265955103953/100000000000000 : ℝ)^1563 := by
    have hnat : (2183736083 : ℕ)^2075*100000000000000^1563 ≤ 13265955103953^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183736083 10000000000 13265955103953 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316358847/2500000000 : ℝ)^2075 ≤ (42675938026123/100000000000000 : ℝ)^1563 := by
    have hnat : (1316358847 : ℕ)^2075*100000000000000^1563 ≤ 42675938026123^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316358847 2500000000 42675938026123 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674173067/1250000000 : ℝ)^2075 ≤ (44058106845929/100000000000000 : ℝ)^1563 := by
    have hnat : (674173067 : ℕ)^2075*100000000000000^1563 ≤ 44058106845929^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674173067 1250000000 44058106845929 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183736083/10000000000 : ℝ), (1316358847/2500000000 : ℝ), (674173067/1250000000 : ℝ)] ![(13265955103953/100000000000000 : ℝ), (42675938026123/100000000000000 : ℝ), (44058106845929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183736083/10000000000 : ℝ)|^2075 ≤ (13265955103953/100000000000000 : ℝ)^1563
        have hw : |(-2183736083/10000000000 : ℝ)|=(2183736083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316358847/2500000000 : ℝ)|^2075 ≤ (42675938026123/100000000000000 : ℝ)^1563
        have hw : |(1316358847/2500000000 : ℝ)|=(1316358847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674173067/1250000000 : ℝ)|^2075 ≤ (44058106845929/100000000000000 : ℝ)^1563
        have hw : |(674173067/1250000000 : ℝ)|=(674173067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312393363/10000000000 : ℝ)*x 0 + (-424138983/2000000000 : ℝ)*x 1 + (1078676907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312393363/10000000000 : ℝ)^2075 ≤ (43181937323151/100000000000000 : ℝ)^1563 := by
    have hnat : (5312393363 : ℕ)^2075*100000000000000^1563 ≤ 43181937323151^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312393363 10000000000 43181937323151 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424138983/2000000000 : ℝ)^2075 ≤ (637997791849/5000000000000 : ℝ)^1563 := by
    have hnat : (424138983 : ℕ)^2075*5000000000000^1563 ≤ 637997791849^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424138983 2000000000 637997791849 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078676907/2000000000 : ℝ)^2075 ≤ (11014526708771/25000000000000 : ℝ)^1563 := by
    have hnat : (1078676907 : ℕ)^2075*25000000000000^1563 ≤ 11014526708771^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078676907 2000000000 11014526708771 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312393363/10000000000 : ℝ), (-424138983/2000000000 : ℝ), (1078676907/2000000000 : ℝ)] ![(43181937323151/100000000000000 : ℝ), (637997791849/5000000000000 : ℝ), (11014526708771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312393363/10000000000 : ℝ)|^2075 ≤ (43181937323151/100000000000000 : ℝ)^1563
        have hw : |(5312393363/10000000000 : ℝ)|=(5312393363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424138983/2000000000 : ℝ)|^2075 ≤ (637997791849/5000000000000 : ℝ)^1563
        have hw : |(-424138983/2000000000 : ℝ)|=(424138983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078676907/2000000000 : ℝ)|^2075 ≤ (11014526708771/25000000000000 : ℝ)^1563
        have hw : |(1078676907/2000000000 : ℝ)|=(1078676907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062478673/2000000000 : ℝ)*x 0 + (5393384533/10000000000 : ℝ)*x 1 + (-1060347457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062478673/2000000000 : ℝ)^2075 ≤ (43181937344733/100000000000000 : ℝ)^1563 := by
    have hnat : (1062478673 : ℕ)^2075*100000000000000^1563 ≤ 43181937344733^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062478673 2000000000 43181937344733 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393384533/10000000000 : ℝ)^2075 ≤ (8811621362679/20000000000000 : ℝ)^1563 := by
    have hnat : (5393384533 : ℕ)^2075*20000000000000^1563 ≤ 8811621362679^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393384533 10000000000 8811621362679 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060347457/5000000000 : ℝ)^2075 ≤ (49843577457/390625000000 : ℝ)^1563 := by
    have hnat : (1060347457 : ℕ)^2075*390625000000^1563 ≤ 49843577457^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060347457 5000000000 49843577457 390625000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062478673/2000000000 : ℝ), (5393384533/10000000000 : ℝ), (-1060347457/5000000000 : ℝ)] ![(43181937344733/100000000000000 : ℝ), (8811621362679/20000000000000 : ℝ), (49843577457/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062478673/2000000000 : ℝ)|^2075 ≤ (43181937344733/100000000000000 : ℝ)^1563
        have hw : |(1062478673/2000000000 : ℝ)|=(1062478673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393384533/10000000000 : ℝ)|^2075 ≤ (8811621362679/20000000000000 : ℝ)^1563
        have hw : |(5393384533/10000000000 : ℝ)|=(5393384533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1060347457/5000000000 : ℝ)|^2075 ≤ (49843577457/390625000000 : ℝ)^1563
        have hw : |(-1060347457/5000000000 : ℝ)|=(1060347457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s7_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1092408689/2500000000 : ℝ)*x 0 + (899576317/2000000000 : ℝ)*x 1 + (4245076399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092408689/2500000000 : ℝ)^2075 ≤ (6663369327797/20000000000000 : ℝ)^1563 := by
    have hnat : (1092408689 : ℕ)^2075*20000000000000^1563 ≤ 6663369327797^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092408689 2500000000 6663369327797 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899576317/2000000000 : ℝ)^2075 ≤ (17310597654959/50000000000000 : ℝ)^1563 := by
    have hnat : (899576317 : ℕ)^2075*50000000000000^1563 ≤ 17310597654959^1563*2000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899576317 2000000000 17310597654959 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245076399/10000000000 : ℝ)^2075 ≤ (4007744754673/12500000000000 : ℝ)^1563 := by
    have hnat : (4245076399 : ℕ)^2075*12500000000000^1563 ≤ 4007744754673^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245076399 10000000000 4007744754673 12500000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092408689/2500000000 : ℝ), (899576317/2000000000 : ℝ), (4245076399/10000000000 : ℝ)] ![(6663369327797/20000000000000 : ℝ), (17310597654959/50000000000000 : ℝ), (4007744754673/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092408689/2500000000 : ℝ)|^2075 ≤ (6663369327797/20000000000000 : ℝ)^1563
        have hw : |(1092408689/2500000000 : ℝ)|=(1092408689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899576317/2000000000 : ℝ)|^2075 ≤ (17310597654959/50000000000000 : ℝ)^1563
        have hw : |(899576317/2000000000 : ℝ)|=(899576317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245076399/10000000000 : ℝ)|^2075 ≤ (4007744754673/12500000000000 : ℝ)^1563
        have hw : |(4245076399/10000000000 : ℝ)|=(4245076399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5653/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1403/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7019/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7019/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5649/50000 : ℝ) ^ (8299/2048 : ℝ) ≤ (14538825126359339/100000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^8299 ≤ (14538825126359339/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5649 : ℕ)^8299*100000000000000000000^2048 ≤ 14538825126359339^2048*50000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 14538825126359339 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (14538825126359339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7019/50000 : ℝ) ^ (8299/2048 : ℝ) ≤ (35048624765536653/100000000000000000000 : ℝ) := by
    have hpowers : (7019/50000 : ℝ)^8299 ≤ (35048624765536653/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7019 : ℕ)^8299*100000000000000000000^2048 ≤ 35048624765536653^2048*50000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7019 50000 35048624765536653 100000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7019/50000 : ℝ)) (X := (35048624765536653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014538825126359339/50000000000000000000 : ℝ) ≤ (10000717490148253/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50014538825126359339/50000000000000000000 : ℝ)^2048 ≤ (10000717490148253/10000000000000000 : ℝ)^8299 := by
      have hnat : (50014538825126359339 : ℕ)^2048*10000000000000000^8299 ≤ 10000717490148253^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014538825126359339 50000000000000000000 10000717490148253 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000717490148253/10000000000000000 : ℝ)) (X := (50014538825126359339/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506198431236486999/12500000000000000000 : ℝ) ≤ (10001223474361301/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (12506198431236486999/12500000000000000000 : ℝ)^2048 ≤ (10001223474361301/10000000000000000 : ℝ)^8299 := by
      have hnat : (12506198431236486999 : ℕ)^2048*10000000000000000^8299 ≤ 10001223474361301^8299*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506198431236486999 12500000000000000000 10001223474361301 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001223474361301/10000000000000000 : ℝ)) (X := (12506198431236486999/12500000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035048624765536653/50000000000000000000 : ℝ) ≤ (10001729458574349/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50035048624765536653/50000000000000000000 : ℝ)^2048 ≤ (10001729458574349/10000000000000000 : ℝ)^8299 := by
      have hnat : (50035048624765536653 : ℕ)^2048*10000000000000000^8299 ≤ 10001729458574349^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035048624765536653 50000000000000000000 10001729458574349 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001729458574349/10000000000000000 : ℝ)) (X := (50035048624765536653/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14538825126359339/100000000000000000000 : ℝ) ≤ ((6847633175932045153/6850000000000000000 : ℝ)+2*(63248026631/34250000000000 : ℝ)*(5649/50000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (6847633175932045153/6850000000000000000 : ℝ)+2*(63248026631/34250000000000 : ℝ)*(5649/50000 : ℝ)=(10000717490148253/10000000000000000 : ℝ) by norm_num, show 1+2*(14538825126359339/100000000000000000000 : ℝ)=(50014538825126359339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35048624765536653/100000000000000000000 : ℝ)+(14538825126359339/100000000000000000000 : ℝ) ≤ ((6847633175932045153/6850000000000000000 : ℝ)+(63248026631/34250000000000 : ℝ)*((7019/50000 : ℝ)+(5649/50000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (6847633175932045153/6850000000000000000 : ℝ)+(63248026631/34250000000000 : ℝ)*((7019/50000 : ℝ)+(5649/50000 : ℝ))=(10001223474361301/10000000000000000 : ℝ) by norm_num, show 1+(35048624765536653/100000000000000000000 : ℝ)+(14538825126359339/100000000000000000000 : ℝ)=(12506198431236486999/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35048624765536653/100000000000000000000 : ℝ) ≤ ((6847633175932045153/6850000000000000000 : ℝ)+2*(63248026631/34250000000000 : ℝ)*(7019/50000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (6847633175932045153/6850000000000000000 : ℝ)+2*(63248026631/34250000000000 : ℝ)*(7019/50000 : ℝ)=(10001729458574349/10000000000000000 : ℝ) by norm_num, show 1+2*(35048624765536653/100000000000000000000 : ℝ)=(50035048624765536653/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6847633175932045153/6850000000000000000 : ℝ)*(X 1 0+X 2 0)+(63248026631/34250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (6847633175932045153/6850000000000000000 : ℝ)) (alpha := (63248026631/34250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6847633175932045153/6850000000000000000 : ℝ)*(X 0 1+X 2 1)+(63248026631/34250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (6847633175932045153/6850000000000000000 : ℝ)) (alpha := (63248026631/34250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6847633175932045153/6850000000000000000 : ℝ)*(X 0 2+X 1 2)+(63248026631/34250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (7019/50000 : ℝ)) (c := (6847633175932045153/6850000000000000000 : ℝ)) (alpha := (63248026631/34250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1091865507/5000000000 : ℝ)*X 0 0+(539370873/1000000000 : ℝ)*X 0 1+(5265112427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668111001/1250000000 : ℝ)*X 1 0+(-2248966959/10000000000 : ℝ)*X 1 1+(5265112513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267244411/500000000 : ℝ)*X 2 0+(329069523/625000000 : ℝ)*X 2 1+(-2248966869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369624989/10000000000 : ℝ)*X 0 0+(4244436043/10000000000 : ℝ)*X 0 1+(2249259783/5000000000 : ℝ)*X 0 2+(4369624989/10000000000 : ℝ)*X 1 0+(4244436043/10000000000 : ℝ)*X 1 1+(2249259783/5000000000 : ℝ)*X 1 2+(4369624989/10000000000 : ℝ)*X 2 0+(4244436043/10000000000 : ℝ)*X 2 1+(2249259783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183736083/10000000000 : ℝ)*X 0 0+(1316358847/2500000000 : ℝ)*X 0 1+(674173067/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312393363/10000000000 : ℝ)*X 1 0+(-424138983/2000000000 : ℝ)*X 1 1+(1078676907/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062478673/2000000000 : ℝ)*X 2 0+(5393384533/10000000000 : ℝ)*X 2 1+(-1060347457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092408689/2500000000 : ℝ)*X 0 0+(899576317/2000000000 : ℝ)*X 0 1+(4245076399/10000000000 : ℝ)*X 0 2+(1092408689/2500000000 : ℝ)*X 1 0+(899576317/2000000000 : ℝ)*X 1 1+(4245076399/10000000000 : ℝ)*X 1 2+(1092408689/2500000000 : ℝ)*X 2 0+(899576317/2000000000 : ℝ)*X 2 1+(4245076399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13869595388969891349039/3425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (914816451/100000000000000 : ℝ)*(base19) + (245028761/25000000000000 : ℝ)*(base23) + (64978461/50000000000000 : ℝ)*(lower2) + (2007281/4000000000000 : ℝ)*(upper3) + (70558797/100000000000000 : ℝ)*(upper5) + (1464009434673681/25000000000000 : ℝ)*(major0) + (1464009434673681/25000000000000 : ℝ)*(major1) + (1464009434673681/25000000000000 : ℝ)*(major2) + (7776300264375459/100000000000000 : ℝ)*(sp0) + (7776334419517569/100000000000000 : ℝ)*(sp1) + (243010448569343/3125000000000 : ℝ)*(sp2) + (196786277382973/5000000000000 : ℝ)*(sp3) + (17534979281/50000000000000 : ℝ)*(sp4) + (451887877/3125000000000 : ℝ)*(sp7) + (983935002017881/25000000000000 : ℝ)*(f.failure) + (388816766716701/5000000000000 : ℝ)*(f.sum) + (2024177543353/856250000000000000000000000 : ℝ)*base66 + (54740351252418193/171250000000000000000000000000000 : ℝ)*base67 + (1193259568966331807/171250000000000000000000000000000 : ℝ)*base70 + (57934586739918193/171250000000000000000000000000000 : ℝ)*base71 + (7010994634363/3425000000000000000000000000 : ℝ)*base73 + (1696548706546331807/171250000000000000000000000000000 : ℝ)*base76 + (669391245469918193/171250000000000000000000000000000 : ℝ)*base77 + (675374783440081807/171250000000000000000000000000000 : ℝ)*base80 + (10843276519/1672363281250000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (528469/100000000000000000000 : ℝ)*base90 + (528469/100000000000000000000 : ℝ)*base92 + (528469/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1603936376422609589203593249/171250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (854583053/50000000000000 : ℝ)*(base19) + (116747791/6250000000000 : ℝ)*(base23) + (18579039/10000000000000 : ℝ)*(upper3) + (70886777/100000000000000 : ℝ)*(lower4) + (190462621/100000000000000 : ℝ)*(upper5) + (2942804531134937/50000000000000 : ℝ)*(major0) + (2942804531134937/50000000000000 : ℝ)*(major1) + (2942804531134937/50000000000000 : ℝ)*(major2) + (182953219/390625000000 : ℝ)*(sp1) + (50500959697/100000000000000 : ℝ)*(sp2) + (7815603437590647/100000000000000 : ℝ)*(sp4) + (3907777446200239/50000000000000 : ℝ)*(sp5) + (1563110213733259/20000000000000 : ℝ)*(sp6) + (24722589842171/625000000000 : ℝ)*(sp7) + (24722589842171/625000000000 : ℝ)*(f.failure) + (7815603437590647/100000000000000 : ℝ)*(f.sum) + (7613374556913/3425000000000000000000000000 : ℝ)*base65 + (3029374378260789639/342500000000000000000000000000000 : ℝ)*base68 + (5490377233390789639/342500000000000000000000000000000 : ℝ)*base70 + (3458360611635789639/342500000000000000000000000000000 : ℝ)*base72 + (3608893922981/1712500000000000000000000000 : ℝ)*base74 + (8565782609615789639/342500000000000000000000000000000 : ℝ)*base76 + (2639425982868289639/342500000000000000000000000000000 : ℝ)*base78 + (10141055233798289639/342500000000000000000000000000000 : ℝ)*base80 + (3204576506737/3425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (24321/2500000000000000000 : ℝ)*base89 + (24321/2500000000000000000 : ℝ)*base91 + (24321/2500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1107_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1107_s8_0 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-43674739/200000000 : ℝ)*x 0 + (2696812973/5000000000 : ℝ)*x 1 + (5265191419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43674739/200000000 : ℝ)^2075 ≤ (13265962096197/100000000000000 : ℝ)^1563 := by
    have hnat : (43674739 : ℕ)^2075*100000000000000^1563 ≤ 13265962096197^1563*200000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43674739 200000000 13265962096197 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696812973/5000000000 : ℝ)^2075 ≤ (275379530753/625000000000 : ℝ)^1563 := by
    have hnat : (2696812973 : ℕ)^2075*625000000000^1563 ≤ 275379530753^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696812973 5000000000 275379530753 625000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265191419/10000000000 : ℝ)^2075 ≤ (21336656482981/50000000000000 : ℝ)^1563 := by
    have hnat : (5265191419 : ℕ)^2075*50000000000000^1563 ≤ 21336656482981^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265191419 10000000000 21336656482981 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-43674739/200000000 : ℝ), (2696812973/5000000000 : ℝ), (5265191419/10000000000 : ℝ)] ![(13265962096197/100000000000000 : ℝ), (275379530753/625000000000 : ℝ), (21336656482981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-43674739/200000000 : ℝ)|^2075 ≤ (13265962096197/100000000000000 : ℝ)^1563
        have hw : |(-43674739/200000000 : ℝ)|=(43674739/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696812973/5000000000 : ℝ)|^2075 ≤ (275379530753/625000000000 : ℝ)^1563
        have hw : |(2696812973/5000000000 : ℝ)|=(2696812973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265191419/10000000000 : ℝ)|^2075 ≤ (21336656482981/50000000000000 : ℝ)^1563
        have hw : |(5265191419/10000000000 : ℝ)|=(5265191419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_1 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336216937/2500000000 : ℝ)*x 0 + (-562222593/2500000000 : ℝ)*x 1 + (2632595417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336216937/2500000000 : ℝ)^2075 ≤ (43532726326699/100000000000000 : ℝ)^1563 := by
    have hnat : (1336216937 : ℕ)^2075*100000000000000^1563 ≤ 43532726326699^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336216937 2500000000 43532726326699 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562222593/2500000000 : ℝ)^2075 ≤ (6896983491383/50000000000000 : ℝ)^1563 := by
    have hnat : (562222593 : ℕ)^2075*50000000000000^1563 ≤ 6896983491383^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562222593 2500000000 6896983491383 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632595417/5000000000 : ℝ)^2075 ≤ (42673306671521/100000000000000 : ℝ)^1563 := by
    have hnat : (2632595417 : ℕ)^2075*100000000000000^1563 ≤ 42673306671521^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632595417 5000000000 42673306671521 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336216937/2500000000 : ℝ), (-562222593/2500000000 : ℝ), (2632595417/5000000000 : ℝ)] ![(43532726326699/100000000000000 : ℝ), (6896983491383/50000000000000 : ℝ), (42673306671521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336216937/2500000000 : ℝ)|^2075 ≤ (43532726326699/100000000000000 : ℝ)^1563
        have hw : |(1336216937/2500000000 : ℝ)|=(1336216937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562222593/2500000000 : ℝ)|^2075 ≤ (6896983491383/50000000000000 : ℝ)^1563
        have hw : |(-562222593/2500000000 : ℝ)|=(562222593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632595417/5000000000 : ℝ)|^2075 ≤ (42673306671521/100000000000000 : ℝ)^1563
        have hw : |(2632595417/5000000000 : ℝ)|=(2632595417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_2 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336217091/2500000000 : ℝ)*x 0 + (2632595071/5000000000 : ℝ)*x 1 + (-562222617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336217091/2500000000 : ℝ)^2075 ≤ (21766366493691/50000000000000 : ℝ)^1563 := by
    have hnat : (1336217091 : ℕ)^2075*50000000000000^1563 ≤ 21766366493691^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336217091 2500000000 21766366493691 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632595071/5000000000 : ℝ)^2075 ≤ (42673299225789/100000000000000 : ℝ)^1563 := by
    have hnat : (2632595071 : ℕ)^2075*100000000000000^1563 ≤ 42673299225789^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632595071 5000000000 42673299225789 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562222617/2500000000 : ℝ)^2075 ≤ (6896983882243/50000000000000 : ℝ)^1563 := by
    have hnat : (562222617 : ℕ)^2075*50000000000000^1563 ≤ 6896983882243^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562222617 2500000000 6896983882243 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336217091/2500000000 : ℝ), (2632595071/5000000000 : ℝ), (-562222617/2500000000 : ℝ)] ![(21766366493691/50000000000000 : ℝ), (42673299225789/100000000000000 : ℝ), (6896983882243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336217091/2500000000 : ℝ)|^2075 ≤ (21766366493691/50000000000000 : ℝ)^1563
        have hw : |(1336217091/2500000000 : ℝ)|=(1336217091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632595071/5000000000 : ℝ)|^2075 ≤ (42673299225789/100000000000000 : ℝ)^1563
        have hw : |(2632595071/5000000000 : ℝ)|=(2632595071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-562222617/2500000000 : ℝ)|^2075 ≤ (6896983882243/50000000000000 : ℝ)^1563
        have hw : |(-562222617/2500000000 : ℝ)|=(562222617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_3 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1092407237/2500000000 : ℝ)*x 0 + (2122297499/5000000000 : ℝ)*x 1 + (2249179843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092407237/2500000000 : ℝ)^2075 ≤ (1665839392443/5000000000000 : ℝ)^1563 := by
    have hnat : (1092407237 : ℕ)^2075*5000000000000^1563 ≤ 1665839392443^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092407237 2500000000 1665839392443 5000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122297499/5000000000 : ℝ)^2075 ≤ (32057131201031/100000000000000 : ℝ)^1563 := by
    have hnat : (2122297499 : ℕ)^2075*100000000000000^1563 ≤ 32057131201031^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122297499 5000000000 32057131201031 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249179843/5000000000 : ℝ)^2075 ≤ (6925216187539/20000000000000 : ℝ)^1563 := by
    have hnat : (2249179843 : ℕ)^2075*20000000000000^1563 ≤ 6925216187539^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249179843 5000000000 6925216187539 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092407237/2500000000 : ℝ), (2122297499/5000000000 : ℝ), (2249179843/5000000000 : ℝ)] ![(1665839392443/5000000000000 : ℝ), (32057131201031/100000000000000 : ℝ), (6925216187539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092407237/2500000000 : ℝ)|^2075 ≤ (1665839392443/5000000000000 : ℝ)^1563
        have hw : |(1092407237/2500000000 : ℝ)|=(1092407237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122297499/5000000000 : ℝ)|^2075 ≤ (32057131201031/100000000000000 : ℝ)^1563
        have hw : |(2122297499/5000000000 : ℝ)|=(2122297499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249179843/5000000000 : ℝ)|^2075 ≤ (6925216187539/20000000000000 : ℝ)^1563
        have hw : |(2249179843/5000000000 : ℝ)|=(2249179843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_4 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2183742057/10000000000 : ℝ)*x 0 + (1316378279/2500000000 : ℝ)*x 1 + (215732119/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183742057/10000000000 : ℝ)^2075 ≤ (13266003283521/100000000000000 : ℝ)^1563 := by
    have hnat : (2183742057 : ℕ)^2075*100000000000000^1563 ≤ 13266003283521^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183742057 10000000000 13266003283521 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316378279/2500000000 : ℝ)^2075 ≤ (10669193593257/25000000000000 : ℝ)^1563 := by
    have hnat : (1316378279 : ℕ)^2075*25000000000000^1563 ≤ 10669193593257^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316378279 2500000000 10669193593257 25000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215732119/400000000 : ℝ)^2075 ≤ (44057222331269/100000000000000 : ℝ)^1563 := by
    have hnat : (215732119 : ℕ)^2075*100000000000000^1563 ≤ 44057222331269^1563*400000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215732119 400000000 44057222331269 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2183742057/10000000000 : ℝ), (1316378279/2500000000 : ℝ), (215732119/400000000 : ℝ)] ![(13266003283521/100000000000000 : ℝ), (10669193593257/25000000000000 : ℝ), (44057222331269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2183742057/10000000000 : ℝ)|^2075 ≤ (13266003283521/100000000000000 : ℝ)^1563
        have hw : |(-2183742057/10000000000 : ℝ)|=(2183742057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316378279/2500000000 : ℝ)|^2075 ≤ (10669193593257/25000000000000 : ℝ)^1563
        have hw : |(1316378279/2500000000 : ℝ)|=(1316378279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215732119/400000000 : ℝ)|^2075 ≤ (44057222331269/100000000000000 : ℝ)^1563
        have hw : |(215732119/400000000 : ℝ)|=(215732119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_5 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312413689/10000000000 : ℝ)*x 0 + (-1060389089/5000000000 : ℝ)*x 1 + (269665149/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312413689/10000000000 : ℝ)^2075 ≤ (8636431333173/20000000000000 : ℝ)^1563 := by
    have hnat : (5312413689 : ℕ)^2075*20000000000000^1563 ≤ 8636431333173^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312413689 10000000000 8636431333173 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060389089/5000000000 : ℝ)^2075 ≤ (2552124186783/20000000000000 : ℝ)^1563 := by
    have hnat : (1060389089 : ℕ)^2075*20000000000000^1563 ≤ 2552124186783^1563*5000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060389089 5000000000 2552124186783 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269665149/500000000 : ℝ)^2075 ≤ (44057222385493/100000000000000 : ℝ)^1563 := by
    have hnat : (269665149 : ℕ)^2075*100000000000000^1563 ≤ 44057222385493^1563*500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269665149 500000000 44057222385493 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312413689/10000000000 : ℝ), (-1060389089/5000000000 : ℝ), (269665149/500000000 : ℝ)] ![(8636431333173/20000000000000 : ℝ), (2552124186783/20000000000000 : ℝ), (44057222385493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312413689/10000000000 : ℝ)|^2075 ≤ (8636431333173/20000000000000 : ℝ)^1563
        have hw : |(5312413689/10000000000 : ℝ)|=(5312413689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060389089/5000000000 : ℝ)|^2075 ≤ (2552124186783/20000000000000 : ℝ)^1563
        have hw : |(-1060389089/5000000000 : ℝ)|=(1060389089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269665149/500000000 : ℝ)|^2075 ≤ (44057222385493/100000000000000 : ℝ)^1563
        have hw : |(269665149/500000000 : ℝ)|=(269665149/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_6 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (664051709/1250000000 : ℝ)*x 0 + (5393302983/10000000000 : ℝ)*x 1 + (-2120778197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664051709/1250000000 : ℝ)^2075 ≤ (21591078241207/50000000000000 : ℝ)^1563 := by
    have hnat : (664051709 : ℕ)^2075*50000000000000^1563 ≤ 21591078241207^1563*1250000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664051709 1250000000 21591078241207 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393302983/10000000000 : ℝ)^2075 ≤ (44057222418027/100000000000000 : ℝ)^1563 := by
    have hnat : (5393302983 : ℕ)^2075*100000000000000^1563 ≤ 44057222418027^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393302983 10000000000 44057222418027 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120778197/10000000000 : ℝ)^2075 ≤ (6380310542843/50000000000000 : ℝ)^1563 := by
    have hnat : (2120778197 : ℕ)^2075*50000000000000^1563 ≤ 6380310542843^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120778197 10000000000 6380310542843 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664051709/1250000000 : ℝ), (5393302983/10000000000 : ℝ), (-2120778197/10000000000 : ℝ)] ![(21591078241207/50000000000000 : ℝ), (44057222418027/100000000000000 : ℝ), (6380310542843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664051709/1250000000 : ℝ)|^2075 ≤ (21591078241207/50000000000000 : ℝ)^1563
        have hw : |(664051709/1250000000 : ℝ)|=(664051709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393302983/10000000000 : ℝ)|^2075 ≤ (44057222418027/100000000000000 : ℝ)^1563
        have hw : |(5393302983/10000000000 : ℝ)|=(5393302983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2120778197/10000000000 : ℝ)|^2075 ≤ (6380310542843/50000000000000 : ℝ)^1563
        have hw : |(-2120778197/10000000000 : ℝ)|=(2120778197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1107_s8_7 (p : ℝ) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1092409703/2500000000 : ℝ)*x 0 + (4497723681/10000000000 : ℝ)*x 1 + (4245233227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092409703/2500000000 : ℝ)^2075 ≤ (6663377538983/20000000000000 : ℝ)^1563 := by
    have hnat : (1092409703 : ℕ)^2075*20000000000000^1563 ≤ 6663377538983^1563*2500000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092409703 2500000000 6663377538983 20000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497723681/10000000000 : ℝ)^2075 ≤ (34619581754827/100000000000000 : ℝ)^1563 := by
    have hnat : (4497723681 : ℕ)^2075*100000000000000^1563 ≤ 34619581754827^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497723681 10000000000 34619581754827 100000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245233227/10000000000 : ℝ)^2075 ≤ (16031765267301/50000000000000 : ℝ)^1563 := by
    have hnat : (4245233227 : ℕ)^2075*50000000000000^1563 ≤ 16031765267301^1563*10000000000^2075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245233227 10000000000 16031765267301 50000000000000 2075 1563 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2075/512 : ℝ)) 2075 1563 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092409703/2500000000 : ℝ), (4497723681/10000000000 : ℝ), (4245233227/10000000000 : ℝ)] ![(6663377538983/20000000000000 : ℝ), (34619581754827/100000000000000 : ℝ), (16031765267301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092409703/2500000000 : ℝ)|^2075 ≤ (6663377538983/20000000000000 : ℝ)^1563
        have hw : |(1092409703/2500000000 : ℝ)|=(1092409703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497723681/10000000000 : ℝ)|^2075 ≤ (34619581754827/100000000000000 : ℝ)^1563
        have hw : |(4497723681/10000000000 : ℝ)|=(4497723681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245233227/10000000000 : ℝ)|^2075 ≤ (16031765267301/50000000000000 : ℝ)^1563
        have hw : |(4245233227/10000000000 : ℝ)|=(4245233227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1107_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3507/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5653/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5653/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5653/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5653/50000 : ℝ) ^ (8299/2048 : ℝ) ≤ (7290293637180411/50000000000000000000 : ℝ) := by
    have hpowers : (5653/50000 : ℝ)^8299 ≤ (7290293637180411/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5653 : ℕ)^8299*50000000000000000000^2048 ≤ 7290293637180411^2048*50000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5653 50000 7290293637180411 50000000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5653/50000 : ℝ)) (X := (7290293637180411/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1403/10000 : ℝ) ^ (8299/2048 : ℝ) ≤ (4370969662876829/12500000000000000000 : ℝ) := by
    have hpowers : (1403/10000 : ℝ)^8299 ≤ (4370969662876829/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1403 : ℕ)^8299*12500000000000000000^2048 ≤ 4370969662876829^2048*10000^8299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 10000 4370969662876829 12500000000000000000 8299 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/10000 : ℝ)) (X := (4370969662876829/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007290293637180411/25000000000000000000 : ℝ) ≤ (5000359775440731/5000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (25007290293637180411/25000000000000000000 : ℝ)^2048 ≤ (5000359775440731/5000000000000000 : ℝ)^8299 := by
      have hnat : (25007290293637180411 : ℕ)^2048*5000000000000000^8299 ≤ 5000359775440731^8299*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007290293637180411 25000000000000000000 5000359775440731 5000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359775440731/5000000000000000 : ℝ)) (X := (25007290293637180411/25000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024774172288687727/50000000000000000000 : ℝ) ≤ (10001222509693319/10000000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (50024774172288687727/50000000000000000000 : ℝ)^2048 ≤ (10001222509693319/10000000000000000 : ℝ)^8299 := by
      have hnat : (50024774172288687727 : ℕ)^2048*10000000000000000^8299 ≤ 10001222509693319^8299*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024774172288687727 50000000000000000000 10001222509693319 10000000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001222509693319/10000000000000000 : ℝ)) (X := (50024774172288687727/50000000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254370969662876829/6250000000000000000 : ℝ) ≤ (1250215683563147/1250000000000000 : ℝ) ^ (8299/2048 : ℝ) := by
    have hpowers : (6254370969662876829/6250000000000000000 : ℝ)^2048 ≤ (1250215683563147/1250000000000000 : ℝ)^8299 := by
      have hnat : (6254370969662876829 : ℕ)^2048*1250000000000000^8299 ≤ 1250215683563147^8299*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254370969662876829 6250000000000000000 1250215683563147 1250000000000000 2048 8299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250215683563147/1250000000000000 : ℝ)) (X := (6254370969662876829/6250000000000000000 : ℝ)) (by norm_num) 8299 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7290293637180411/50000000000000000000 : ℝ) ≤ ((6807646787986848001/6810000000000000000 : ℝ)+2*(502958811857/272400000000000 : ℝ)*(5653/50000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (6807646787986848001/6810000000000000000 : ℝ)+2*(502958811857/272400000000000 : ℝ)*(5653/50000 : ℝ)=(5000359775440731/5000000000000000 : ℝ) by norm_num, show 1+2*(7290293637180411/50000000000000000000 : ℝ)=(25007290293637180411/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4370969662876829/12500000000000000000 : ℝ)+(7290293637180411/50000000000000000000 : ℝ) ≤ ((6807646787986848001/6810000000000000000 : ℝ)+(502958811857/272400000000000 : ℝ)*((1403/10000 : ℝ)+(5653/50000 : ℝ)))^(8299/2048 : ℝ) := by
    rw [show (6807646787986848001/6810000000000000000 : ℝ)+(502958811857/272400000000000 : ℝ)*((1403/10000 : ℝ)+(5653/50000 : ℝ))=(10001222509693319/10000000000000000 : ℝ) by norm_num, show 1+(4370969662876829/12500000000000000000 : ℝ)+(7290293637180411/50000000000000000000 : ℝ)=(50024774172288687727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4370969662876829/12500000000000000000 : ℝ) ≤ ((6807646787986848001/6810000000000000000 : ℝ)+2*(502958811857/272400000000000 : ℝ)*(1403/10000 : ℝ))^(8299/2048 : ℝ) := by
    rw [show (6807646787986848001/6810000000000000000 : ℝ)+2*(502958811857/272400000000000 : ℝ)*(1403/10000 : ℝ)=(1250215683563147/1250000000000000 : ℝ) by norm_num, show 1+2*(4370969662876829/12500000000000000000 : ℝ)=(6254370969662876829/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6807646787986848001/6810000000000000000 : ℝ)*(X 1 0+X 2 0)+(502958811857/272400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (6807646787986848001/6810000000000000000 : ℝ)) (alpha := (502958811857/272400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6807646787986848001/6810000000000000000 : ℝ)*(X 0 1+X 2 1)+(502958811857/272400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (6807646787986848001/6810000000000000000 : ℝ)) (alpha := (502958811857/272400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6807646787986848001/6810000000000000000 : ℝ)*(X 0 2+X 1 2)+(502958811857/272400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8299/2048 : ℝ)) (lo := (5653/50000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (6807646787986848001/6810000000000000000 : ℝ)) (alpha := (502958811857/272400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-43674739/200000000 : ℝ)*X 0 0+(2696812973/5000000000 : ℝ)*X 0 1+(5265191419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336216937/2500000000 : ℝ)*X 1 0+(-562222593/2500000000 : ℝ)*X 1 1+(2632595417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336217091/2500000000 : ℝ)*X 2 0+(2632595071/5000000000 : ℝ)*X 2 1+(-562222617/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092407237/2500000000 : ℝ)*X 0 0+(2122297499/5000000000 : ℝ)*X 0 1+(2249179843/5000000000 : ℝ)*X 0 2+(1092407237/2500000000 : ℝ)*X 1 0+(2122297499/5000000000 : ℝ)*X 1 1+(2249179843/5000000000 : ℝ)*X 1 2+(1092407237/2500000000 : ℝ)*X 2 0+(2122297499/5000000000 : ℝ)*X 2 1+(2249179843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2183742057/10000000000 : ℝ)*X 0 0+(1316378279/2500000000 : ℝ)*X 0 1+(215732119/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312413689/10000000000 : ℝ)*X 1 0+(-1060389089/5000000000 : ℝ)*X 1 1+(269665149/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664051709/1250000000 : ℝ)*X 2 0+(5393302983/10000000000 : ℝ)*X 2 1+(-2120778197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092409703/2500000000 : ℝ)*X 0 0+(4497723681/10000000000 : ℝ)*X 0 1+(4245233227/10000000000 : ℝ)*X 0 2+(1092409703/2500000000 : ℝ)*X 1 0+(4497723681/10000000000 : ℝ)*X 1 1+(4245233227/10000000000 : ℝ)*X 1 2+(1092409703/2500000000 : ℝ)*X 2 0+(4497723681/10000000000 : ℝ)*X 2 1+(4245233227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1107_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10988419468234435143951/1135000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1016745579/50000000000000 : ℝ)*(base19) + (1320325581/50000000000000 : ℝ)*(base23) + (77552563/50000000000000 : ℝ)*(lower2) + (55932699/25000000000000 : ℝ)*(upper3) + (5919133/25000000000000 : ℝ)*(upper5) + (732924703861497/12500000000000 : ℝ)*(major0) + (732924703861497/12500000000000 : ℝ)*(major1) + (732924703861497/12500000000000 : ℝ)*(major2) + (7786086339804011/100000000000000 : ℝ)*(sp0) + (3893053221678457/50000000000000 : ℝ)*(sp1) + (778610583619691/10000000000000 : ℝ)*(sp2) + (3940667323444629/100000000000000 : ℝ)*(sp3) + (11068522031/50000000000000 : ℝ)*(sp4) + (9569388507/50000000000000 : ℝ)*(sp7) + (3940686462221643/100000000000000 : ℝ)*(f.failure) + (973263559606009/12500000000000 : ℝ)*(f.sum) + (612363435513/567500000000000000000000000 : ℝ)*base65 + (82887414451902501/28375000000000000000000000000000 : ℝ)*base68 + (173494448105722499/28375000000000000000000000000000 : ℝ)*base69 + (324647421447652501/28375000000000000000000000000000 : ℝ)*base72 + (462295669553/567500000000000000000000000 : ℝ)*base73 + (467639339448347499/28375000000000000000000000000000 : ℝ)*base75 + (660668301939652501/28375000000000000000000000000000 : ℝ)*base78 + (113255493148847499/28375000000000000000000000000000 : ℝ)*base79 + (5525522427183/567500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (217407/400000000000000000000 : ℝ)*base90 + (217407/400000000000000000000 : ℝ)*base92 + (217407/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76625930268807627024160231/11350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256319371/20000000000000 : ℝ)*(base19) + (336337731/25000000000000 : ℝ)*(base23) + (459014567/100000000000000 : ℝ)*(lower1) + (67645457/50000000000000 : ℝ)*(upper3) + (44472033/100000000000000 : ℝ)*(lower4) + (27995109/20000000000000 : ℝ)*(upper5) + (1178583703559731/20000000000000 : ℝ)*(major0) + (1178583703559731/20000000000000 : ℝ)*(major1) + (1178583703559731/20000000000000 : ℝ)*(major2) + (415933639/50000000000000 : ℝ)*(sp2) + (3912654939629251/50000000000000 : ℝ)*(sp4) + (489081787353853/6250000000000 : ℝ)*(sp5) + (78253077020403/1000000000000 : ℝ)*(sp6) + (495065866412417/12500000000000 : ℝ)*(sp7) + (495065866412417/12500000000000 : ℝ)*(f.failure) + (3912654939629251/50000000000000 : ℝ)*(f.sum) + (181865179327/544800000000000000000000000 : ℝ)*base65 + (635803358251492423/45400000000000000000000000000000 : ℝ)*base68 + (93518185651092423/45400000000000000000000000000000 : ℝ)*base70 + (3544136494126107577/45400000000000000000000000000000 : ℝ)*base71 + (13630427947261/2724000000000000000000000000 : ℝ)*base74 + (7246718014237092423/45400000000000000000000000000000 : ℝ)*base76 + (406502285401892423/45400000000000000000000000000000 : ℝ)*base78 + (96391255189092423/45400000000000000000000000000000 : ℝ)*base80 + (524403652553/544800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (550467/50000000000000000000 : ℝ)*base89 + (550467/50000000000000000000 : ℝ)*base91 + (550467/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1107_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1107_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1107_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1107_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1107_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1107_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8299/2048 : ℝ) ≤ p) (hpb : p ≤ (2075/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5951651/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1107_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

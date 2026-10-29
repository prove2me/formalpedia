-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1528_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:46.512989+00:00
-- url     : https://prove2.me/submissions/dd8eef09-e936-4d0c-8818-e32464acbb72

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
theorem support_rectangle_w1528_s0_0 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1668995459/10000000000 : ℝ)*x 0 + (737576899/1250000000 : ℝ)*x 1 + (243105083/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1668995459/10000000000 : ℝ)^4553 ≤ (1985487471237/20000000000000 : ℝ)^3529 := by
    have hnat : (1668995459 : ℕ)^4553*20000000000000^3529 ≤ 1985487471237^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668995459 10000000000 1985487471237 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737576899/1250000000 : ℝ)^4553 ≤ (50631314793247/100000000000000 : ℝ)^3529 := by
    have hnat : (737576899 : ℕ)^4553*100000000000000^3529 ≤ 50631314793247^3529*1250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737576899 1250000000 50631314793247 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243105083/500000000 : ℝ)^4553 ≤ (19720623917131/50000000000000 : ℝ)^3529 := by
    have hnat : (243105083 : ℕ)^4553*50000000000000^3529 ≤ 19720623917131^3529*500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243105083 500000000 19720623917131 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1668995459/10000000000 : ℝ), (737576899/1250000000 : ℝ), (243105083/500000000 : ℝ)] ![(1985487471237/20000000000000 : ℝ), (50631314793247/100000000000000 : ℝ), (19720623917131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1668995459/10000000000 : ℝ)|^4553 ≤ (1985487471237/20000000000000 : ℝ)^3529
        have hw : |(-1668995459/10000000000 : ℝ)|=(1668995459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737576899/1250000000 : ℝ)|^4553 ≤ (50631314793247/100000000000000 : ℝ)^3529
        have hw : |(737576899/1250000000 : ℝ)|=(737576899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243105083/500000000 : ℝ)|^4553 ≤ (19720623917131/50000000000000 : ℝ)^3529
        have hw : |(243105083/500000000 : ℝ)|=(243105083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_1 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1094901379/2000000000 : ℝ)*x 0 + (-140619629/625000000 : ℝ)*x 1 + (4862101551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094901379/2000000000 : ℝ)^4553 ≤ (1838574808931/4000000000000 : ℝ)^3529 := by
    have hnat : (1094901379 : ℕ)^4553*4000000000000^3529 ≤ 1838574808931^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094901379 2000000000 1838574808931 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140619629/625000000 : ℝ)^4553 ≤ (14594383071743/100000000000000 : ℝ)^3529 := by
    have hnat : (140619629 : ℕ)^4553*100000000000000^3529 ≤ 14594383071743^3529*625000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140619629 625000000 14594383071743 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4862101551/10000000000 : ℝ)^4553 ≤ (39441246693489/100000000000000 : ℝ)^3529 := by
    have hnat : (4862101551 : ℕ)^4553*100000000000000^3529 ≤ 39441246693489^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862101551 10000000000 39441246693489 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094901379/2000000000 : ℝ), (-140619629/625000000 : ℝ), (4862101551/10000000000 : ℝ)] ![(1838574808931/4000000000000 : ℝ), (14594383071743/100000000000000 : ℝ), (39441246693489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094901379/2000000000 : ℝ)|^4553 ≤ (1838574808931/4000000000000 : ℝ)^3529
        have hw : |(1094901379/2000000000 : ℝ)|=(1094901379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140619629/625000000 : ℝ)|^4553 ≤ (14594383071743/100000000000000 : ℝ)^3529
        have hw : |(-140619629/625000000 : ℝ)|=(140619629/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4862101551/10000000000 : ℝ)|^4553 ≤ (39441246693489/100000000000000 : ℝ)^3529
        have hw : |(4862101551/10000000000 : ℝ)|=(4862101551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_2 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1368626767/2500000000 : ℝ)*x 0 + (303881353/625000000 : ℝ)*x 1 + (-1124956859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368626767/2500000000 : ℝ)^4553 ≤ (4596437209727/10000000000000 : ℝ)^3529 := by
    have hnat : (1368626767 : ℕ)^4553*10000000000000^3529 ≤ 4596437209727^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368626767 2500000000 4596437209727 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303881353/625000000 : ℝ)^4553 ≤ (77033686931/195312500000 : ℝ)^3529 := by
    have hnat : (303881353 : ℕ)^4553*195312500000^3529 ≤ 77033686931^3529*625000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303881353 625000000 77033686931 195312500000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124956859/5000000000 : ℝ)^4553 ≤ (14594380176121/100000000000000 : ℝ)^3529 := by
    have hnat : (1124956859 : ℕ)^4553*100000000000000^3529 ≤ 14594380176121^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124956859 5000000000 14594380176121 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1368626767/2500000000 : ℝ), (303881353/625000000 : ℝ), (-1124956859/5000000000 : ℝ)] ![(4596437209727/10000000000000 : ℝ), (77033686931/195312500000 : ℝ), (14594380176121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1368626767/2500000000 : ℝ)|^4553 ≤ (4596437209727/10000000000000 : ℝ)^3529
        have hw : |(1368626767/2500000000 : ℝ)|=(1368626767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303881353/625000000 : ℝ)|^4553 ≤ (77033686931/195312500000 : ℝ)^3529
        have hw : |(303881353/625000000 : ℝ)|=(303881353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1124956859/5000000000 : ℝ)|^4553 ≤ (14594380176121/100000000000000 : ℝ)^3529
        have hw : |(-1124956859/5000000000 : ℝ)|=(1124956859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_3 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035214237/2500000000 : ℝ)*x 0 + (3091511917/10000000000 : ℝ)*x 1 + (136825121/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035214237/2500000000 : ℝ)^4553 ≤ (32061392154213/100000000000000 : ℝ)^3529 := by
    have hnat : (1035214237 : ℕ)^4553*100000000000000^3529 ≤ 32061392154213^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035214237 2500000000 32061392154213 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091511917/10000000000 : ℝ)^4553 ≤ (21990507733351/100000000000000 : ℝ)^3529 := by
    have hnat : (3091511917 : ℕ)^4553*100000000000000^3529 ≤ 21990507733351^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091511917 10000000000 21990507733351 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136825121/250000000 : ℝ)^4553 ≤ (45948100099951/100000000000000 : ℝ)^3529 := by
    have hnat : (136825121 : ℕ)^4553*100000000000000^3529 ≤ 45948100099951^3529*250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136825121 250000000 45948100099951 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035214237/2500000000 : ℝ), (3091511917/10000000000 : ℝ), (136825121/250000000 : ℝ)] ![(32061392154213/100000000000000 : ℝ), (21990507733351/100000000000000 : ℝ), (45948100099951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035214237/2500000000 : ℝ)|^4553 ≤ (32061392154213/100000000000000 : ℝ)^3529
        have hw : |(1035214237/2500000000 : ℝ)|=(1035214237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091511917/10000000000 : ℝ)|^4553 ≤ (21990507733351/100000000000000 : ℝ)^3529
        have hw : |(3091511917/10000000000 : ℝ)|=(3091511917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136825121/250000000 : ℝ)|^4553 ≤ (45948100099951/100000000000000 : ℝ)^3529
        have hw : |(136825121/250000000 : ℝ)|=(136825121/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_4 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1672381269/10000000000 : ℝ)*x 0 + (1222127201/2500000000 : ℝ)*x 1 + (5873264703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1672381269/10000000000 : ℝ)^4553 ≤ (77761156849/781250000000 : ℝ)^3529 := by
    have hnat : (1672381269 : ℕ)^4553*781250000000^3529 ≤ 77761156849^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672381269 10000000000 77761156849 781250000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1222127201/2500000000 : ℝ)^4553 ≤ (39717837328209/100000000000000 : ℝ)^3529 := by
    have hnat : (1222127201 : ℕ)^4553*100000000000000^3529 ≤ 39717837328209^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222127201 2500000000 39717837328209 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5873264703/10000000000 : ℝ)^4553 ≤ (50328734582277/100000000000000 : ℝ)^3529 := by
    have hnat : (5873264703 : ℕ)^4553*100000000000000^3529 ≤ 50328734582277^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5873264703 10000000000 50328734582277 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1672381269/10000000000 : ℝ), (1222127201/2500000000 : ℝ), (5873264703/10000000000 : ℝ)] ![(77761156849/781250000000 : ℝ), (39717837328209/100000000000000 : ℝ), (50328734582277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1672381269/10000000000 : ℝ)|^4553 ≤ (77761156849/781250000000 : ℝ)^3529
        have hw : |(-1672381269/10000000000 : ℝ)|=(1672381269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1222127201/2500000000 : ℝ)|^4553 ≤ (39717837328209/100000000000000 : ℝ)^3529
        have hw : |(1222127201/2500000000 : ℝ)|=(1222127201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5873264703/10000000000 : ℝ)|^4553 ≤ (50328734582277/100000000000000 : ℝ)^3529
        have hw : |(5873264703/10000000000 : ℝ)|=(5873264703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_5 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324419289/625000000 : ℝ)*x 0 + (-123875109/1000000000 : ℝ)*x 1 + (146831619/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324419289/625000000 : ℝ)^4553 ≤ (10728395567759/25000000000000 : ℝ)^3529 := by
    have hnat : (324419289 : ℕ)^4553*25000000000000^3529 ≤ 10728395567759^3529*625000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324419289 625000000 10728395567759 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123875109/1000000000 : ℝ)^4553 ≤ (844710313067/12500000000000 : ℝ)^3529 := by
    have hnat : (123875109 : ℕ)^4553*12500000000000^3529 ≤ 844710313067^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123875109 1000000000 844710313067 12500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146831619/250000000 : ℝ)^4553 ≤ (50328735212447/100000000000000 : ℝ)^3529 := by
    have hnat : (146831619 : ℕ)^4553*100000000000000^3529 ≤ 50328735212447^3529*250000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146831619 250000000 50328735212447 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324419289/625000000 : ℝ), (-123875109/1000000000 : ℝ), (146831619/250000000 : ℝ)] ![(10728395567759/25000000000000 : ℝ), (844710313067/12500000000000 : ℝ), (50328735212447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324419289/625000000 : ℝ)|^4553 ≤ (10728395567759/25000000000000 : ℝ)^3529
        have hw : |(324419289/625000000 : ℝ)|=(324419289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123875109/1000000000 : ℝ)|^4553 ≤ (844710313067/12500000000000 : ℝ)^3529
        have hw : |(-123875109/1000000000 : ℝ)|=(123875109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146831619/250000000 : ℝ)|^4553 ≤ (50328735212447/100000000000000 : ℝ)^3529
        have hw : |(146831619/250000000 : ℝ)|=(146831619/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_6 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259535429/500000000 : ℝ)*x 0 + (2936632497/5000000000 : ℝ)*x 1 + (-1238750789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259535429/500000000 : ℝ)^4553 ≤ (42913581801719/100000000000000 : ℝ)^3529 := by
    have hnat : (259535429 : ℕ)^4553*100000000000000^3529 ≤ 42913581801719^3529*500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259535429 500000000 42913581801719 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2936632497/5000000000 : ℝ)^4553 ≤ (25164368899729/50000000000000 : ℝ)^3529 := by
    have hnat : (2936632497 : ℕ)^4553*50000000000000^3529 ≤ 25164368899729^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2936632497 5000000000 25164368899729 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1238750789/10000000000 : ℝ)^4553 ≤ (6757680386047/100000000000000 : ℝ)^3529 := by
    have hnat : (1238750789 : ℕ)^4553*100000000000000^3529 ≤ 6757680386047^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238750789 10000000000 6757680386047 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259535429/500000000 : ℝ), (2936632497/5000000000 : ℝ), (-1238750789/10000000000 : ℝ)] ![(42913581801719/100000000000000 : ℝ), (25164368899729/50000000000000 : ℝ), (6757680386047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259535429/500000000 : ℝ)|^4553 ≤ (42913581801719/100000000000000 : ℝ)^3529
        have hw : |(259535429/500000000 : ℝ)|=(259535429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2936632497/5000000000 : ℝ)|^4553 ≤ (25164368899729/50000000000000 : ℝ)^3529
        have hw : |(2936632497/5000000000 : ℝ)|=(2936632497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1238750789/10000000000 : ℝ)|^4553 ≤ (6757680386047/100000000000000 : ℝ)^3529
        have hw : |(-1238750789/10000000000 : ℝ)|=(1238750789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s0_7 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037155261/2500000000 : ℝ)*x 0 + (5412448699/10000000000 : ℝ)*x 1 + (315423159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037155261/2500000000 : ℝ)^4553 ≤ (16069485839107/50000000000000 : ℝ)^3529 := by
    have hnat : (1037155261 : ℕ)^4553*50000000000000^3529 ≤ 16069485839107^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037155261 2500000000 16069485839107 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412448699/10000000000 : ℝ)^4553 ≤ (22646621644529/50000000000000 : ℝ)^3529 := by
    have hnat : (5412448699 : ℕ)^4553*50000000000000^3529 ≤ 22646621644529^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412448699 10000000000 22646621644529 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315423159/1000000000 : ℝ)^4553 ≤ (22567785024619/100000000000000 : ℝ)^3529 := by
    have hnat : (315423159 : ℕ)^4553*100000000000000^3529 ≤ 22567785024619^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315423159 1000000000 22567785024619 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037155261/2500000000 : ℝ), (5412448699/10000000000 : ℝ), (315423159/1000000000 : ℝ)] ![(16069485839107/50000000000000 : ℝ), (22646621644529/50000000000000 : ℝ), (22567785024619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037155261/2500000000 : ℝ)|^4553 ≤ (16069485839107/50000000000000 : ℝ)^3529
        have hw : |(1037155261/2500000000 : ℝ)|=(1037155261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412448699/10000000000 : ℝ)|^4553 ≤ (22646621644529/50000000000000 : ℝ)^3529
        have hw : |(5412448699/10000000000 : ℝ)|=(5412448699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315423159/1000000000 : ℝ)|^4553 ≤ (22567785024619/100000000000000 : ℝ)^3529
        have hw : |(315423159/1000000000 : ℝ)|=(315423159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1528_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3031/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25279/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4551/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4551 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4551*1^1024 ≤ 0^1024*1^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4551/1024 : ℝ) ≤ (1703809041230176813/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4551 ≤ (1703809041230176813/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4551*100000000000000000000^1024 ≤ 1703809041230176813^1024*5^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1703809041230176813 100000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1703809041230176813/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4551 := by
      have hnat : (1 : ℕ)^1024*1^4551 ≤ 1^4551*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101703809041230176813/100000000000000000000 : ℝ) ≤ (627380378403981/625000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (101703809041230176813/100000000000000000000 : ℝ)^1024 ≤ (627380378403981/625000000000000 : ℝ)^4551 := by
      have hnat : (101703809041230176813 : ℕ)^1024*625000000000000^4551 ≤ 627380378403981^4551*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101703809041230176813 100000000000000000000 627380378403981 625000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627380378403981/625000000000000 : ℝ)) (X := (101703809041230176813/100000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51703809041230176813/50000000000000000000 : ℝ) ≤ (314880378403981/312500000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (51703809041230176813/50000000000000000000 : ℝ)^1024 ≤ (314880378403981/312500000000000 : ℝ)^4551 := by
      have hnat : (51703809041230176813 : ℕ)^1024*312500000000000^4551 ≤ 314880378403981^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51703809041230176813 50000000000000000000 314880378403981 312500000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314880378403981/312500000000000 : ℝ)) (X := (51703809041230176813/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2380378403981/250000000000000 : ℝ)*(0 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2380378403981/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1703809041230176813/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2380378403981/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4551/1024 : ℝ) := by
    rw [show (1 : ℝ)+(2380378403981/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(627380378403981/625000000000000 : ℝ) by norm_num, show 1+(1703809041230176813/100000000000000000000 : ℝ)+(0 : ℝ)=(101703809041230176813/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1703809041230176813/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2380378403981/250000000000000 : ℝ)*(2/5 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(2380378403981/250000000000000 : ℝ)*(2/5 : ℝ)=(314880378403981/312500000000000 : ℝ) by norm_num, show 1+2*(1703809041230176813/100000000000000000000 : ℝ)=(51703809041230176813/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2380378403981/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2380378403981/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2380378403981/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2380378403981/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2380378403981/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2380378403981/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1668995459/10000000000 : ℝ)*X 0 0+(737576899/1250000000 : ℝ)*X 0 1+(243105083/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1094901379/2000000000 : ℝ)*X 1 0+(-140619629/625000000 : ℝ)*X 1 1+(4862101551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1368626767/2500000000 : ℝ)*X 2 0+(303881353/625000000 : ℝ)*X 2 1+(-1124956859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1035214237/2500000000 : ℝ)*X 0 0+(3091511917/10000000000 : ℝ)*X 0 1+(136825121/250000000 : ℝ)*X 0 2+(1035214237/2500000000 : ℝ)*X 1 0+(3091511917/10000000000 : ℝ)*X 1 1+(136825121/250000000 : ℝ)*X 1 2+(1035214237/2500000000 : ℝ)*X 2 0+(3091511917/10000000000 : ℝ)*X 2 1+(136825121/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1672381269/10000000000 : ℝ)*X 0 0+(1222127201/2500000000 : ℝ)*X 0 1+(5873264703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324419289/625000000 : ℝ)*X 1 0+(-123875109/1000000000 : ℝ)*X 1 1+(146831619/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259535429/500000000 : ℝ)*X 2 0+(2936632497/5000000000 : ℝ)*X 2 1+(-1238750789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037155261/2500000000 : ℝ)*X 0 0+(5412448699/10000000000 : ℝ)*X 0 1+(315423159/1000000000 : ℝ)*X 0 2+(1037155261/2500000000 : ℝ)*X 1 0+(5412448699/10000000000 : ℝ)*X 1 1+(315423159/1000000000 : ℝ)*X 1 2+(1037155261/2500000000 : ℝ)*X 2 0+(5412448699/10000000000 : ℝ)*X 2 1+(315423159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37070984022900150160161/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2327143/20000000000000 : ℝ)*(base1) + (731591541/50000000000000 : ℝ)*(base19) + (1493612459/100000000000000 : ℝ)*(base23) + (17682467/12500000000000 : ℝ)*(upper3) + (62505843/25000000000000 : ℝ)*(upper5) + (691417518333691/100000000000000 : ℝ)*(major0) + (691417518333691/100000000000000 : ℝ)*(major1) + (691417518333691/100000000000000 : ℝ)*(major2) + (481459759399051/50000000000000 : ℝ)*(sp0) + (481461959970757/50000000000000 : ℝ)*(sp1) + (481461944756069/50000000000000 : ℝ)*(sp2) + (209953570554663/50000000000000 : ℝ)*(sp3) + (587596221/10000000000000 : ℝ)*(sp4) + (8996429/390625000000 : ℝ)*(sp7) + (209954727915433/50000000000000 : ℝ)*(f.failure) + (240731345781149/25000000000000 : ℝ)*(f.sum) + (32095235873871/12500000000000000000000000000 : ℝ)*base65 + (17158077273871/25000000000000000000000000000 : ℝ)*base67 + (60113137073871/25000000000000000000000000000 : ℝ)*base69 + (130966252473871/25000000000000000000000000000 : ℝ)*base71 + (13727560548871/12500000000000000000000000000 : ℝ)*base73 + (111244005473871/25000000000000000000000000000 : ℝ)*base75 + (26889943623871/25000000000000000000000000000 : ℝ)*base77 + (9969552273871/25000000000000000000000000000 : ℝ)*base79 + (41496549373871/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1091007/1250000000000000000000 : ℝ)*base89 + (1091007/1250000000000000000000 : ℝ)*base91 + (1091007/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (874711375427423687193/97656250000000000000000000 : ℝ) := by norm_num
    linear_combination (1989037339/100000000000000 : ℝ)*(base19) + (12531777/625000000000 : ℝ)*(base23) + (37463651/100000000000000 : ℝ)*(base32) + (149105797/50000000000000 : ℝ)*(upper3) + (251118141/100000000000000 : ℝ)*(upper5) + (22786051501293/3125000000000 : ℝ)*(major0) + (22786051501293/3125000000000 : ℝ)*(major1) + (22786051501293/3125000000000 : ℝ)*(major2) + (5225661733/100000000000000 : ℝ)*(sp1) + (1419149553/25000000000000 : ℝ)*(sp2) + (63467484823439/6250000000000 : ℝ)*(sp4) + (1015472542475951/100000000000000 : ℝ)*(sp5) + (1015472075492491/100000000000000 : ℝ)*(sp6) + (442827202875923/100000000000000 : ℝ)*(sp7) + (221413620169787/50000000000000 : ℝ)*(f.failure) + (63467484823439/6250000000000 : ℝ)*(f.sum) + (495105989509/781250000000000000000000000 : ℝ)*base66 + (10363450713393/3125000000000000000000000000 : ℝ)*base68 + (6957819058259/1562500000000000000000000000 : ℝ)*base70 + (4010022417857/3125000000000000000000000000 : ℝ)*base71 + (11761444329911/3125000000000000000000000000 : ℝ)*base74 + (5696684474107/3125000000000000000000000000 : ℝ)*base75 + (115798778683/781250000000000000000000000 : ℝ)*base77 + (1945644882143/3125000000000000000000000000 : ℝ)*base80 + (10254210829911/3125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7353373/1250000000000000000000 : ℝ)*base89 + (7353373/1250000000000000000000 : ℝ)*base91 + (7353373/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1528_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3031/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25279/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1528_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1528_s1_0 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1818448999/10000000000 : ℝ)*x 0 + (1390026591/2500000000 : ℝ)*x 1 + (1021296711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1818448999/10000000000 : ℝ)^4553 ≤ (86632473433/781250000000 : ℝ)^3529 := by
    have hnat : (1818448999 : ℕ)^4553*781250000000^3529 ≤ 86632473433^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818448999 10000000000 86632473433 781250000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390026591/2500000000 : ℝ)^4553 ≤ (23446854277809/50000000000000 : ℝ)^3529 := by
    have hnat : (1390026591 : ℕ)^4553*50000000000000^3529 ≤ 23446854277809^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390026591 2500000000 23446854277809 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021296711/2000000000 : ℝ)^4553 ≤ (4201733483383/10000000000000 : ℝ)^3529 := by
    have hnat : (1021296711 : ℕ)^4553*10000000000000^3529 ≤ 4201733483383^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021296711 2000000000 4201733483383 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1818448999/10000000000 : ℝ), (1390026591/2500000000 : ℝ), (1021296711/2000000000 : ℝ)] ![(86632473433/781250000000 : ℝ), (23446854277809/50000000000000 : ℝ), (4201733483383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1818448999/10000000000 : ℝ)|^4553 ≤ (86632473433/781250000000 : ℝ)^3529
        have hw : |(-1818448999/10000000000 : ℝ)|=(1818448999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1390026591/2500000000 : ℝ)|^4553 ≤ (23446854277809/50000000000000 : ℝ)^3529
        have hw : |(1390026591/2500000000 : ℝ)|=(1390026591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021296711/2000000000 : ℝ)|^4553 ≤ (4201733483383/10000000000000 : ℝ)^3529
        have hw : |(1021296711/2000000000 : ℝ)|=(1021296711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_1 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269186957/500000000 : ℝ)*x 0 + (-1028422819/5000000000 : ℝ)*x 1 + (1021296433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269186957/500000000 : ℝ)^4553 ≤ (44983517499413/100000000000000 : ℝ)^3529 := by
    have hnat : (269186957 : ℕ)^4553*100000000000000^3529 ≤ 44983517499413^3529*500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269186957 500000000 44983517499413 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028422819/5000000000 : ℝ)^4553 ≤ (6499581205479/50000000000000 : ℝ)^3529 := by
    have hnat : (1028422819 : ℕ)^4553*50000000000000^3529 ≤ 6499581205479^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028422819 5000000000 6499581205479 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021296433/2000000000 : ℝ)^4553 ≤ (21008660038937/50000000000000 : ℝ)^3529 := by
    have hnat : (1021296433 : ℕ)^4553*50000000000000^3529 ≤ 21008660038937^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021296433 2000000000 21008660038937 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269186957/500000000 : ℝ), (-1028422819/5000000000 : ℝ), (1021296433/2000000000 : ℝ)] ![(44983517499413/100000000000000 : ℝ), (6499581205479/50000000000000 : ℝ), (21008660038937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269186957/500000000 : ℝ)|^4553 ≤ (44983517499413/100000000000000 : ℝ)^3529
        have hw : |(269186957/500000000 : ℝ)|=(269186957/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028422819/5000000000 : ℝ)|^4553 ≤ (6499581205479/50000000000000 : ℝ)^3529
        have hw : |(-1028422819/5000000000 : ℝ)|=(1028422819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021296433/2000000000 : ℝ)|^4553 ≤ (21008660038937/50000000000000 : ℝ)^3529
        have hw : |(1021296433/2000000000 : ℝ)|=(1021296433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_2 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076747633/2000000000 : ℝ)*x 0 + (5106483501/10000000000 : ℝ)*x 1 + (-2056845187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076747633/2000000000 : ℝ)^4553 ≤ (8996701397799/20000000000000 : ℝ)^3529 := by
    have hnat : (1076747633 : ℕ)^4553*20000000000000^3529 ≤ 8996701397799^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076747633 2000000000 8996701397799 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5106483501/10000000000 : ℝ)^4553 ≤ (42017334260577/100000000000000 : ℝ)^3529 := by
    have hnat : (5106483501 : ℕ)^4553*100000000000000^3529 ≤ 42017334260577^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5106483501 10000000000 42017334260577 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2056845187/10000000000 : ℝ)^4553 ≤ (6499579366799/50000000000000 : ℝ)^3529 := by
    have hnat : (2056845187 : ℕ)^4553*50000000000000^3529 ≤ 6499579366799^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056845187 10000000000 6499579366799 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076747633/2000000000 : ℝ), (5106483501/10000000000 : ℝ), (-2056845187/10000000000 : ℝ)] ![(8996701397799/20000000000000 : ℝ), (42017334260577/100000000000000 : ℝ), (6499579366799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076747633/2000000000 : ℝ)|^4553 ≤ (8996701397799/20000000000000 : ℝ)^3529
        have hw : |(1076747633/2000000000 : ℝ)|=(1076747633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5106483501/10000000000 : ℝ)|^4553 ≤ (42017334260577/100000000000000 : ℝ)^3529
        have hw : |(5106483501/10000000000 : ℝ)|=(5106483501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2056845187/10000000000 : ℝ)|^4553 ≤ (6499579366799/50000000000000 : ℝ)^3529
        have hw : |(-2056845187/10000000000 : ℝ)|=(2056845187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_3 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243773137/10000000000 : ℝ)*x 0 + (750043733/2000000000 : ℝ)*x 1 + (1197614331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243773137/10000000000 : ℝ)^4553 ≤ (8273286416283/25000000000000 : ℝ)^3529 := by
    have hnat : (4243773137 : ℕ)^4553*25000000000000^3529 ≤ 8273286416283^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243773137 10000000000 8273286416283 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750043733/2000000000 : ℝ)^4553 ≤ (7053453363669/25000000000000 : ℝ)^3529 := by
    have hnat : (750043733 : ℕ)^4553*25000000000000^3529 ≤ 7053453363669^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750043733 2000000000 7053453363669 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197614331/2500000000 : ℝ)^4553 ≤ (1547721634347/4000000000000 : ℝ)^3529 := by
    have hnat : (1197614331 : ℕ)^4553*4000000000000^3529 ≤ 1547721634347^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197614331 2500000000 1547721634347 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243773137/10000000000 : ℝ), (750043733/2000000000 : ℝ), (1197614331/2500000000 : ℝ)] ![(8273286416283/25000000000000 : ℝ), (7053453363669/25000000000000 : ℝ), (1547721634347/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243773137/10000000000 : ℝ)|^4553 ≤ (8273286416283/25000000000000 : ℝ)^3529
        have hw : |(4243773137/10000000000 : ℝ)|=(4243773137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(750043733/2000000000 : ℝ)|^4553 ≤ (7053453363669/25000000000000 : ℝ)^3529
        have hw : |(750043733/2000000000 : ℝ)|=(750043733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1197614331/2500000000 : ℝ)|^4553 ≤ (1547721634347/4000000000000 : ℝ)^3529
        have hw : |(1197614331/2500000000 : ℝ)|=(1197614331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_4 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-363744407/2000000000 : ℝ)*x 0 + (2555721841/5000000000 : ℝ)*x 1 + (347191779/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363744407/2000000000 : ℝ)^4553 ≤ (5545552375503/50000000000000 : ℝ)^3529 := by
    have hnat : (363744407 : ℕ)^4553*50000000000000^3529 ≤ 5545552375503^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363744407 2000000000 5545552375503 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2555721841/5000000000 : ℝ)^4553 ≤ (10517499487/25000000000 : ℝ)^3529 := by
    have hnat : (2555721841 : ℕ)^4553*25000000000^3529 ≤ 10517499487^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555721841 5000000000 10517499487 25000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347191779/625000000 : ℝ)^4553 ≤ (9367779456043/20000000000000 : ℝ)^3529 := by
    have hnat : (347191779 : ℕ)^4553*20000000000000^3529 ≤ 9367779456043^3529*625000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347191779 625000000 9367779456043 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-363744407/2000000000 : ℝ), (2555721841/5000000000 : ℝ), (347191779/625000000 : ℝ)] ![(5545552375503/50000000000000 : ℝ), (10517499487/25000000000 : ℝ), (9367779456043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-363744407/2000000000 : ℝ)|^4553 ≤ (5545552375503/50000000000000 : ℝ)^3529
        have hw : |(-363744407/2000000000 : ℝ)|=(363744407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2555721841/5000000000 : ℝ)|^4553 ≤ (10517499487/25000000000 : ℝ)^3529
        have hw : |(2555721841/5000000000 : ℝ)|=(2555721841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(347191779/625000000 : ℝ)|^4553 ≤ (9367779456043/20000000000000 : ℝ)^3529
        have hw : |(347191779/625000000 : ℝ)|=(347191779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_5 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632016149/5000000000 : ℝ)*x 0 + (-804129961/5000000000 : ℝ)*x 1 + (2777534301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632016149/5000000000 : ℝ)^4553 ≤ (1747890906953/4000000000000 : ℝ)^3529 := by
    have hnat : (2632016149 : ℕ)^4553*4000000000000^3529 ≤ 1747890906953^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632016149 5000000000 1747890906953 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804129961/5000000000 : ℝ)^4553 ≤ (946382852221/10000000000000 : ℝ)^3529 := by
    have hnat : (804129961 : ℕ)^4553*10000000000000^3529 ≤ 946382852221^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804129961 5000000000 946382852221 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2777534301/5000000000 : ℝ)^4553 ≤ (11709724695357/25000000000000 : ℝ)^3529 := by
    have hnat : (2777534301 : ℕ)^4553*25000000000000^3529 ≤ 11709724695357^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777534301 5000000000 11709724695357 25000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632016149/5000000000 : ℝ), (-804129961/5000000000 : ℝ), (2777534301/5000000000 : ℝ)] ![(1747890906953/4000000000000 : ℝ), (946382852221/10000000000000 : ℝ), (11709724695357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632016149/5000000000 : ℝ)|^4553 ≤ (1747890906953/4000000000000 : ℝ)^3529
        have hw : |(2632016149/5000000000 : ℝ)|=(2632016149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-804129961/5000000000 : ℝ)|^4553 ≤ (946382852221/10000000000000 : ℝ)^3529
        have hw : |(-804129961/5000000000 : ℝ)|=(804129961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2777534301/5000000000 : ℝ)|^4553 ≤ (11709724695357/25000000000000 : ℝ)^3529
        have hw : |(2777534301/5000000000 : ℝ)|=(2777534301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_6 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65800401/125000000 : ℝ)*x 0 + (5555068739/10000000000 : ℝ)*x 1 + (-804130017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65800401/125000000 : ℝ)^4553 ≤ (43697270339087/100000000000000 : ℝ)^3529 := by
    have hnat : (65800401 : ℕ)^4553*100000000000000^3529 ≤ 43697270339087^3529*125000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65800401 125000000 43697270339087 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5555068739/10000000000 : ℝ)^4553 ≤ (46838900271763/100000000000000 : ℝ)^3529 := by
    have hnat : (5555068739 : ℕ)^4553*100000000000000^3529 ≤ 46838900271763^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5555068739 10000000000 46838900271763 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804130017/5000000000 : ℝ)^4553 ≤ (1892765874503/20000000000000 : ℝ)^3529 := by
    have hnat : (804130017 : ℕ)^4553*20000000000000^3529 ≤ 1892765874503^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804130017 5000000000 1892765874503 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65800401/125000000 : ℝ), (5555068739/10000000000 : ℝ), (-804130017/5000000000 : ℝ)] ![(43697270339087/100000000000000 : ℝ), (46838900271763/100000000000000 : ℝ), (1892765874503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65800401/125000000 : ℝ)|^4553 ≤ (43697270339087/100000000000000 : ℝ)^3529
        have hw : |(65800401/125000000 : ℝ)|=(65800401/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5555068739/10000000000 : ℝ)|^4553 ≤ (46838900271763/100000000000000 : ℝ)^3529
        have hw : |(5555068739/10000000000 : ℝ)|=(5555068739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-804130017/5000000000 : ℝ)|^4553 ≤ (1892765874503/20000000000000 : ℝ)^3529
        have hw : |(-804130017/5000000000 : ℝ)|=(804130017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s1_7 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2122199407/5000000000 : ℝ)*x 0 + (955816533/2000000000 : ℝ)*x 1 + (1880886407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122199407/5000000000 : ℝ)^4553 ≤ (33099440601773/100000000000000 : ℝ)^3529 := by
    have hnat : (2122199407 : ℕ)^4553*100000000000000^3529 ≤ 33099440601773^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122199407 5000000000 33099440601773 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955816533/2000000000 : ℝ)^4553 ≤ (3857454844583/10000000000000 : ℝ)^3529 := by
    have hnat : (955816533 : ℕ)^4553*10000000000000^3529 ≤ 3857454844583^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955816533 2000000000 3857454844583 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1880886407/5000000000 : ℝ)^4553 ≤ (1133040437327/4000000000000 : ℝ)^3529 := by
    have hnat : (1880886407 : ℕ)^4553*4000000000000^3529 ≤ 1133040437327^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880886407 5000000000 1133040437327 4000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122199407/5000000000 : ℝ), (955816533/2000000000 : ℝ), (1880886407/5000000000 : ℝ)] ![(33099440601773/100000000000000 : ℝ), (3857454844583/10000000000000 : ℝ), (1133040437327/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122199407/5000000000 : ℝ)|^4553 ≤ (33099440601773/100000000000000 : ℝ)^3529
        have hw : |(2122199407/5000000000 : ℝ)|=(2122199407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(955816533/2000000000 : ℝ)|^4553 ≤ (3857454844583/10000000000000 : ℝ)^3529
        have hw : |(955816533/2000000000 : ℝ)|=(955816533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1880886407/5000000000 : ℝ)|^4553 ≤ (1133040437327/4000000000000 : ℝ)^3529
        have hw : |(1880886407/5000000000 : ℝ)|=(1880886407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1528_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4283/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18163/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25279/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3031/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25279/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3031/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25279/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3031/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3031/100000 : ℝ) ^ (4551/1024 : ℝ) ≤ (3570161025953/20000000000000000000 : ℝ) := by
    have hpowers : (3031/100000 : ℝ)^4551 ≤ (3570161025953/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3031 : ℕ)^4551*20000000000000000000^1024 ≤ 3570161025953^1024*100000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3031 100000 3570161025953 20000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3031/100000 : ℝ)) (X := (3570161025953/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25279/100000 : ℝ) ^ (4551/1024 : ℝ) ≤ (44329650882293603/20000000000000000000 : ℝ) := by
    have hpowers : (25279/100000 : ℝ)^4551 ≤ (44329650882293603/20000000000000000000 : ℝ)^1024 := by
      have hnat : (25279 : ℕ)^4551*20000000000000000000^1024 ≤ 44329650882293603^1024*100000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25279 100000 44329650882293603 20000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25279/100000 : ℝ)) (X := (44329650882293603/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000003570161025953/10000000000000000000 : ℝ) ≤ (2500000200826433/2500000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (10000003570161025953/10000000000000000000 : ℝ)^1024 ≤ (2500000200826433/2500000000000000 : ℝ)^4551 := by
      have hnat : (10000003570161025953 : ℕ)^1024*2500000000000000^4551 ≤ 2500000200826433^4551*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000003570161025953 10000000000000000000 2500000200826433 2500000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000200826433/2500000000000000 : ℝ)) (X := (10000003570161025953/10000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5011083305260829889/5000000000000000000 : ℝ) ≤ (10004983330638031/10000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (5011083305260829889/5000000000000000000 : ℝ)^1024 ≤ (10004983330638031/10000000000000000 : ℝ)^4551 := by
      have hnat : (5011083305260829889 : ℕ)^1024*10000000000000000^4551 ≤ 10004983330638031^4551*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5011083305260829889 5000000000000000000 10004983330638031 10000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004983330638031/10000000000000000 : ℝ)) (X := (5011083305260829889/5000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10044329650882293603/10000000000000000000 : ℝ) ≤ (1000996585797033/1000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (10044329650882293603/10000000000000000000 : ℝ)^1024 ≤ (1000996585797033/1000000000000000 : ℝ)^4551 := by
      have hnat : (10044329650882293603 : ℕ)^1024*1000000000000000^4551 ≤ 1000996585797033^4551*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10044329650882293603 10000000000000000000 1000996585797033 1000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000996585797033/1000000000000000 : ℝ)) (X := (10044329650882293603/10000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3570161025953/20000000000000000000 : ℝ) ≤ ((111224906895628764499/111240000000000000000 : ℝ)+2*(4982527332299/2224800000000000 : ℝ)*(3031/100000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (111224906895628764499/111240000000000000000 : ℝ)+2*(4982527332299/2224800000000000 : ℝ)*(3031/100000 : ℝ)=(2500000200826433/2500000000000000 : ℝ) by norm_num, show 1+2*(3570161025953/20000000000000000000 : ℝ)=(10000003570161025953/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44329650882293603/20000000000000000000 : ℝ)+(3570161025953/20000000000000000000 : ℝ) ≤ ((111224906895628764499/111240000000000000000 : ℝ)+(4982527332299/2224800000000000 : ℝ)*((25279/100000 : ℝ)+(3031/100000 : ℝ)))^(4551/1024 : ℝ) := by
    rw [show (111224906895628764499/111240000000000000000 : ℝ)+(4982527332299/2224800000000000 : ℝ)*((25279/100000 : ℝ)+(3031/100000 : ℝ))=(10004983330638031/10000000000000000 : ℝ) by norm_num, show 1+(44329650882293603/20000000000000000000 : ℝ)+(3570161025953/20000000000000000000 : ℝ)=(5011083305260829889/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44329650882293603/20000000000000000000 : ℝ) ≤ ((111224906895628764499/111240000000000000000 : ℝ)+2*(4982527332299/2224800000000000 : ℝ)*(25279/100000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (111224906895628764499/111240000000000000000 : ℝ)+2*(4982527332299/2224800000000000 : ℝ)*(25279/100000 : ℝ)=(1000996585797033/1000000000000000 : ℝ) by norm_num, show 1+2*(44329650882293603/20000000000000000000 : ℝ)=(10044329650882293603/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (111224906895628764499/111240000000000000000 : ℝ)*(X 1 0+X 2 0)+(4982527332299/2224800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (3031/100000 : ℝ)) (hi := (25279/100000 : ℝ)) (c := (111224906895628764499/111240000000000000000 : ℝ)) (alpha := (4982527332299/2224800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (111224906895628764499/111240000000000000000 : ℝ)*(X 0 1+X 2 1)+(4982527332299/2224800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (3031/100000 : ℝ)) (hi := (25279/100000 : ℝ)) (c := (111224906895628764499/111240000000000000000 : ℝ)) (alpha := (4982527332299/2224800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (111224906895628764499/111240000000000000000 : ℝ)*(X 0 2+X 1 2)+(4982527332299/2224800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (3031/100000 : ℝ)) (hi := (25279/100000 : ℝ)) (c := (111224906895628764499/111240000000000000000 : ℝ)) (alpha := (4982527332299/2224800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1818448999/10000000000 : ℝ)*X 0 0+(1390026591/2500000000 : ℝ)*X 0 1+(1021296711/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((269186957/500000000 : ℝ)*X 1 0+(-1028422819/5000000000 : ℝ)*X 1 1+(1021296433/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1076747633/2000000000 : ℝ)*X 2 0+(5106483501/10000000000 : ℝ)*X 2 1+(-2056845187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4243773137/10000000000 : ℝ)*X 0 0+(750043733/2000000000 : ℝ)*X 0 1+(1197614331/2500000000 : ℝ)*X 0 2+(4243773137/10000000000 : ℝ)*X 1 0+(750043733/2000000000 : ℝ)*X 1 1+(1197614331/2500000000 : ℝ)*X 1 2+(4243773137/10000000000 : ℝ)*X 2 0+(750043733/2000000000 : ℝ)*X 2 1+(1197614331/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-363744407/2000000000 : ℝ)*X 0 0+(2555721841/5000000000 : ℝ)*X 0 1+(347191779/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632016149/5000000000 : ℝ)*X 1 0+(-804129961/5000000000 : ℝ)*X 1 1+(2777534301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((65800401/125000000 : ℝ)*X 2 0+(5555068739/10000000000 : ℝ)*X 2 1+(-804130017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2122199407/5000000000 : ℝ)*X 0 0+(955816533/2000000000 : ℝ)*X 0 1+(1880886407/5000000000 : ℝ)*X 0 2+(2122199407/5000000000 : ℝ)*X 1 0+(955816533/2000000000 : ℝ)*X 1 1+(1880886407/5000000000 : ℝ)*X 1 2+(2122199407/5000000000 : ℝ)*X 2 0+(955816533/2000000000 : ℝ)*X 2 1+(1880886407/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (510315301434596813874931459/927000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21811699/20000000000000 : ℝ)*(base1) + (867372377/100000000000000 : ℝ)*(base19) + (95825893/20000000000000 : ℝ)*(base23) + (10673459/10000000000000 : ℝ)*(upper5) + (791449822286959/50000000000000 : ℝ)*(major0) + (791449822286959/50000000000000 : ℝ)*(major1) + (791449822286959/50000000000000 : ℝ)*(major2) + (137779749517403/6250000000000 : ℝ)*(sp0) + (551119101372959/25000000000000 : ℝ)*(sp1) + (1102238643999453/50000000000000 : ℝ)*(sp2) + (961320138263447/100000000000000 : ℝ)*(sp3) + (1883908417/100000000000000 : ℝ)*(sp4) + (247132079/50000000000000 : ℝ)*(sp5) + (314086863/25000000000000 : ℝ)*(sp7) + (192264300733879/20000000000000 : ℝ)*(f.failure) + (2204477767128371/100000000000000 : ℝ)*(f.sum) + (3352527216341/55620000000000000000000000000 : ℝ)*base65 + (22420936825084918541/5562000000000000000000000000000000 : ℝ)*base67 + (9381842428438918541/5562000000000000000000000000000000 : ℝ)*base69 + (25174633022704918541/5562000000000000000000000000000000 : ℝ)*base71 + (95155129793321/55620000000000000000000000000 : ℝ)*base73 + (22616832627097081459/5562000000000000000000000000000000 : ℝ)*base76 + (12819452194987081459/5562000000000000000000000000000000 : ℝ)*base78 + (24262317907804918541/5562000000000000000000000000000000 : ℝ)*base79 + (142767543811661/55620000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3459841/500000000000000000000 : ℝ)*base89 + (3459841/500000000000000000000 : ℝ)*base91 + (3459841/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (95539716219305946966767/37080000000000000000000000000 : ℝ) := by norm_num
    linear_combination (121938863/25000000000000 : ℝ)*(base19) + (95302169/20000000000000 : ℝ)*(base23) + (78554719/100000000000000 : ℝ)*(upper3) + (9080489/25000000000000 : ℝ)*(lower4) + (6308287/100000000000000 : ℝ)*(upper5) + (1618570268204773/100000000000000 : ℝ)*(major0) + (1618570268204773/100000000000000 : ℝ)*(major1) + (1618570268204773/100000000000000 : ℝ)*(major2) + (3775338851/100000000000000 : ℝ)*(sp1) + (4351726741/100000000000000 : ℝ)*(sp2) + (1127077789414961/50000000000000 : ℝ)*(sp4) + (2254151315735619/100000000000000 : ℝ)*(sp5) + (140884421912021/6250000000000 : ℝ)*(sp6) + (196596974338701/20000000000000 : ℝ)*(sp7) + (196596974338701/20000000000000 : ℝ)*(f.failure) + (1127077789414961/50000000000000 : ℝ)*(f.sum) + (60923533831127/111240000000000000000000000000 : ℝ)*base65 + (51680913581114896273/11124000000000000000000000000000000 : ℝ)*base68 + (8505385533009103727/11124000000000000000000000000000000 : ℝ)*base69 + (1804279100553103727/11124000000000000000000000000000000 : ℝ)*base71 + (68890806216433/111240000000000000000000000000 : ℝ)*base74 + (15388391179629103727/11124000000000000000000000000000000 : ℝ)*base75 + (19804742131778896273/11124000000000000000000000000000000 : ℝ)*base78 + (23471915067998896273/11124000000000000000000000000000000 : ℝ)*base80 + (42980886644833/111240000000000000000000000000 : ℝ)*base82 + (1058021/500000000000000000000 : ℝ)*base90 + (1058021/500000000000000000000 : ℝ)*base92 + (1058021/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1528_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25279/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3031/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4283/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18163/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1528_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1528_s2_0 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-920594751/5000000000 : ℝ)*x 0 + (170405263/312500000 : ℝ)*x 1 + (5198866633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (920594751/5000000000 : ℝ)^4553 ≤ (704261916241/6250000000000 : ℝ)^3529 := by
    have hnat : (920594751 : ℕ)^4553*6250000000000^3529 ≤ 704261916241^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920594751 5000000000 704261916241 6250000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170405263/312500000 : ℝ)^4553 ≤ (4573119138719/10000000000000 : ℝ)^3529 := by
    have hnat : (170405263 : ℕ)^4553*10000000000000^3529 ≤ 4573119138719^3529*312500000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170405263 312500000 4573119138719 10000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198866633/10000000000 : ℝ)^4553 ≤ (21500308969933/50000000000000 : ℝ)^3529 := by
    have hnat : (5198866633 : ℕ)^4553*50000000000000^3529 ≤ 21500308969933^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198866633 10000000000 21500308969933 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-920594751/5000000000 : ℝ), (170405263/312500000 : ℝ), (5198866633/10000000000 : ℝ)] ![(704261916241/6250000000000 : ℝ), (4573119138719/10000000000000 : ℝ), (21500308969933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-920594751/5000000000 : ℝ)|^4553 ≤ (704261916241/6250000000000 : ℝ)^3529
        have hw : |(-920594751/5000000000 : ℝ)|=(920594751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170405263/312500000 : ℝ)|^4553 ≤ (4573119138719/10000000000000 : ℝ)^3529
        have hw : |(170405263/312500000 : ℝ)|=(170405263/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198866633/10000000000 : ℝ)|^4553 ≤ (21500308969933/50000000000000 : ℝ)^3529
        have hw : |(5198866633/10000000000 : ℝ)|=(5198866633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_1 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071276601/2000000000 : ℝ)*x 0 + (-197187697/1000000000 : ℝ)*x 1 + (5198867059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071276601/2000000000 : ℝ)^4553 ≤ (44688838311077/100000000000000 : ℝ)^3529 := by
    have hnat : (1071276601 : ℕ)^4553*100000000000000^3529 ≤ 44688838311077^3529*2000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071276601 2000000000 44688838311077 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197187697/1000000000 : ℝ)^4553 ≤ (6155269591009/50000000000000 : ℝ)^3529 := by
    have hnat : (197187697 : ℕ)^4553*50000000000000^3529 ≤ 6155269591009^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197187697 1000000000 6155269591009 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198867059/10000000000 : ℝ)^4553 ≤ (5375077810723/12500000000000 : ℝ)^3529 := by
    have hnat : (5198867059 : ℕ)^4553*12500000000000^3529 ≤ 5375077810723^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198867059 10000000000 5375077810723 12500000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071276601/2000000000 : ℝ), (-197187697/1000000000 : ℝ), (5198867059/10000000000 : ℝ)] ![(44688838311077/100000000000000 : ℝ), (6155269591009/50000000000000 : ℝ), (5375077810723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071276601/2000000000 : ℝ)|^4553 ≤ (44688838311077/100000000000000 : ℝ)^3529
        have hw : |(1071276601/2000000000 : ℝ)|=(1071276601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197187697/1000000000 : ℝ)|^4553 ≤ (6155269591009/50000000000000 : ℝ)^3529
        have hw : |(-197187697/1000000000 : ℝ)|=(197187697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198867059/10000000000 : ℝ)|^4553 ≤ (5375077810723/12500000000000 : ℝ)^3529
        have hw : |(5198867059/10000000000 : ℝ)|=(5198867059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_2 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356383733/10000000000 : ℝ)*x 0 + (5198866627/10000000000 : ℝ)*x 1 + (-1971876571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356383733/10000000000 : ℝ)^4553 ≤ (698263221051/1562500000000 : ℝ)^3529 := by
    have hnat : (5356383733 : ℕ)^4553*1562500000000^3529 ≤ 698263221051^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356383733 10000000000 698263221051 1562500000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198866627/10000000000 : ℝ)^4553 ≤ (43000617875839/100000000000000 : ℝ)^3529 := by
    have hnat : (5198866627 : ℕ)^4553*100000000000000^3529 ≤ 43000617875839^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198866627 10000000000 43000617875839 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971876571/10000000000 : ℝ)^4553 ≤ (6155267984119/50000000000000 : ℝ)^3529 := by
    have hnat : (1971876571 : ℕ)^4553*50000000000000^3529 ≤ 6155267984119^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971876571 10000000000 6155267984119 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356383733/10000000000 : ℝ), (5198866627/10000000000 : ℝ), (-1971876571/10000000000 : ℝ)] ![(698263221051/1562500000000 : ℝ), (43000617875839/100000000000000 : ℝ), (6155267984119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356383733/10000000000 : ℝ)|^4553 ≤ (698263221051/1562500000000 : ℝ)^3529
        have hw : |(5356383733/10000000000 : ℝ)|=(5356383733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198866627/10000000000 : ℝ)|^4553 ≤ (43000617875839/100000000000000 : ℝ)^3529
        have hw : |(5198866627/10000000000 : ℝ)|=(5198866627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971876571/10000000000 : ℝ)|^4553 ≤ (6155267984119/50000000000000 : ℝ)^3529
        have hw : |(-1971876571/10000000000 : ℝ)|=(1971876571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_3 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260141903/10000000000 : ℝ)*x 0 + (1988565939/5000000000 : ℝ)*x 1 + (1139958219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260141903/10000000000 : ℝ)^4553 ≤ (16628960189871/50000000000000 : ℝ)^3529 := by
    have hnat : (4260141903 : ℕ)^4553*50000000000000^3529 ≤ 16628960189871^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260141903 10000000000 16628960189871 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988565939/5000000000 : ℝ)^4553 ≤ (190220956309/625000000000 : ℝ)^3529 := by
    have hnat : (1988565939 : ℕ)^4553*625000000000^3529 ≤ 190220956309^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988565939 5000000000 190220956309 625000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139958219/2500000000 : ℝ)^4553 ≤ (36306726598759/100000000000000 : ℝ)^3529 := by
    have hnat : (1139958219 : ℕ)^4553*100000000000000^3529 ≤ 36306726598759^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139958219 2500000000 36306726598759 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260141903/10000000000 : ℝ), (1988565939/5000000000 : ℝ), (1139958219/2500000000 : ℝ)] ![(16628960189871/50000000000000 : ℝ), (190220956309/625000000000 : ℝ), (36306726598759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260141903/10000000000 : ℝ)|^4553 ≤ (16628960189871/50000000000000 : ℝ)^3529
        have hw : |(4260141903/10000000000 : ℝ)|=(4260141903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1988565939/5000000000 : ℝ)|^4553 ≤ (190220956309/625000000000 : ℝ)^3529
        have hw : |(1988565939/5000000000 : ℝ)|=(1988565939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139958219/2500000000 : ℝ)|^4553 ≤ (36306726598759/100000000000000 : ℝ)^3529
        have hw : |(1139958219/2500000000 : ℝ)|=(1139958219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_4 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1841236247/10000000000 : ℝ)*x 0 + (520043267/1000000000 : ℝ)*x 1 + (1362847417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841236247/10000000000 : ℝ)^4553 ≤ (11268559755103/100000000000000 : ℝ)^3529 := by
    have hnat : (1841236247 : ℕ)^4553*100000000000000^3529 ≤ 11268559755103^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841236247 10000000000 11268559755103 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520043267/1000000000 : ℝ)^4553 ≤ (8603466023237/20000000000000 : ℝ)^3529 := by
    have hnat : (520043267 : ℕ)^4553*20000000000000^3529 ≤ 8603466023237^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520043267 1000000000 8603466023237 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362847417/2500000000 : ℝ)^4553 ≤ (22857055059829/50000000000000 : ℝ)^3529 := by
    have hnat : (1362847417 : ℕ)^4553*50000000000000^3529 ≤ 22857055059829^3529*2500000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362847417 2500000000 22857055059829 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1841236247/10000000000 : ℝ), (520043267/1000000000 : ℝ), (1362847417/2500000000 : ℝ)] ![(11268559755103/100000000000000 : ℝ), (8603466023237/20000000000000 : ℝ), (22857055059829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1841236247/10000000000 : ℝ)|^4553 ≤ (11268559755103/100000000000000 : ℝ)^3529
        have hw : |(-1841236247/10000000000 : ℝ)|=(1841236247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520043267/1000000000 : ℝ)|^4553 ≤ (8603466023237/20000000000000 : ℝ)^3529
        have hw : |(520043267/1000000000 : ℝ)|=(520043267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362847417/2500000000 : ℝ)|^4553 ≤ (22857055059829/50000000000000 : ℝ)^3529
        have hw : |(1362847417/2500000000 : ℝ)|=(1362847417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_5 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289507229/10000000000 : ℝ)*x 0 + (-1719354791/10000000000 : ℝ)*x 1 + (5451390953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289507229/10000000000 : ℝ)^4553 ≤ (21985147847287/50000000000000 : ℝ)^3529 := by
    have hnat : (5289507229 : ℕ)^4553*50000000000000^3529 ≤ 21985147847287^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289507229 10000000000 21985147847287 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1719354791/10000000000 : ℝ)^4553 ≤ (10315580267471/100000000000000 : ℝ)^3529 := by
    have hnat : (1719354791 : ℕ)^4553*100000000000000^3529 ≤ 10315580267471^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719354791 10000000000 10315580267471 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451390953/10000000000 : ℝ)^4553 ≤ (9142824804427/20000000000000 : ℝ)^3529 := by
    have hnat : (5451390953 : ℕ)^4553*20000000000000^3529 ≤ 9142824804427^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451390953 10000000000 9142824804427 20000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289507229/10000000000 : ℝ), (-1719354791/10000000000 : ℝ), (5451390953/10000000000 : ℝ)] ![(21985147847287/50000000000000 : ℝ), (10315580267471/100000000000000 : ℝ), (9142824804427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289507229/10000000000 : ℝ)|^4553 ≤ (21985147847287/50000000000000 : ℝ)^3529
        have hw : |(5289507229/10000000000 : ℝ)|=(5289507229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1719354791/10000000000 : ℝ)|^4553 ≤ (10315580267471/100000000000000 : ℝ)^3529
        have hw : |(-1719354791/10000000000 : ℝ)|=(1719354791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451390953/10000000000 : ℝ)|^4553 ≤ (9142824804427/20000000000000 : ℝ)^3529
        have hw : |(5451390953/10000000000 : ℝ)|=(5451390953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_6 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289508089/10000000000 : ℝ)*x 0 + (5451390959/10000000000 : ℝ)*x 1 + (-1719353591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289508089/10000000000 : ℝ)^4553 ≤ (21985152458961/50000000000000 : ℝ)^3529 := by
    have hnat : (5289508089 : ℕ)^4553*50000000000000^3529 ≤ 21985152458961^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289508089 10000000000 21985152458961 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451390959/10000000000 : ℝ)^4553 ≤ (45714124087049/100000000000000 : ℝ)^3529 := by
    have hnat : (5451390959 : ℕ)^4553*100000000000000^3529 ≤ 45714124087049^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451390959 10000000000 45714124087049 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1719353591/10000000000 : ℝ)^4553 ≤ (5157785489381/50000000000000 : ℝ)^3529 := by
    have hnat : (1719353591 : ℕ)^4553*50000000000000^3529 ≤ 5157785489381^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719353591 10000000000 5157785489381 50000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289508089/10000000000 : ℝ), (5451390959/10000000000 : ℝ), (-1719353591/10000000000 : ℝ)] ![(21985152458961/50000000000000 : ℝ), (45714124087049/100000000000000 : ℝ), (5157785489381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289508089/10000000000 : ℝ)|^4553 ≤ (21985152458961/50000000000000 : ℝ)^3529
        have hw : |(5289508089/10000000000 : ℝ)|=(5289508089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451390959/10000000000 : ℝ)|^4553 ≤ (45714124087049/100000000000000 : ℝ)^3529
        have hw : |(5451390959/10000000000 : ℝ)|=(5451390959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1719353591/10000000000 : ℝ)|^4553 ≤ (5157785489381/50000000000000 : ℝ)^3529
        have hw : |(-1719353591/10000000000 : ℝ)|=(1719353591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1528_s2_7 (p : ℝ) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4260253107/10000000000 : ℝ)*x 0 + (2278121961/5000000000 : ℝ)*x 1 + (398075173/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260253107/10000000000 : ℝ)^4553 ≤ (33259040434021/100000000000000 : ℝ)^3529 := by
    have hnat : (4260253107 : ℕ)^4553*100000000000000^3529 ≤ 33259040434021^3529*10000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260253107 10000000000 33259040434021 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278121961/5000000000 : ℝ)^4553 ≤ (36269862599551/100000000000000 : ℝ)^3529 := by
    have hnat : (2278121961 : ℕ)^4553*100000000000000^3529 ≤ 36269862599551^3529*5000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278121961 5000000000 36269862599551 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398075173/1000000000 : ℝ)^4553 ≤ (30471096955027/100000000000000 : ℝ)^3529 := by
    have hnat : (398075173 : ℕ)^4553*100000000000000^3529 ≤ 30471096955027^3529*1000000000^4553 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398075173 1000000000 30471096955027 100000000000000 4553 3529 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4553/1024 : ℝ)) 4553 3529 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260253107/10000000000 : ℝ), (2278121961/5000000000 : ℝ), (398075173/1000000000 : ℝ)] ![(33259040434021/100000000000000 : ℝ), (36269862599551/100000000000000 : ℝ), (30471096955027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260253107/10000000000 : ℝ)|^4553 ≤ (33259040434021/100000000000000 : ℝ)^3529
        have hw : |(4260253107/10000000000 : ℝ)|=(4260253107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2278121961/5000000000 : ℝ)|^4553 ≤ (36269862599551/100000000000000 : ℝ)^3529
        have hw : |(2278121961/5000000000 : ℝ)|=(2278121961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398075173/1000000000 : ℝ)|^4553 ≤ (30471096955027/100000000000000 : ℝ)^3529
        have hw : |(398075173/1000000000 : ℝ)|=(398075173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1528_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18163/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4283/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5279/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15939/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18163/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4283/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18163/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4283/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18163/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4283/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18163/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4283/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18163/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4283/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18163/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4283/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4283/50000 : ℝ) ^ (4551/1024 : ℝ) ≤ (1806788108176283/100000000000000000000 : ℝ) := by
    have hpowers : (4283/50000 : ℝ)^4551 ≤ (1806788108176283/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4283 : ℕ)^4551*100000000000000000000^1024 ≤ 1806788108176283^1024*50000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4283 50000 1806788108176283 100000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4283/50000 : ℝ)) (X := (1806788108176283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18163/100000 : ℝ) ^ (4551/1024 : ℝ) ≤ (25500620977061691/50000000000000000000 : ℝ) := by
    have hpowers : (18163/100000 : ℝ)^4551 ≤ (25500620977061691/50000000000000000000 : ℝ)^1024 := by
      have hnat : (18163 : ℕ)^4551*50000000000000000000^1024 ≤ 25500620977061691^1024*100000^4551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18163 100000 25500620977061691 50000000000000000000 4551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18163/100000 : ℝ)) (X := (25500620977061691/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001806788108176283/50000000000000000000 : ℝ) ≤ (1000008130631143/1000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (50001806788108176283/50000000000000000000 : ℝ)^1024 ≤ (1000008130631143/1000000000000000 : ℝ)^4551 := by
      have hnat : (50001806788108176283 : ℕ)^1024*1000000000000000^4551 ≤ 1000008130631143^4551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001806788108176283 50000000000000000000 1000008130631143 1000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000008130631143/1000000000000000 : ℝ)) (X := (50001806788108176283/50000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010561606012459933/20000000000000000000 : ℝ) ≤ (5000593983309209/5000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (20010561606012459933/20000000000000000000 : ℝ)^1024 ≤ (5000593983309209/5000000000000000 : ℝ)^4551 := by
      have hnat : (20010561606012459933 : ℕ)^1024*5000000000000000^4551 ≤ 5000593983309209^4551*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010561606012459933 20000000000000000000 5000593983309209 5000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000593983309209/5000000000000000 : ℝ)) (X := (20010561606012459933/20000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25025500620977061691/25000000000000000000 : ℝ) ≤ (5001147313462703/5000000000000000 : ℝ) ^ (4551/1024 : ℝ) := by
    have hpowers : (25025500620977061691/25000000000000000000 : ℝ)^1024 ≤ (5001147313462703/5000000000000000 : ℝ)^4551 := by
      have hnat : (25025500620977061691 : ℕ)^1024*5000000000000000^4551 ≤ 5001147313462703^4551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025500620977061691 25000000000000000000 5001147313462703 5000000000000000 1024 4551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001147313462703/5000000000000000 : ℝ)) (X := (25025500620977061691/25000000000000000000 : ℝ)) (by norm_num) 4551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1806788108176283/100000000000000000000 : ℝ) ≤ ((15991970165381912549/15995000000000000000 : ℝ)+2*(92221692249/79975000000000 : ℝ)*(4283/50000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (15991970165381912549/15995000000000000000 : ℝ)+2*(92221692249/79975000000000 : ℝ)*(4283/50000 : ℝ)=(1000008130631143/1000000000000000 : ℝ) by norm_num, show 1+2*(1806788108176283/100000000000000000000 : ℝ)=(50001806788108176283/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25500620977061691/50000000000000000000 : ℝ)+(1806788108176283/100000000000000000000 : ℝ) ≤ ((15991970165381912549/15995000000000000000 : ℝ)+(92221692249/79975000000000 : ℝ)*((18163/100000 : ℝ)+(4283/50000 : ℝ)))^(4551/1024 : ℝ) := by
    rw [show (15991970165381912549/15995000000000000000 : ℝ)+(92221692249/79975000000000 : ℝ)*((18163/100000 : ℝ)+(4283/50000 : ℝ))=(5000593983309209/5000000000000000 : ℝ) by norm_num, show 1+(25500620977061691/50000000000000000000 : ℝ)+(1806788108176283/100000000000000000000 : ℝ)=(20010561606012459933/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25500620977061691/50000000000000000000 : ℝ) ≤ ((15991970165381912549/15995000000000000000 : ℝ)+2*(92221692249/79975000000000 : ℝ)*(18163/100000 : ℝ))^(4551/1024 : ℝ) := by
    rw [show (15991970165381912549/15995000000000000000 : ℝ)+2*(92221692249/79975000000000 : ℝ)*(18163/100000 : ℝ)=(5001147313462703/5000000000000000 : ℝ) by norm_num, show 1+2*(25500620977061691/50000000000000000000 : ℝ)=(25025500620977061691/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15991970165381912549/15995000000000000000 : ℝ)*(X 1 0+X 2 0)+(92221692249/79975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (4283/50000 : ℝ)) (hi := (18163/100000 : ℝ)) (c := (15991970165381912549/15995000000000000000 : ℝ)) (alpha := (92221692249/79975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15991970165381912549/15995000000000000000 : ℝ)*(X 0 1+X 2 1)+(92221692249/79975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (4283/50000 : ℝ)) (hi := (18163/100000 : ℝ)) (c := (15991970165381912549/15995000000000000000 : ℝ)) (alpha := (92221692249/79975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15991970165381912549/15995000000000000000 : ℝ)*(X 0 2+X 1 2)+(92221692249/79975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4551/1024 : ℝ)) (lo := (4283/50000 : ℝ)) (hi := (18163/100000 : ℝ)) (c := (15991970165381912549/15995000000000000000 : ℝ)) (alpha := (92221692249/79975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-920594751/5000000000 : ℝ)*X 0 0+(170405263/312500000 : ℝ)*X 0 1+(5198866633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1071276601/2000000000 : ℝ)*X 1 0+(-197187697/1000000000 : ℝ)*X 1 1+(5198867059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356383733/10000000000 : ℝ)*X 2 0+(5198866627/10000000000 : ℝ)*X 2 1+(-1971876571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4260141903/10000000000 : ℝ)*X 0 0+(1988565939/5000000000 : ℝ)*X 0 1+(1139958219/2500000000 : ℝ)*X 0 2+(4260141903/10000000000 : ℝ)*X 1 0+(1988565939/5000000000 : ℝ)*X 1 1+(1139958219/2500000000 : ℝ)*X 1 2+(4260141903/10000000000 : ℝ)*X 2 0+(1988565939/5000000000 : ℝ)*X 2 1+(1139958219/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1841236247/10000000000 : ℝ)*X 0 0+(520043267/1000000000 : ℝ)*X 0 1+(1362847417/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289507229/10000000000 : ℝ)*X 1 0+(-1719354791/10000000000 : ℝ)*X 1 1+(5451390953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289508089/10000000000 : ℝ)*X 2 0+(5451390959/10000000000 : ℝ)*X 2 1+(-1719353591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260253107/10000000000 : ℝ)*X 0 0+(2278121961/5000000000 : ℝ)*X 0 1+(398075173/1000000000 : ℝ)*X 0 2+(4260253107/10000000000 : ℝ)*X 1 0+(2278121961/5000000000 : ℝ)*X 1 1+(398075173/1000000000 : ℝ)*X 1 2+(4260253107/10000000000 : ℝ)*X 2 0+(2278121961/5000000000 : ℝ)*X 2 1+(398075173/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1528_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44111642683625185478471313/28562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154492849/25000000000000 : ℝ)*(base19) + (782264507/100000000000000 : ℝ)*(base23) + (8930039/50000000000000 : ℝ)*(upper3) + (39699891/20000000000000 : ℝ)*(upper4) + (182018517/100000000000000 : ℝ)*(upper5) + (1412904218671253/50000000000000 : ℝ)*(major0) + (1412904218671253/50000000000000 : ℝ)*(major1) + (1412904218671253/50000000000000 : ℝ)*(major2) + (3935438281710829/100000000000000 : ℝ)*(sp0) + (3935455344765119/100000000000000 : ℝ)*(sp1) + (3935455180472009/100000000000000 : ℝ)*(sp2) + (1716153177163623/100000000000000 : ℝ)*(sp3) + (17681025687/100000000000000 : ℝ)*(sp4) + (1536661039/20000000000000 : ℝ)*(sp7) + (1716160860468817/100000000000000 : ℝ)*(f.failure) + (983863990684129/25000000000000 : ℝ)*(f.sum) + (5423113044273/2285000000000000000000000000 : ℝ)*base65 + (775490687884263729/114250000000000000000000000000000 : ℝ)*base68 + (68273229695486271/114250000000000000000000000000000 : ℝ)*base69 + (300915392281013729/114250000000000000000000000000000 : ℝ)*base72 + (6393080551661/1142500000000000000000000000 : ℝ)*base74 + (1355743837063513729/114250000000000000000000000000000 : ℝ)*base76 + (202777727259513729/114250000000000000000000000000000 : ℝ)*base78 + (1567422844752513729/114250000000000000000000000000000 : ℝ)*base80 + (4573288704253/2285000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8685257/2500000000000000000000 : ℝ)*base90 + (8685257/2500000000000000000000 : ℝ)*base92 + (8685257/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278231162439617958791973/15995000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84097383/25000000000000 : ℝ)*(base23) + (448591671/100000000000000 : ℝ)*(lower2) + (411118311/100000000000000 : ℝ)*(upper3) + (144282597/100000000000000 : ℝ)*(lower4) + (1430600063268899/50000000000000 : ℝ)*(major0) + (1430600063268899/50000000000000 : ℝ)*(major1) + (1430600063268899/50000000000000 : ℝ)*(major2) + (799301827/20000000000000 : ℝ)*(sp1) + (24864285739/100000000000000 : ℝ)*(sp2) + (2230748031/100000000000000 : ℝ)*(sp3) + (498093105789299/12500000000000 : ℝ)*(sp4) + (498092606225657/12500000000000 : ℝ)*(sp5) + (3984719645639121/100000000000000 : ℝ)*(sp6) + (434413149045923/25000000000000 : ℝ)*(sp7) + (434413706732931/25000000000000 : ℝ)*(f.failure) + (498093105789299/12500000000000 : ℝ)*(f.sum) + (58699450138873/15995000000000000000000000000 : ℝ)*base65 + (103422061619786449/799750000000000000000000000000000 : ℝ)*base68 + (29588538914297286449/799750000000000000000000000000000 : ℝ)*base70 + (4954691620543713551/799750000000000000000000000000000 : ℝ)*base71 + (7680078755947/3998750000000000000000000000 : ℝ)*base73 + (93517681871963551/799750000000000000000000000000000 : ℝ)*base75 + (118408655008267036449/799750000000000000000000000000000 : ℝ)*base78 + (41941632549968213551/799750000000000000000000000000000 : ℝ)*base79 + (13025407658497/3998750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5844149/625000000000000000000 : ℝ)*base89 + (5844149/625000000000000000000 : ℝ)*base91 + (5844149/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1528_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18163/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4283/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1528_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1528_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1528_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1528_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1528_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4551/1024 : ℝ) ≤ p) (hpb : p ≤ (4553/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41164679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5279/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15939/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1528_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1771_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:06.116587+00:00
-- url     : https://prove2.me/submissions/c44103ac-1add-4a0f-be77-1d044de11368

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
theorem support_rectangle_w1771_box_0 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-759683023/10000000000 : ℝ)*x 0 + (1350904029/2500000000 : ℝ)*x 1 + (1080722757/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (759683023/10000000000 : ℝ)^6111 ≤ (2260875327073/50000000000000 : ℝ)^5087 := by
    have hnat : (759683023 : ℕ)^6111*50000000000000^5087 ≤ 2260875327073^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759683023 10000000000 2260875327073 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350904029/2500000000 : ℝ)^6111 ≤ (5967392129521/12500000000000 : ℝ)^5087 := by
    have hnat : (1350904029 : ℕ)^6111*12500000000000^5087 ≤ 5967392129521^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350904029 2500000000 5967392129521 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080722757/2000000000 : ℝ)^6111 ≤ (23869556148563/50000000000000 : ℝ)^5087 := by
    have hnat : (1080722757 : ℕ)^6111*50000000000000^5087 ≤ 23869556148563^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080722757 2000000000 23869556148563 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-759683023/10000000000 : ℝ), (1350904029/2500000000 : ℝ), (1080722757/2000000000 : ℝ)] ![(2260875327073/50000000000000 : ℝ), (5967392129521/12500000000000 : ℝ), (23869556148563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-759683023/10000000000 : ℝ)|^6111 ≤ (2260875327073/50000000000000 : ℝ)^5087
        have hw : |(-759683023/10000000000 : ℝ)|=(759683023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350904029/2500000000 : ℝ)|^6111 ≤ (5967392129521/12500000000000 : ℝ)^5087
        have hw : |(1350904029/2500000000 : ℝ)|=(1350904029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080722757/2000000000 : ℝ)|^6111 ≤ (23869556148563/50000000000000 : ℝ)^5087
        have hw : |(1080722757/2000000000 : ℝ)|=(1080722757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_1 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103833419/200000000 : ℝ)*x 0 + (-106199761/1000000000 : ℝ)*x 1 + (270180757/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103833419/200000000 : ℝ)^6111 ≤ (45498724628629/100000000000000 : ℝ)^5087 := by
    have hnat : (103833419 : ℕ)^6111*100000000000000^5087 ≤ 45498724628629^5087*200000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103833419 200000000 45498724628629 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106199761/1000000000 : ℝ)^6111 ≤ (6762148685669/100000000000000 : ℝ)^5087 := by
    have hnat : (106199761 : ℕ)^6111*100000000000000^5087 ≤ 6762148685669^5087*1000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106199761 1000000000 6762148685669 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270180757/500000000 : ℝ)^6111 ≤ (47739126677821/100000000000000 : ℝ)^5087 := by
    have hnat : (270180757 : ℕ)^6111*100000000000000^5087 ≤ 47739126677821^5087*500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270180757 500000000 47739126677821 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103833419/200000000 : ℝ), (-106199761/1000000000 : ℝ), (270180757/500000000 : ℝ)] ![(45498724628629/100000000000000 : ℝ), (6762148685669/100000000000000 : ℝ), (47739126677821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103833419/200000000 : ℝ)|^6111 ≤ (45498724628629/100000000000000 : ℝ)^5087
        have hw : |(103833419/200000000 : ℝ)|=(103833419/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106199761/1000000000 : ℝ)|^6111 ≤ (6762148685669/100000000000000 : ℝ)^5087
        have hw : |(-106199761/1000000000 : ℝ)|=(106199761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270180757/500000000 : ℝ)|^6111 ≤ (47739126677821/100000000000000 : ℝ)^5087
        have hw : |(270180757/500000000 : ℝ)|=(270180757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_2 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2595835667/5000000000 : ℝ)*x 0 + (5403614743/10000000000 : ℝ)*x 1 + (-1061997631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2595835667/5000000000 : ℝ)^6111 ≤ (45498728671351/100000000000000 : ℝ)^5087 := by
    have hnat : (2595835667 : ℕ)^6111*100000000000000^5087 ≤ 45498728671351^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595835667 5000000000 45498728671351 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403614743/10000000000 : ℝ)^6111 ≤ (47739122464437/100000000000000 : ℝ)^5087 := by
    have hnat : (5403614743 : ℕ)^6111*100000000000000^5087 ≤ 47739122464437^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403614743 10000000000 47739122464437 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061997631/10000000000 : ℝ)^6111 ≤ (6762148846301/100000000000000 : ℝ)^5087 := by
    have hnat : (1061997631 : ℕ)^6111*100000000000000^5087 ≤ 6762148846301^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061997631 10000000000 6762148846301 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2595835667/5000000000 : ℝ), (5403614743/10000000000 : ℝ), (-1061997631/10000000000 : ℝ)] ![(45498728671351/100000000000000 : ℝ), (47739122464437/100000000000000 : ℝ), (6762148846301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2595835667/5000000000 : ℝ)|^6111 ≤ (45498728671351/100000000000000 : ℝ)^5087
        have hw : |(2595835667/5000000000 : ℝ)|=(2595835667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403614743/10000000000 : ℝ)|^6111 ≤ (47739122464437/100000000000000 : ℝ)^5087
        have hw : |(5403614743/10000000000 : ℝ)|=(5403614743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061997631/10000000000 : ℝ)|^6111 ≤ (6762148846301/100000000000000 : ℝ)^5087
        have hw : |(-1061997631/10000000000 : ℝ)|=(1061997631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_3 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (225156633/500000000 : ℝ)*x 0 + (469304269/1250000000 : ℝ)*x 1 + (750886717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225156633/500000000 : ℝ)^6111 ≤ (38350245719411/100000000000000 : ℝ)^5087 := by
    have hnat : (225156633 : ℕ)^6111*100000000000000^5087 ≤ 38350245719411^5087*500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225156633 500000000 38350245719411 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469304269/1250000000 : ℝ)^6111 ≤ (7706219982217/25000000000000 : ℝ)^5087 := by
    have hnat : (469304269 : ℕ)^6111*25000000000000^5087 ≤ 7706219982217^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469304269 1250000000 7706219982217 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (750886717/2000000000 : ℝ)^6111 ≤ (30824874336567/100000000000000 : ℝ)^5087 := by
    have hnat : (750886717 : ℕ)^6111*100000000000000^5087 ≤ 30824874336567^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750886717 2000000000 30824874336567 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225156633/500000000 : ℝ), (469304269/1250000000 : ℝ), (750886717/2000000000 : ℝ)] ![(38350245719411/100000000000000 : ℝ), (7706219982217/25000000000000 : ℝ), (30824874336567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225156633/500000000 : ℝ)|^6111 ≤ (38350245719411/100000000000000 : ℝ)^5087
        have hw : |(225156633/500000000 : ℝ)|=(225156633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469304269/1250000000 : ℝ)|^6111 ≤ (7706219982217/25000000000000 : ℝ)^5087
        have hw : |(469304269/1250000000 : ℝ)|=(469304269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(750886717/2000000000 : ℝ)|^6111 ≤ (30824874336567/100000000000000 : ℝ)^5087
        have hw : |(750886717/2000000000 : ℝ)|=(750886717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_4 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507534313/10000000000 : ℝ)*x 0 + (1282489373/2500000000 : ℝ)*x 1 + (128248961/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507534313/10000000000 : ℝ)^6111 ≤ (160943905791/1562500000000 : ℝ)^5087 := by
    have hnat : (1507534313 : ℕ)^6111*1562500000000^5087 ≤ 160943905791^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507534313 10000000000 160943905791 1562500000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282489373/2500000000 : ℝ)^6111 ≤ (2803111876779/6250000000000 : ℝ)^5087 := by
    have hnat : (1282489373 : ℕ)^6111*6250000000000^5087 ≤ 2803111876779^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282489373 2500000000 2803111876779 6250000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128248961/250000000 : ℝ)^6111 ≤ (22424899992469/50000000000000 : ℝ)^5087 := by
    have hnat : (128248961 : ℕ)^6111*50000000000000^5087 ≤ 22424899992469^5087*250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128248961 250000000 22424899992469 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507534313/10000000000 : ℝ), (1282489373/2500000000 : ℝ), (128248961/250000000 : ℝ)] ![(160943905791/1562500000000 : ℝ), (2803111876779/6250000000000 : ℝ), (22424899992469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507534313/10000000000 : ℝ)|^6111 ≤ (160943905791/1562500000000 : ℝ)^5087
        have hw : |(-1507534313/10000000000 : ℝ)|=(1507534313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282489373/2500000000 : ℝ)|^6111 ≤ (2803111876779/6250000000000 : ℝ)^5087
        have hw : |(1282489373/2500000000 : ℝ)|=(1282489373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128248961/250000000 : ℝ)|^6111 ≤ (22424899992469/50000000000000 : ℝ)^5087
        have hw : |(128248961/250000000 : ℝ)|=(128248961/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_5 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686651367/5000000000 : ℝ)*x 0 + (-1187424051/10000000000 : ℝ)*x 1 + (5129956909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686651367/5000000000 : ℝ)^6111 ≤ (23708800606699/50000000000000 : ℝ)^5087 := by
    have hnat : (2686651367 : ℕ)^6111*50000000000000^5087 ≤ 23708800606699^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686651367 5000000000 23708800606699 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1187424051/10000000000 : ℝ)^6111 ≤ (966576858387/12500000000000 : ℝ)^5087 := by
    have hnat : (1187424051 : ℕ)^6111*12500000000000^5087 ≤ 966576858387^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187424051 10000000000 966576858387 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129956909/10000000000 : ℝ)^6111 ≤ (11212445976361/25000000000000 : ℝ)^5087 := by
    have hnat : (5129956909 : ℕ)^6111*25000000000000^5087 ≤ 11212445976361^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129956909 10000000000 11212445976361 25000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686651367/5000000000 : ℝ), (-1187424051/10000000000 : ℝ), (5129956909/10000000000 : ℝ)] ![(23708800606699/50000000000000 : ℝ), (966576858387/12500000000000 : ℝ), (11212445976361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686651367/5000000000 : ℝ)|^6111 ≤ (23708800606699/50000000000000 : ℝ)^5087
        have hw : |(2686651367/5000000000 : ℝ)|=(2686651367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1187424051/10000000000 : ℝ)|^6111 ≤ (966576858387/12500000000000 : ℝ)^5087
        have hw : |(-1187424051/10000000000 : ℝ)|=(1187424051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129956909/10000000000 : ℝ)|^6111 ≤ (11212445976361/25000000000000 : ℝ)^5087
        have hw : |(5129956909/10000000000 : ℝ)|=(5129956909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_6 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537330123/1000000000 : ℝ)*x 0 + (5129958477/10000000000 : ℝ)*x 1 + (-74213999/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537330123/1000000000 : ℝ)^6111 ≤ (47417585269421/100000000000000 : ℝ)^5087 := by
    have hnat : (537330123 : ℕ)^6111*100000000000000^5087 ≤ 47417585269421^5087*1000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537330123 1000000000 47417585269421 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129958477/10000000000 : ℝ)^6111 ≤ (22424900186767/50000000000000 : ℝ)^5087 := by
    have hnat : (5129958477 : ℕ)^6111*50000000000000^5087 ≤ 22424900186767^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129958477 10000000000 22424900186767 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74213999/625000000 : ℝ)^6111 ≤ (3866307171479/50000000000000 : ℝ)^5087 := by
    have hnat : (74213999 : ℕ)^6111*50000000000000^5087 ≤ 3866307171479^5087*625000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74213999 625000000 3866307171479 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537330123/1000000000 : ℝ), (5129958477/10000000000 : ℝ), (-74213999/625000000 : ℝ)] ![(47417585269421/100000000000000 : ℝ), (22424900186767/50000000000000 : ℝ), (3866307171479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537330123/1000000000 : ℝ)|^6111 ≤ (47417585269421/100000000000000 : ℝ)^5087
        have hw : |(537330123/1000000000 : ℝ)|=(537330123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129958477/10000000000 : ℝ)|^6111 ≤ (22424900186767/50000000000000 : ℝ)^5087
        have hw : |(5129958477/10000000000 : ℝ)|=(5129958477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74213999/625000000 : ℝ)|^6111 ≤ (3866307171479/50000000000000 : ℝ)^5087
        have hw : |(-74213999/625000000 : ℝ)|=(74213999/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_7 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3416136699/10000000000 : ℝ)*x 0 + (859185931/2000000000 : ℝ)*x 1 + (6873487/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3416136699/10000000000 : ℝ)^6111 ≤ (27519281212157/100000000000000 : ℝ)^5087 := by
    have hnat : (3416136699 : ℕ)^6111*100000000000000^5087 ≤ 27519281212157^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416136699 10000000000 27519281212157 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859185931/2000000000 : ℝ)^6111 ≤ (4530045100207/12500000000000 : ℝ)^5087 := by
    have hnat : (859185931 : ℕ)^6111*12500000000000^5087 ≤ 4530045100207^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859185931 2000000000 4530045100207 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6873487/16000000 : ℝ)^6111 ≤ (4530044745513/12500000000000 : ℝ)^5087 := by
    have hnat : (6873487 : ℕ)^6111*12500000000000^5087 ≤ 4530044745513^5087*16000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6873487 16000000 4530044745513 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3416136699/10000000000 : ℝ), (859185931/2000000000 : ℝ), (6873487/16000000 : ℝ)] ![(27519281212157/100000000000000 : ℝ), (4530045100207/12500000000000 : ℝ), (4530044745513/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3416136699/10000000000 : ℝ)|^6111 ≤ (27519281212157/100000000000000 : ℝ)^5087
        have hw : |(3416136699/10000000000 : ℝ)|=(3416136699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(859185931/2000000000 : ℝ)|^6111 ≤ (4530045100207/12500000000000 : ℝ)^5087
        have hw : |(859185931/2000000000 : ℝ)|=(859185931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6873487/16000000 : ℝ)|^6111 ≤ (4530044745513/12500000000000 : ℝ)^5087
        have hw : |(6873487/16000000 : ℝ)|=(6873487/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_8 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168061021/1250000000 : ℝ)*x 0 + (4919637919/10000000000 : ℝ)*x 1 + (1365813137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168061021/1250000000 : ℝ)^6111 ≤ (897713486599/10000000000000 : ℝ)^5087 := by
    have hnat : (168061021 : ℕ)^6111*10000000000000^5087 ≤ 897713486599^5087*1250000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168061021 1250000000 897713486599 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4919637919/10000000000 : ℝ)^6111 ≤ (83300980579/195312500000 : ℝ)^5087 := by
    have hnat : (4919637919 : ℕ)^6111*195312500000^5087 ≤ 83300980579^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4919637919 10000000000 83300980579 195312500000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365813137/2500000000 : ℝ)^6111 ≤ (4837276306757/10000000000000 : ℝ)^5087 := by
    have hnat : (1365813137 : ℕ)^6111*10000000000000^5087 ≤ 4837276306757^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365813137 2500000000 4837276306757 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168061021/1250000000 : ℝ), (4919637919/10000000000 : ℝ), (1365813137/2500000000 : ℝ)] ![(897713486599/10000000000000 : ℝ), (83300980579/195312500000 : ℝ), (4837276306757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168061021/1250000000 : ℝ)|^6111 ≤ (897713486599/10000000000000 : ℝ)^5087
        have hw : |(-168061021/1250000000 : ℝ)|=(168061021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4919637919/10000000000 : ℝ)|^6111 ≤ (83300980579/195312500000 : ℝ)^5087
        have hw : |(4919637919/10000000000 : ℝ)|=(4919637919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365813137/2500000000 : ℝ)|^6111 ≤ (4837276306757/10000000000000 : ℝ)^5087
        have hw : |(1365813137/2500000000 : ℝ)|=(1365813137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_9 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (206086827/400000000 : ℝ)*x 0 + (-258351521/2500000000 : ℝ)*x 1 + (5463252877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206086827/400000000 : ℝ)^6111 ≤ (45083187959959/100000000000000 : ℝ)^5087 := by
    have hnat : (206086827 : ℕ)^6111*100000000000000^5087 ≤ 45083187959959^5087*400000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206086827 400000000 45083187959959 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258351521/2500000000 : ℝ)^6111 ≤ (6544045460023/100000000000000 : ℝ)^5087 := by
    have hnat : (258351521 : ℕ)^6111*100000000000000^5087 ≤ 6544045460023^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258351521 2500000000 6544045460023 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463252877/10000000000 : ℝ)^6111 ≤ (4837276656699/10000000000000 : ℝ)^5087 := by
    have hnat : (5463252877 : ℕ)^6111*10000000000000^5087 ≤ 4837276656699^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463252877 10000000000 4837276656699 10000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206086827/400000000 : ℝ), (-258351521/2500000000 : ℝ), (5463252877/10000000000 : ℝ)] ![(45083187959959/100000000000000 : ℝ), (6544045460023/100000000000000 : ℝ), (4837276656699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206086827/400000000 : ℝ)|^6111 ≤ (45083187959959/100000000000000 : ℝ)^5087
        have hw : |(206086827/400000000 : ℝ)|=(206086827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258351521/2500000000 : ℝ)|^6111 ≤ (6544045460023/100000000000000 : ℝ)^5087
        have hw : |(-258351521/2500000000 : ℝ)|=(258351521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463252877/10000000000 : ℝ)|^6111 ≤ (4837276656699/10000000000000 : ℝ)^5087
        have hw : |(5463252877/10000000000 : ℝ)|=(5463252877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_10 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152170679/10000000000 : ℝ)*x 0 + (341453273/625000000 : ℝ)*x 1 + (-1033406789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152170679/10000000000 : ℝ)^6111 ≤ (22541594001003/50000000000000 : ℝ)^5087 := by
    have hnat : (5152170679 : ℕ)^6111*50000000000000^5087 ≤ 22541594001003^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152170679 10000000000 22541594001003 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341453273/625000000 : ℝ)^6111 ≤ (24186380576497/50000000000000 : ℝ)^5087 := by
    have hnat : (341453273 : ℕ)^6111*50000000000000^5087 ≤ 24186380576497^5087*625000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341453273 625000000 24186380576497 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033406789/10000000000 : ℝ)^6111 ≤ (818006352889/12500000000000 : ℝ)^5087 := by
    have hnat : (1033406789 : ℕ)^6111*12500000000000^5087 ≤ 818006352889^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033406789 10000000000 818006352889 12500000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152170679/10000000000 : ℝ), (341453273/625000000 : ℝ), (-1033406789/10000000000 : ℝ)] ![(22541594001003/50000000000000 : ℝ), (24186380576497/50000000000000 : ℝ), (818006352889/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152170679/10000000000 : ℝ)|^6111 ≤ (22541594001003/50000000000000 : ℝ)^5087
        have hw : |(5152170679/10000000000 : ℝ)|=(5152170679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341453273/625000000 : ℝ)|^6111 ≤ (24186380576497/50000000000000 : ℝ)^5087
        have hw : |(341453273/625000000 : ℝ)|=(341453273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033406789/10000000000 : ℝ)|^6111 ≤ (818006352889/12500000000000 : ℝ)^5087
        have hw : |(-1033406789/10000000000 : ℝ)|=(1033406789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_11 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (945929049/2000000000 : ℝ)*x 0 + (22724931/62500000 : ℝ)*x 1 + (1817994491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (945929049/2000000000 : ℝ)^6111 ≤ (40679199195597/100000000000000 : ℝ)^5087 := by
    have hnat : (945929049 : ℕ)^6111*100000000000000^5087 ≤ 40679199195597^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945929049 2000000000 40679199195597 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22724931/62500000 : ℝ)^6111 ≤ (29660400290697/100000000000000 : ℝ)^5087 := by
    have hnat : (22724931 : ℕ)^6111*100000000000000^5087 ≤ 29660400290697^5087*62500000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22724931 62500000 29660400290697 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1817994491/5000000000 : ℝ)^6111 ≤ (14830200253143/50000000000000 : ℝ)^5087 := by
    have hnat : (1817994491 : ℕ)^6111*50000000000000^5087 ≤ 14830200253143^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817994491 5000000000 14830200253143 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(945929049/2000000000 : ℝ), (22724931/62500000 : ℝ), (1817994491/5000000000 : ℝ)] ![(40679199195597/100000000000000 : ℝ), (29660400290697/100000000000000 : ℝ), (14830200253143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(945929049/2000000000 : ℝ)|^6111 ≤ (40679199195597/100000000000000 : ℝ)^5087
        have hw : |(945929049/2000000000 : ℝ)|=(945929049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22724931/62500000 : ℝ)|^6111 ≤ (29660400290697/100000000000000 : ℝ)^5087
        have hw : |(22724931/62500000 : ℝ)|=(22724931/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1817994491/5000000000 : ℝ)|^6111 ≤ (14830200253143/50000000000000 : ℝ)^5087
        have hw : |(1817994491/5000000000 : ℝ)|=(1817994491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_12 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-454009713/5000000000 : ℝ)*x 0 + (5602354741/10000000000 : ℝ)*x 1 + (5100601829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (454009713/5000000000 : ℝ)^6111 ≤ (350140535759/6250000000000 : ℝ)^5087 := by
    have hnat : (454009713 : ℕ)^6111*6250000000000^5087 ≤ 350140535759^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454009713 5000000000 350140535759 6250000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5602354741/10000000000 : ℝ)^6111 ≤ (9971218918127/20000000000000 : ℝ)^5087 := by
    have hnat : (5602354741 : ℕ)^6111*20000000000000^5087 ≤ 9971218918127^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602354741 10000000000 9971218918127 20000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100601829/10000000000 : ℝ)^6111 ≤ (8908331364859/20000000000000 : ℝ)^5087 := by
    have hnat : (5100601829 : ℕ)^6111*20000000000000^5087 ≤ 8908331364859^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100601829 10000000000 8908331364859 20000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-454009713/5000000000 : ℝ), (5602354741/10000000000 : ℝ), (5100601829/10000000000 : ℝ)] ![(350140535759/6250000000000 : ℝ), (9971218918127/20000000000000 : ℝ), (8908331364859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-454009713/5000000000 : ℝ)|^6111 ≤ (350140535759/6250000000000 : ℝ)^5087
        have hw : |(-454009713/5000000000 : ℝ)|=(454009713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5602354741/10000000000 : ℝ)|^6111 ≤ (9971218918127/20000000000000 : ℝ)^5087
        have hw : |(5602354741/10000000000 : ℝ)|=(5602354741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100601829/10000000000 : ℝ)|^6111 ≤ (8908331364859/20000000000000 : ℝ)^5087
        have hw : |(5100601829/10000000000 : ℝ)|=(5100601829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_13 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392862797/10000000000 : ℝ)*x 0 + (-300070669/2500000000 : ℝ)*x 1 + (5100601083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392862797/10000000000 : ℝ)^6111 ≤ (47625034286479/100000000000000 : ℝ)^5087 := by
    have hnat : (5392862797 : ℕ)^6111*100000000000000^5087 ≤ 47625034286479^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392862797 10000000000 47625034286479 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300070669/2500000000 : ℝ)^6111 ≤ (3916658347107/50000000000000 : ℝ)^5087 := by
    have hnat : (300070669 : ℕ)^6111*50000000000000^5087 ≤ 3916658347107^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300070669 2500000000 3916658347107 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100601083/10000000000 : ℝ)^6111 ≤ (22270824499197/50000000000000 : ℝ)^5087 := by
    have hnat : (5100601083 : ℕ)^6111*50000000000000^5087 ≤ 22270824499197^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100601083 10000000000 22270824499197 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392862797/10000000000 : ℝ), (-300070669/2500000000 : ℝ), (5100601083/10000000000 : ℝ)] ![(47625034286479/100000000000000 : ℝ), (3916658347107/50000000000000 : ℝ), (22270824499197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392862797/10000000000 : ℝ)|^6111 ≤ (47625034286479/100000000000000 : ℝ)^5087
        have hw : |(5392862797/10000000000 : ℝ)|=(5392862797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300070669/2500000000 : ℝ)|^6111 ≤ (3916658347107/50000000000000 : ℝ)^5087
        have hw : |(-300070669/2500000000 : ℝ)|=(300070669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100601083/10000000000 : ℝ)|^6111 ≤ (22270824499197/50000000000000 : ℝ)^5087
        have hw : |(5100601083/10000000000 : ℝ)|=(5100601083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_14 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392862639/10000000000 : ℝ)*x 0 + (2550300241/5000000000 : ℝ)*x 1 + (-240056739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392862639/10000000000 : ℝ)^6111 ≤ (2976564538143/6250000000000 : ℝ)^5087 := by
    have hnat : (5392862639 : ℕ)^6111*6250000000000^5087 ≤ 2976564538143^5087*10000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392862639 10000000000 2976564538143 6250000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2550300241/5000000000 : ℝ)^6111 ≤ (22270821346807/50000000000000 : ℝ)^5087 := by
    have hnat : (2550300241 : ℕ)^6111*50000000000000^5087 ≤ 22270821346807^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550300241 5000000000 22270821346807 50000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240056739/2000000000 : ℝ)^6111 ≤ (7833324683113/100000000000000 : ℝ)^5087 := by
    have hnat : (240056739 : ℕ)^6111*100000000000000^5087 ≤ 7833324683113^5087*2000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240056739 2000000000 7833324683113 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392862639/10000000000 : ℝ), (2550300241/5000000000 : ℝ), (-240056739/2000000000 : ℝ)] ![(2976564538143/6250000000000 : ℝ), (22270821346807/50000000000000 : ℝ), (7833324683113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392862639/10000000000 : ℝ)|^6111 ≤ (2976564538143/6250000000000 : ℝ)^5087
        have hw : |(5392862639/10000000000 : ℝ)|=(5392862639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2550300241/5000000000 : ℝ)|^6111 ≤ (22270821346807/50000000000000 : ℝ)^5087
        have hw : |(2550300241/5000000000 : ℝ)|=(2550300241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240056739/2000000000 : ℝ)|^6111 ≤ (7833324683113/100000000000000 : ℝ)^5087
        have hw : |(-240056739/2000000000 : ℝ)|=(240056739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1771_box_15 (p : ℝ) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131774551/400000000 : ℝ)*x 0 + (2176889761/5000000000 : ℝ)*x 1 + (1088446321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131774551/400000000 : ℝ)^6111 ≤ (26345121716071/100000000000000 : ℝ)^5087 := by
    have hnat : (131774551 : ℕ)^6111*100000000000000^5087 ≤ 26345121716071^5087*400000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131774551 400000000 26345121716071 100000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2176889761/5000000000 : ℝ)^6111 ≤ (1473096394239/4000000000000 : ℝ)^5087 := by
    have hnat : (2176889761 : ℕ)^6111*4000000000000^5087 ≤ 1473096394239^5087*5000000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176889761 5000000000 1473096394239 4000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088446321/2500000000 : ℝ)^6111 ≤ (7365493681241/20000000000000 : ℝ)^5087 := by
    have hnat : (1088446321 : ℕ)^6111*20000000000000^5087 ≤ 7365493681241^5087*2500000000^6111 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088446321 2500000000 7365493681241 20000000000000 6111 5087 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6111/1024 : ℝ)) 6111 5087 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131774551/400000000 : ℝ), (2176889761/5000000000 : ℝ), (1088446321/2500000000 : ℝ)] ![(26345121716071/100000000000000 : ℝ), (1473096394239/4000000000000 : ℝ), (7365493681241/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131774551/400000000 : ℝ)|^6111 ≤ (26345121716071/100000000000000 : ℝ)^5087
        have hw : |(131774551/400000000 : ℝ)|=(131774551/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2176889761/5000000000 : ℝ)|^6111 ≤ (1473096394239/4000000000000 : ℝ)^5087
        have hw : |(2176889761/5000000000 : ℝ)|=(2176889761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088446321/2500000000 : ℝ)|^6111 ≤ (7365493681241/20000000000000 : ℝ)^5087
        have hw : |(1088446321/2500000000 : ℝ)|=(1088446321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1771_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(8667/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5913/10000 : ℝ) ∧ (5169/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93273/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17573/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17573/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4629/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17573/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17573/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4629/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17573/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17573/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4629/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4629/50000 : ℝ) ^ (6095/1024 : ℝ) ≤ (3527985820269/5000000000000000000 : ℝ) := by
    have hpowers : (4629/50000 : ℝ)^6095 ≤ (3527985820269/5000000000000000000 : ℝ)^1024 := by
      have hnat : (4629 : ℕ)^6095*5000000000000000000^1024 ≤ 3527985820269^1024*50000^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4629 50000 3527985820269 5000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4629/50000 : ℝ)) (X := (3527985820269/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17573/100000 : ℝ) ^ (6095/1024 : ℝ) ≤ (1600223933985769/50000000000000000000 : ℝ) := by
    have hpowers : (17573/100000 : ℝ)^6095 ≤ (1600223933985769/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17573 : ℕ)^6095*50000000000000000000^1024 ≤ 1600223933985769^1024*100000^6095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17573 100000 1600223933985769 50000000000000000000 6095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17573/100000 : ℝ)) (X := (1600223933985769/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500003527985820269/2500000000000000000 : ℝ) ≤ (10000002370897693/10000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (2500003527985820269/2500000000000000000 : ℝ)^1024 ≤ (10000002370897693/10000000000000000 : ℝ)^6095 := by
      have hnat : (2500003527985820269 : ℕ)^1024*10000000000000000^6095 ≤ 10000002370897693^6095*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500003527985820269 2500000000000000000 10000002370897693 10000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002370897693/10000000000000000 : ℝ)) (X := (2500003527985820269/2500000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50001635503792188459/50000000000000000000 : ℝ) ≤ (5000027477163163/5000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (50001635503792188459/50000000000000000000 : ℝ)^1024 ≤ (5000027477163163/5000000000000000 : ℝ)^6095 := by
      have hnat : (50001635503792188459 : ℕ)^1024*5000000000000000^6095 ≤ 5000027477163163^6095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001635503792188459 50000000000000000000 5000027477163163 5000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000027477163163/5000000000000000 : ℝ)) (X := (50001635503792188459/50000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25001600223933985769/25000000000000000000 : ℝ) ≤ (10000107537754959/10000000000000000 : ℝ) ^ (6095/1024 : ℝ) := by
    have hpowers : (25001600223933985769/25000000000000000000 : ℝ)^1024 ≤ (10000107537754959/10000000000000000 : ℝ)^6095 := by
      have hnat : (25001600223933985769 : ℕ)^1024*10000000000000000^6095 ≤ 10000107537754959^6095*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001600223933985769 25000000000000000000 10000107537754959 10000000000000000 1024 6095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000107537754959/10000000000000000 : ℝ)) (X := (25001600223933985769/25000000000000000000 : ℝ)) (by norm_num) 6095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3527985820269/5000000000000000000 : ℝ) ≤ ((83149046079249748667/83150000000000000000 : ℝ)+2*(52583428633/831500000000000 : ℝ)*(4629/50000 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (83149046079249748667/83150000000000000000 : ℝ)+2*(52583428633/831500000000000 : ℝ)*(4629/50000 : ℝ)=(10000002370897693/10000000000000000 : ℝ) by norm_num, show 1+2*(3527985820269/5000000000000000000 : ℝ)=(2500003527985820269/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1600223933985769/50000000000000000000 : ℝ)+(3527985820269/5000000000000000000 : ℝ) ≤ ((83149046079249748667/83150000000000000000 : ℝ)+(52583428633/831500000000000 : ℝ)*((17573/100000 : ℝ)+(4629/50000 : ℝ)))^(6095/1024 : ℝ) := by
    rw [show (83149046079249748667/83150000000000000000 : ℝ)+(52583428633/831500000000000 : ℝ)*((17573/100000 : ℝ)+(4629/50000 : ℝ))=(5000027477163163/5000000000000000 : ℝ) by norm_num, show 1+(1600223933985769/50000000000000000000 : ℝ)+(3527985820269/5000000000000000000 : ℝ)=(50001635503792188459/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1600223933985769/50000000000000000000 : ℝ) ≤ ((83149046079249748667/83150000000000000000 : ℝ)+2*(52583428633/831500000000000 : ℝ)*(17573/100000 : ℝ))^(6095/1024 : ℝ) := by
    rw [show (83149046079249748667/83150000000000000000 : ℝ)+2*(52583428633/831500000000000 : ℝ)*(17573/100000 : ℝ)=(10000107537754959/10000000000000000 : ℝ) by norm_num, show 1+2*(1600223933985769/50000000000000000000 : ℝ)=(25001600223933985769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (83149046079249748667/83150000000000000000 : ℝ)*(X 1 0+X 2 0)+(52583428633/831500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (4629/50000 : ℝ)) (hi := (17573/100000 : ℝ)) (c := (83149046079249748667/83150000000000000000 : ℝ)) (alpha := (52583428633/831500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (83149046079249748667/83150000000000000000 : ℝ)*(X 0 1+X 2 1)+(52583428633/831500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (4629/50000 : ℝ)) (hi := (17573/100000 : ℝ)) (c := (83149046079249748667/83150000000000000000 : ℝ)) (alpha := (52583428633/831500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (83149046079249748667/83150000000000000000 : ℝ)*(X 0 2+X 1 2)+(52583428633/831500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6095/1024 : ℝ)) (lo := (4629/50000 : ℝ)) (hi := (17573/100000 : ℝ)) (c := (83149046079249748667/83150000000000000000 : ℝ)) (alpha := (52583428633/831500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-759683023/10000000000 : ℝ)*X 0 0+(1350904029/2500000000 : ℝ)*X 0 1+(1080722757/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((103833419/200000000 : ℝ)*X 1 0+(-106199761/1000000000 : ℝ)*X 1 1+(270180757/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2595835667/5000000000 : ℝ)*X 2 0+(5403614743/10000000000 : ℝ)*X 2 1+(-1061997631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((225156633/500000000 : ℝ)*X 0 0+(469304269/1250000000 : ℝ)*X 0 1+(750886717/2000000000 : ℝ)*X 0 2+(225156633/500000000 : ℝ)*X 1 0+(469304269/1250000000 : ℝ)*X 1 1+(750886717/2000000000 : ℝ)*X 1 2+(225156633/500000000 : ℝ)*X 2 0+(469304269/1250000000 : ℝ)*X 2 1+(750886717/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1507534313/10000000000 : ℝ)*X 0 0+(1282489373/2500000000 : ℝ)*X 0 1+(128248961/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686651367/5000000000 : ℝ)*X 1 0+(-1187424051/10000000000 : ℝ)*X 1 1+(5129956909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537330123/1000000000 : ℝ)*X 2 0+(5129958477/10000000000 : ℝ)*X 2 1+(-74213999/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3416136699/10000000000 : ℝ)*X 0 0+(859185931/2000000000 : ℝ)*X 0 1+(6873487/16000000 : ℝ)*X 0 2+(3416136699/10000000000 : ℝ)*X 1 0+(859185931/2000000000 : ℝ)*X 1 1+(6873487/16000000 : ℝ)*X 1 2+(3416136699/10000000000 : ℝ)*X 2 0+(859185931/2000000000 : ℝ)*X 2 1+(6873487/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-168061021/1250000000 : ℝ)*X 0 0+(4919637919/10000000000 : ℝ)*X 0 1+(1365813137/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((206086827/400000000 : ℝ)*X 1 0+(-258351521/2500000000 : ℝ)*X 1 1+(5463252877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5152170679/10000000000 : ℝ)*X 2 0+(341453273/625000000 : ℝ)*X 2 1+(-1033406789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((945929049/2000000000 : ℝ)*X 0 0+(22724931/62500000 : ℝ)*X 0 1+(1817994491/5000000000 : ℝ)*X 0 2+(945929049/2000000000 : ℝ)*X 1 0+(22724931/62500000 : ℝ)*X 1 1+(1817994491/5000000000 : ℝ)*X 1 2+(945929049/2000000000 : ℝ)*X 2 0+(22724931/62500000 : ℝ)*X 2 1+(1817994491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-454009713/5000000000 : ℝ)*X 0 0+(5602354741/10000000000 : ℝ)*X 0 1+(5100601829/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392862797/10000000000 : ℝ)*X 1 0+(-300070669/2500000000 : ℝ)*X 1 1+(5100601083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5392862639/10000000000 : ℝ)*X 2 0+(2550300241/5000000000 : ℝ)*X 2 1+(-240056739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((131774551/400000000 : ℝ)*X 0 0+(2176889761/5000000000 : ℝ)*X 0 1+(1088446321/2500000000 : ℝ)*X 0 2+(131774551/400000000 : ℝ)*X 1 0+(2176889761/5000000000 : ℝ)*X 1 1+(1088446321/2500000000 : ℝ)*X 1 2+(131774551/400000000 : ℝ)*X 2 0+(2176889761/5000000000 : ℝ)*X 2 1+(1088446321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1771_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8667/12500 : ℝ) ≤ (-1441261274054865364373302668220059/2078750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115573619/100000000000000 : ℝ)*(upper1) + (77491203/50000000000000 : ℝ)*(lower4) + (36854169/100000000000000 : ℝ)*(upper5) + (1121272922493941/100000000000000 : ℝ)*(major0) + (1121272922493941/100000000000000 : ℝ)*(major1) + (1121272922493941/100000000000000 : ℝ)*(major2) + (5437420717/100000000000000 : ℝ)*(sp1) + (104776247/6250000000000 : ℝ)*(sp3) + (1774766194645769/100000000000000 : ℝ)*(sp4) + (177476325886747/10000000000000 : ℝ)*(sp5) + (354952391505689/20000000000000 : ℝ)*(sp6) + (490886496918823/100000000000000 : ℝ)*(sp7) + (1250821209/50000000000000 : ℝ)*(sp12) + (3369379871/50000000000000 : ℝ)*(sp14) + (19635526933551/4000000000000 : ℝ)*(f.failure) + (1774768696288187/100000000000000 : ℝ)*(f.sum) + (97888371847253/41575000000000000000000000000 : ℝ)*base65 + (5289687937979373353/8315000000000000000000000000000000 : ℝ)*base68 + (47976275154159373353/8315000000000000000000000000000000 : ℝ)*base70 + (21345951873659373353/8315000000000000000000000000000000 : ℝ)*base72 + (121393703950989/20787500000000000000000000000 : ℝ)*base73 + (2528346962520626647/8315000000000000000000000000000000 : ℝ)*base75 + (33284897930429373353/8315000000000000000000000000000000 : ℝ)*base78 + (45094580951224373353/8315000000000000000000000000000000 : ℝ)*base80 + (45621834450507/10393750000000000000000000000 : ℝ)*base81 + (140309/20000000000000000000 : ℝ)*base89 + (140309/20000000000000000000 : ℝ)*base91 + (140309/20000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5913/10000 : ℝ) ≤ (614604101601846788862591915849183/1039375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4760863/50000000000000 : ℝ)*(upper0) + (14986371/50000000000000 : ℝ)*(upper3) + (53174007/100000000000000 : ℝ)*(upper4) + (314342927727061/25000000000000 : ℝ)*(major0) + (314342927727061/25000000000000 : ℝ)*(major1) + (314342927727061/25000000000000 : ℝ)*(major2) + (486138172167619/25000000000000 : ℝ)*(sp0) + (1944554429997603/100000000000000 : ℝ)*(sp1) + (1944555613496419/100000000000000 : ℝ)*(sp2) + (275234940429917/50000000000000 : ℝ)*(sp3) + (6694636763/100000000000000 : ℝ)*(sp5) + (5511137947/100000000000000 : ℝ)*(sp6) + (1721542509/100000000000000 : ℝ)*(sp7) + (843596389/10000000000000 : ℝ)*(sp8) + (550471602402343/100000000000000 : ℝ)*(f.failure) + (972280562317183/50000000000000 : ℝ)*(f.sum) + (173382633346273/41575000000000000000000000000 : ℝ)*base66 + (20027732728422872313/2078750000000000000000000000000000 : ℝ)*base68 + (10808349375332872313/2078750000000000000000000000000000 : ℝ)*base70 + (14957178863350372313/2078750000000000000000000000000000 : ℝ)*base72 + (1616913189753/2598437500000000000000000000 : ℝ)*base74 + (8765253278384122313/2078750000000000000000000000000000 : ℝ)*base76 + (5642684399390372313/2078750000000000000000000000000000 : ℝ)*base78 + (14476214476335372313/2078750000000000000000000000000000 : ℝ)*base80 + (20000139687787/10393750000000000000000000000 : ℝ)*base82 + (672637/500000000000000000000 : ℝ)*base89 + (672637/500000000000000000000 : ℝ)*base91 + (672637/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5169/6250 : ℝ) ≤ (3438527322325915936132988560610307/4157500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1227437/2500000000000 : ℝ)*(upper1) + (107113337/100000000000000 : ℝ)*(upper2) + (42957/3125000000000 : ℝ)*(lower5) + (1195175682337231/100000000000000 : ℝ)*(major0) + (1195175682337231/100000000000000 : ℝ)*(major1) + (1195175682337231/100000000000000 : ℝ)*(major2) + (6825848267/25000000000000 : ℝ)*(sp1) + (2470677/62500000000 : ℝ)*(sp3) + (537296701/50000000000000 : ℝ)*(sp4) + (1839538475601649/100000000000000 : ℝ)*(sp8) + (1839512726529291/100000000000000 : ℝ)*(sp9) + (1839540029922359/100000000000000 : ℝ)*(sp10) + (261619255788041/50000000000000 : ℝ)*(sp11) + (119931827/25000000000000 : ℝ)*(sp12) + (523242464659283/100000000000000 : ℝ)*(f.failure) + (1839540029922359/100000000000000 : ℝ)*(f.sum) + (307480818962423/41575000000000000000000000000 : ℝ)*base65 + (59540578180064021077/8315000000000000000000000000000000 : ℝ)*base67 + (52902324330189021077/8315000000000000000000000000000000 : ℝ)*base69 + (48708681295184021077/8315000000000000000000000000000000 : ℝ)*base71 + (189330399161523/41575000000000000000000000000 : ℝ)*base73 + (74522497884344021077/8315000000000000000000000000000000 : ℝ)*base75 + (86121227750344021077/8315000000000000000000000000000000 : ℝ)*base77 + (75347953037329021077/8315000000000000000000000000000000 : ℝ)*base79 + (36382127576281/5196875000000000000000000000 : ℝ)*base81 + (815903/500000000000000000000 : ℝ)*base90 + (815903/500000000000000000000 : ℝ)*base92 + (815903/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-93273/100000 : ℝ) ≤ (-1938852646912723721413912320816693/2078750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6260941/50000000000000 : ℝ)*(upper3) + (38348807/12500000000000 : ℝ)*(lower4) + (153596119/50000000000000 : ℝ)*(upper5) + (1255873588038693/100000000000000 : ℝ)*(major0) + (1255873588038693/100000000000000 : ℝ)*(major1) + (1255873588038693/100000000000000 : ℝ)*(major2) + (1082894163/12500000000000 : ℝ)*(sp4) + (6357626143/10000000000000 : ℝ)*(sp5) + (8172341459/4000000000000 : ℝ)*(sp6) + (12049928039/25000000000000 : ℝ)*(sp7) + (79720512892933/4000000000000 : ℝ)*(sp12) + (1992957909215199/100000000000000 : ℝ)*(sp13) + (996408588470077/50000000000000 : ℝ)*(sp14) + (68720941416021/12500000000000 : ℝ)*(sp15) + (137453932760081/25000000000000 : ℝ)*(f.failure) + (1993021485476629/100000000000000 : ℝ)*(f.sum) + (5058931780519/41575000000000000000000000000 : ℝ)*base65 + (32461739444346927769/8315000000000000000000000000000000 : ℝ)*base68 + (26536843091333072231/8315000000000000000000000000000000 : ℝ)*base69 + (25891440524283072231/8315000000000000000000000000000000 : ℝ)*base71 + (179169072147981/41575000000000000000000000000 : ℝ)*base74 + (38800360516703072231/8315000000000000000000000000000000 : ℝ)*base75 + (25965698188888072231/8315000000000000000000000000000000 : ℝ)*base77 + (4793489921503072231/8315000000000000000000000000000000 : ℝ)*base79 + (21890107385019/41575000000000000000000000000 : ℝ)*base81 + (320421/125000000000000000000 : ℝ)*base90 + (320421/125000000000000000000 : ℝ)*base92 + (320421/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1771_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8667/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(5913/10000 : ℝ) else (5169/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93273/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1771_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1771_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8667/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(5913/10000 : ℝ) else (5169/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93273/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1771_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6095/1024 : ℝ) ≤ p) (hpb : p ≤ (6111/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11420859/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17573/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4629/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8667/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(5913/10000 : ℝ) else (5169/6250 : ℝ) ≤ X j i ∧ X j i ≤ (93273/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1771_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

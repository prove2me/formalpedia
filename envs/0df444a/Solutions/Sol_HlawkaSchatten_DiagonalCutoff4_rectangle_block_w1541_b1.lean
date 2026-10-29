-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1541_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:07:31.355973+00:00
-- url     : https://prove2.me/submissions/02f27f26-bec9-4873-9717-19c46546dd06

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
theorem support_rectangle_w1541_s3_0 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-228207029/1250000000 : ℝ)*x 0 + (339489547/625000000 : ℝ)*x 1 + (2608429741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228207029/1250000000 : ℝ)^4579 ≤ (11185990232787/100000000000000 : ℝ)^3555 := by
    have hnat : (228207029 : ℕ)^4579*100000000000000^3555 ≤ 11185990232787^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228207029 1250000000 11185990232787 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339489547/625000000 : ℝ)^4579 ≤ (22780802798571/50000000000000 : ℝ)^3555 := by
    have hnat : (339489547 : ℕ)^4579*50000000000000^3555 ≤ 22780802798571^3555*625000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339489547 625000000 22780802798571 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608429741/5000000000 : ℝ)^4579 ≤ (21626202078817/50000000000000 : ℝ)^3555 := by
    have hnat : (2608429741 : ℕ)^4579*50000000000000^3555 ≤ 21626202078817^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608429741 5000000000 21626202078817 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-228207029/1250000000 : ℝ), (339489547/625000000 : ℝ), (2608429741/5000000000 : ℝ)] ![(11185990232787/100000000000000 : ℝ), (22780802798571/50000000000000 : ℝ), (21626202078817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-228207029/1250000000 : ℝ)|^4579 ≤ (11185990232787/100000000000000 : ℝ)^3555
        have hw : |(-228207029/1250000000 : ℝ)|=(228207029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339489547/625000000 : ℝ)|^4579 ≤ (22780802798571/50000000000000 : ℝ)^3555
        have hw : |(339489547/625000000 : ℝ)|=(339489547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608429741/5000000000 : ℝ)|^4579 ≤ (21626202078817/50000000000000 : ℝ)^3555
        have hw : |(2608429741/5000000000 : ℝ)|=(2608429741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_1 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675275307/5000000000 : ℝ)*x 0 + (-120984137/625000000 : ℝ)*x 1 + (2608429833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675275307/5000000000 : ℝ)^4579 ≤ (11171333642703/25000000000000 : ℝ)^3555 := by
    have hnat : (2675275307 : ℕ)^4579*25000000000000^3555 ≤ 11171333642703^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675275307 5000000000 11171333642703 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120984137/625000000 : ℝ)^4579 ≤ (6031129645731/50000000000000 : ℝ)^3555 := by
    have hnat : (120984137 : ℕ)^4579*50000000000000^3555 ≤ 6031129645731^3555*625000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120984137 625000000 6031129645731 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608429833/5000000000 : ℝ)^4579 ≤ (43252406122577/100000000000000 : ℝ)^3555 := by
    have hnat : (2608429833 : ℕ)^4579*100000000000000^3555 ≤ 43252406122577^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608429833 5000000000 43252406122577 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675275307/5000000000 : ℝ), (-120984137/625000000 : ℝ), (2608429833/5000000000 : ℝ)] ![(11171333642703/25000000000000 : ℝ), (6031129645731/50000000000000 : ℝ), (43252406122577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675275307/5000000000 : ℝ)|^4579 ≤ (11171333642703/25000000000000 : ℝ)^3555
        have hw : |(2675275307/5000000000 : ℝ)|=(2675275307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-120984137/625000000 : ℝ)|^4579 ≤ (6031129645731/50000000000000 : ℝ)^3555
        have hw : |(-120984137/625000000 : ℝ)|=(120984137/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608429833/5000000000 : ℝ)|^4579 ≤ (43252406122577/100000000000000 : ℝ)^3555
        have hw : |(2608429833/5000000000 : ℝ)|=(2608429833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_2 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675275263/5000000000 : ℝ)*x 0 + (5216859721/10000000000 : ℝ)*x 1 + (-1935746237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675275263/5000000000 : ℝ)^4579 ≤ (22342666812091/50000000000000 : ℝ)^3555 := by
    have hnat : (2675275263 : ℕ)^4579*50000000000000^3555 ≤ 22342666812091^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675275263 5000000000 22342666812091 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216859721/10000000000 : ℝ)^4579 ≤ (10813101677481/25000000000000 : ℝ)^3555 := by
    have hnat : (5216859721 : ℕ)^4579*25000000000000^3555 ≤ 10813101677481^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216859721 10000000000 10813101677481 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935746237/10000000000 : ℝ)^4579 ≤ (6031129826321/50000000000000 : ℝ)^3555 := by
    have hnat : (1935746237 : ℕ)^4579*50000000000000^3555 ≤ 6031129826321^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935746237 10000000000 6031129826321 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675275263/5000000000 : ℝ), (5216859721/10000000000 : ℝ), (-1935746237/10000000000 : ℝ)] ![(22342666812091/50000000000000 : ℝ), (10813101677481/25000000000000 : ℝ), (6031129826321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675275263/5000000000 : ℝ)|^4579 ≤ (22342666812091/50000000000000 : ℝ)^3555
        have hw : |(2675275263/5000000000 : ℝ)|=(2675275263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216859721/10000000000 : ℝ)|^4579 ≤ (10813101677481/25000000000000 : ℝ)^3555
        have hw : |(5216859721/10000000000 : ℝ)|=(5216859721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1935746237/10000000000 : ℝ)|^4579 ≤ (6031129826321/50000000000000 : ℝ)^3555
        have hw : |(-1935746237/10000000000 : ℝ)|=(1935746237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_3 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128116873/5000000000 : ℝ)*x 0 + (802706663/2000000000 : ℝ)*x 1 + (4510982089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128116873/5000000000 : ℝ)^4579 ≤ (16639417324627/50000000000000 : ℝ)^3555 := by
    have hnat : (2128116873 : ℕ)^4579*50000000000000^3555 ≤ 16639417324627^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128116873 5000000000 16639417324627 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802706663/2000000000 : ℝ)^4579 ≤ (30854944345477/100000000000000 : ℝ)^3555 := by
    have hnat : (802706663 : ℕ)^4579*100000000000000^3555 ≤ 30854944345477^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802706663 2000000000 30854944345477 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510982089/10000000000 : ℝ)^4579 ≤ (17933110495339/50000000000000 : ℝ)^3555 := by
    have hnat : (4510982089 : ℕ)^4579*50000000000000^3555 ≤ 17933110495339^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510982089 10000000000 17933110495339 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128116873/5000000000 : ℝ), (802706663/2000000000 : ℝ), (4510982089/10000000000 : ℝ)] ![(16639417324627/50000000000000 : ℝ), (30854944345477/100000000000000 : ℝ), (17933110495339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128116873/5000000000 : ℝ)|^4579 ≤ (16639417324627/50000000000000 : ℝ)^3555
        have hw : |(2128116873/5000000000 : ℝ)|=(2128116873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802706663/2000000000 : ℝ)|^4579 ≤ (30854944345477/100000000000000 : ℝ)^3555
        have hw : |(802706663/2000000000 : ℝ)|=(802706663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510982089/10000000000 : ℝ)|^4579 ≤ (17933110495339/50000000000000 : ℝ)^3555
        have hw : |(4510982089/10000000000 : ℝ)|=(4510982089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_4 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1825685669/10000000000 : ℝ)*x 0 + (5217995907/10000000000 : ℝ)*x 1 + (678835987/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1825685669/10000000000 : ℝ)^4579 ≤ (5593111274903/50000000000000 : ℝ)^3555 := by
    have hnat : (1825685669 : ℕ)^4579*50000000000000^3555 ≤ 5593111274903^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1825685669 10000000000 5593111274903 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217995907/10000000000 : ℝ)^4579 ≤ (21632270232339/50000000000000 : ℝ)^3555 := by
    have hnat : (5217995907 : ℕ)^4579*50000000000000^3555 ≤ 21632270232339^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217995907 10000000000 21632270232339 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678835987/1250000000 : ℝ)^4579 ≤ (45549236974211/100000000000000 : ℝ)^3555 := by
    have hnat : (678835987 : ℕ)^4579*100000000000000^3555 ≤ 45549236974211^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678835987 1250000000 45549236974211 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1825685669/10000000000 : ℝ), (5217995907/10000000000 : ℝ), (678835987/1250000000 : ℝ)] ![(5593111274903/50000000000000 : ℝ), (21632270232339/50000000000000 : ℝ), (45549236974211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1825685669/10000000000 : ℝ)|^4579 ≤ (5593111274903/50000000000000 : ℝ)^3555
        have hw : |(-1825685669/10000000000 : ℝ)|=(1825685669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217995907/10000000000 : ℝ)|^4579 ≤ (21632270232339/50000000000000 : ℝ)^3555
        have hw : |(5217995907/10000000000 : ℝ)|=(5217995907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678835987/1250000000 : ℝ)|^4579 ≤ (45549236974211/100000000000000 : ℝ)^3555
        have hw : |(678835987/1250000000 : ℝ)|=(678835987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_5 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323470711/2500000000 : ℝ)*x 0 + (-53809931/312500000 : ℝ)*x 1 + (2715343957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323470711/2500000000 : ℝ)^4579 ≤ (11019170637389/25000000000000 : ℝ)^3555 := by
    have hnat : (1323470711 : ℕ)^4579*25000000000000^3555 ≤ 11019170637389^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323470711 2500000000 11019170637389 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53809931/312500000 : ℝ)^4579 ≤ (2074816052539/20000000000000 : ℝ)^3555 := by
    have hnat : (53809931 : ℕ)^4579*20000000000000^3555 ≤ 2074816052539^3555*312500000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53809931 312500000 2074816052539 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715343957/5000000000 : ℝ)^4579 ≤ (45549237168671/100000000000000 : ℝ)^3555 := by
    have hnat : (2715343957 : ℕ)^4579*100000000000000^3555 ≤ 45549237168671^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715343957 5000000000 45549237168671 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323470711/2500000000 : ℝ), (-53809931/312500000 : ℝ), (2715343957/5000000000 : ℝ)] ![(11019170637389/25000000000000 : ℝ), (2074816052539/20000000000000 : ℝ), (45549237168671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323470711/2500000000 : ℝ)|^4579 ≤ (11019170637389/25000000000000 : ℝ)^3555
        have hw : |(1323470711/2500000000 : ℝ)|=(1323470711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53809931/312500000 : ℝ)|^4579 ≤ (2074816052539/20000000000000 : ℝ)^3555
        have hw : |(-53809931/312500000 : ℝ)|=(53809931/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715343957/5000000000 : ℝ)|^4579 ≤ (45549237168671/100000000000000 : ℝ)^3555
        have hw : |(2715343957/5000000000 : ℝ)|=(2715343957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_6 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058776577/2000000000 : ℝ)*x 0 + (2715343943/5000000000 : ℝ)*x 1 + (-860958887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058776577/2000000000 : ℝ)^4579 ≤ (44076682989249/100000000000000 : ℝ)^3555 := by
    have hnat : (1058776577 : ℕ)^4579*100000000000000^3555 ≤ 44076682989249^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058776577 2000000000 44076682989249 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715343943/5000000000 : ℝ)^4579 ≤ (22774618433089/50000000000000 : ℝ)^3555 := by
    have hnat : (2715343943 : ℕ)^4579*50000000000000^3555 ≤ 22774618433089^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715343943 5000000000 22774618433089 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860958887/5000000000 : ℝ)^4579 ≤ (10374080123013/100000000000000 : ℝ)^3555 := by
    have hnat : (860958887 : ℕ)^4579*100000000000000^3555 ≤ 10374080123013^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860958887 5000000000 10374080123013 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058776577/2000000000 : ℝ), (2715343943/5000000000 : ℝ), (-860958887/5000000000 : ℝ)] ![(44076682989249/100000000000000 : ℝ), (22774618433089/50000000000000 : ℝ), (10374080123013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058776577/2000000000 : ℝ)|^4579 ≤ (44076682989249/100000000000000 : ℝ)^3555
        have hw : |(1058776577/2000000000 : ℝ)|=(1058776577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715343943/5000000000 : ℝ)|^4579 ≤ (22774618433089/50000000000000 : ℝ)^3555
        have hw : |(2715343943/5000000000 : ℝ)|=(2715343943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-860958887/5000000000 : ℝ)|^4579 ≤ (10374080123013/100000000000000 : ℝ)^3555
        have hw : |(-860958887/5000000000 : ℝ)|=(860958887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s3_7 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064075503/2500000000 : ℝ)*x 0 + (4508352353/10000000000 : ℝ)*x 1 + (4016183153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064075503/2500000000 : ℝ)^4579 ≤ (415994026993/1250000000000 : ℝ)^3555 := by
    have hnat : (1064075503 : ℕ)^4579*1250000000000^3555 ≤ 415994026993^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064075503 2500000000 415994026993 1250000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508352353/10000000000 : ℝ)^4579 ≤ (35839291927967/100000000000000 : ℝ)^3555 := by
    have hnat : (4508352353 : ℕ)^4579*100000000000000^3555 ≤ 35839291927967^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508352353 10000000000 35839291927967 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4016183153/10000000000 : ℝ)^4579 ≤ (30881185899169/100000000000000 : ℝ)^3555 := by
    have hnat : (4016183153 : ℕ)^4579*100000000000000^3555 ≤ 30881185899169^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4016183153 10000000000 30881185899169 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064075503/2500000000 : ℝ), (4508352353/10000000000 : ℝ), (4016183153/10000000000 : ℝ)] ![(415994026993/1250000000000 : ℝ), (35839291927967/100000000000000 : ℝ), (30881185899169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064075503/2500000000 : ℝ)|^4579 ≤ (415994026993/1250000000000 : ℝ)^3555
        have hw : |(1064075503/2500000000 : ℝ)|=(1064075503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508352353/10000000000 : ℝ)|^4579 ≤ (35839291927967/100000000000000 : ℝ)^3555
        have hw : |(4508352353/10000000000 : ℝ)|=(4508352353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4016183153/10000000000 : ℝ)|^4579 ≤ (30881185899169/100000000000000 : ℝ)^3555
        have hw : |(4016183153/10000000000 : ℝ)|=(4016183153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1541_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5489/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7767/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1987/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2129/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1987/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2129/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1987/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2129/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1987/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2129/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1987/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2129/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1987/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2129/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2129/20000 : ℝ) ^ (4577/1024 : ℝ) ≤ (4483396421773921/100000000000000000000 : ℝ) := by
    have hpowers : (2129/20000 : ℝ)^4577 ≤ (4483396421773921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2129 : ℕ)^4577*100000000000000000000^1024 ≤ 4483396421773921^1024*20000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2129 20000 4483396421773921 100000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2129/20000 : ℝ)) (X := (4483396421773921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1987/12500 : ℝ) ^ (4577/1024 : ℝ) ≤ (26913805261462271/100000000000000000000 : ℝ) := by
    have hpowers : (1987/12500 : ℝ)^4577 ≤ (26913805261462271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1987 : ℕ)^4577*100000000000000000000^1024 ≤ 26913805261462271^1024*12500^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1987 12500 26913805261462271 100000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1987/12500 : ℝ)) (X := (26913805261462271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004483396421773921/50000000000000000000 : ℝ) ≤ (10000200604682637/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (50004483396421773921/50000000000000000000 : ℝ)^1024 ≤ (10000200604682637/10000000000000000 : ℝ)^4577 := by
      have hnat : (50004483396421773921 : ℕ)^1024*10000000000000000^4577 ≤ 10000200604682637^4577*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004483396421773921 50000000000000000000 10000200604682637 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000200604682637/10000000000000000 : ℝ)) (X := (50004483396421773921/50000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125981162552601131/3125000000000000000 : ℝ) ≤ (5000351177815561/5000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (3125981162552601131/3125000000000000000 : ℝ)^1024 ≤ (5000351177815561/5000000000000000 : ℝ)^4577 := by
      have hnat : (3125981162552601131 : ℕ)^1024*5000000000000000^4577 ≤ 5000351177815561^4577*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125981162552601131 3125000000000000000 5000351177815561 5000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000351177815561/5000000000000000 : ℝ)) (X := (3125981162552601131/3125000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026913805261462271/50000000000000000000 : ℝ) ≤ (10001204106579607/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (50026913805261462271/50000000000000000000 : ℝ)^1024 ≤ (10001204106579607/10000000000000000 : ℝ)^4577 := by
      have hnat : (50026913805261462271 : ℕ)^1024*10000000000000000^4577 ≤ 10001204106579607^4577*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026913805261462271 50000000000000000000 10001204106579607 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001204106579607/10000000000000000 : ℝ)) (X := (50026913805261462271/50000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4483396421773921/100000000000000000000 : ℝ) ≤ ((52500371097495281237/52510000000000000000 : ℝ)+2*(100350189697/105020000000000 : ℝ)*(2129/20000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (52500371097495281237/52510000000000000000 : ℝ)+2*(100350189697/105020000000000 : ℝ)*(2129/20000 : ℝ)=(10000200604682637/10000000000000000 : ℝ) by norm_num, show 1+2*(4483396421773921/100000000000000000000 : ℝ)=(50004483396421773921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26913805261462271/100000000000000000000 : ℝ)+(4483396421773921/100000000000000000000 : ℝ) ≤ ((52500371097495281237/52510000000000000000 : ℝ)+(100350189697/105020000000000 : ℝ)*((1987/12500 : ℝ)+(2129/20000 : ℝ)))^(4577/1024 : ℝ) := by
    rw [show (52500371097495281237/52510000000000000000 : ℝ)+(100350189697/105020000000000 : ℝ)*((1987/12500 : ℝ)+(2129/20000 : ℝ))=(5000351177815561/5000000000000000 : ℝ) by norm_num, show 1+(26913805261462271/100000000000000000000 : ℝ)+(4483396421773921/100000000000000000000 : ℝ)=(3125981162552601131/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26913805261462271/100000000000000000000 : ℝ) ≤ ((52500371097495281237/52510000000000000000 : ℝ)+2*(100350189697/105020000000000 : ℝ)*(1987/12500 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (52500371097495281237/52510000000000000000 : ℝ)+2*(100350189697/105020000000000 : ℝ)*(1987/12500 : ℝ)=(10001204106579607/10000000000000000 : ℝ) by norm_num, show 1+2*(26913805261462271/100000000000000000000 : ℝ)=(50026913805261462271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52500371097495281237/52510000000000000000 : ℝ)*(X 1 0+X 2 0)+(100350189697/105020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (2129/20000 : ℝ)) (hi := (1987/12500 : ℝ)) (c := (52500371097495281237/52510000000000000000 : ℝ)) (alpha := (100350189697/105020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52500371097495281237/52510000000000000000 : ℝ)*(X 0 1+X 2 1)+(100350189697/105020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (2129/20000 : ℝ)) (hi := (1987/12500 : ℝ)) (c := (52500371097495281237/52510000000000000000 : ℝ)) (alpha := (100350189697/105020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52500371097495281237/52510000000000000000 : ℝ)*(X 0 2+X 1 2)+(100350189697/105020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (2129/20000 : ℝ)) (hi := (1987/12500 : ℝ)) (c := (52500371097495281237/52510000000000000000 : ℝ)) (alpha := (100350189697/105020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-228207029/1250000000 : ℝ)*X 0 0+(339489547/625000000 : ℝ)*X 0 1+(2608429741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675275307/5000000000 : ℝ)*X 1 0+(-120984137/625000000 : ℝ)*X 1 1+(2608429833/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675275263/5000000000 : ℝ)*X 2 0+(5216859721/10000000000 : ℝ)*X 2 1+(-1935746237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2128116873/5000000000 : ℝ)*X 0 0+(802706663/2000000000 : ℝ)*X 0 1+(4510982089/10000000000 : ℝ)*X 0 2+(2128116873/5000000000 : ℝ)*X 1 0+(802706663/2000000000 : ℝ)*X 1 1+(4510982089/10000000000 : ℝ)*X 1 2+(2128116873/5000000000 : ℝ)*X 2 0+(802706663/2000000000 : ℝ)*X 2 1+(4510982089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1825685669/10000000000 : ℝ)*X 0 0+(5217995907/10000000000 : ℝ)*X 0 1+(678835987/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323470711/2500000000 : ℝ)*X 1 0+(-53809931/312500000 : ℝ)*X 1 1+(2715343957/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058776577/2000000000 : ℝ)*X 2 0+(2715343943/5000000000 : ℝ)*X 2 1+(-860958887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1064075503/2500000000 : ℝ)*X 0 0+(4508352353/10000000000 : ℝ)*X 0 1+(4016183153/10000000000 : ℝ)*X 0 2+(1064075503/2500000000 : ℝ)*X 1 0+(4508352353/10000000000 : ℝ)*X 1 1+(4016183153/10000000000 : ℝ)*X 1 2+(1064075503/2500000000 : ℝ)*X 2 0+(4508352353/10000000000 : ℝ)*X 2 1+(4016183153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (705974141634488757743199927/105020000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1105917433/100000000000000 : ℝ)*(base19) + (994261163/100000000000000 : ℝ)*(base23) + (18806617/100000000000000 : ℝ)*(lower2) + (248869859/100000000000000 : ℝ)*(upper3) + (5236919/3125000000000 : ℝ)*(upper5) + (133241080205181/4000000000000 : ℝ)*(major0) + (133241080205181/4000000000000 : ℝ)*(major1) + (133241080205181/4000000000000 : ℝ)*(major2) + (2325880264592349/50000000000000 : ℝ)*(sp0) + (2325888262851643/50000000000000 : ℝ)*(sp1) + (1162944159339889/25000000000000 : ℝ)*(sp2) + (502566563972291/25000000000000 : ℝ)*(sp3) + (17102436021/100000000000000 : ℝ)*(sp4) + (9898673063/100000000000000 : ℝ)*(sp7) + (2010276154562227/100000000000000 : ℝ)*(f.failure) + (58147220395259/1250000000000 : ℝ)*(f.sum) + (1980880770497/262550000000000000000000000 : ℝ)*base66 + (280556874084308897/210040000000000000000000000000000 : ℝ)*base67 + (2499579349088508897/210040000000000000000000000000000 : ℝ)*base69 + (2084298927549828897/210040000000000000000000000000000 : ℝ)*base71 + (8461782014203/1312750000000000000000000000 : ℝ)*base74 + (1624268267879548897/210040000000000000000000000000000 : ℝ)*base75 + (1162356275748897/210040000000000000000000000000000 : ℝ)*base77 + (2437699404196988897/210040000000000000000000000000000 : ℝ)*base79 + (480903453411/656375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (31595417/10000000000000000000000 : ℝ)*base89 + (31595417/10000000000000000000000 : ℝ)*base91 + (31595417/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (248734719663736744869982179/20511718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1905590909/100000000000000 : ℝ)*(base19) + (532646979/25000000000000 : ℝ)*(base23) + (63178431/25000000000000 : ℝ)*(upper3) + (40837057/50000000000000 : ℝ)*(lower4) + (24213551/10000000000000 : ℝ)*(upper5) + (105210231308669/3125000000000 : ℝ)*(major0) + (105210231308669/3125000000000 : ℝ)*(major1) + (105210231308669/3125000000000 : ℝ)*(major2) + (29297961271/100000000000000 : ℝ)*(sp1) + (32502675047/100000000000000 : ℝ)*(sp2) + (470163304099627/10000000000000 : ℝ)*(sp4) + (470160183744409/10000000000000 : ℝ)*(sp5) + (4701598407733307/100000000000000 : ℝ)*(sp6) + (203182135854291/10000000000000 : ℝ)*(sp7) + (203182135854291/10000000000000 : ℝ)*(f.failure) + (470163304099627/10000000000000 : ℝ)*(f.sum) + (5802883631293/2625500000000000000000000000 : ℝ)*base65 + (98683794271106447/164093750000000000000000000000000 : ℝ)*base68 + (321015897912668947/164093750000000000000000000000000 : ℝ)*base70 + (2487932033177206053/164093750000000000000000000000000 : ℝ)*base71 + (18541034946021/2625500000000000000000000000 : ℝ)*base74 + (64017643889643553/164093750000000000000000000000000 : ℝ)*base75 + (2102769039620549803/164093750000000000000000000000000 : ℝ)*base77 + (487551957955487303/164093750000000000000000000000000 : ℝ)*base79 + (46840846266347/5251000000000000000000000000 : ℝ)*base82 + (1074439/1000000000000000000000 : ℝ)*base90 + (1074439/1000000000000000000000 : ℝ)*base92 + (1074439/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1541_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7767/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1541_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1541_s4_0 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-114123191/625000000 : ℝ)*x 0 + (1085949021/2000000000 : ℝ)*x 1 + (5218738673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114123191/625000000 : ℝ)^4579 ≤ (11188474882031/100000000000000 : ℝ)^3555 := by
    have hnat : (114123191 : ℕ)^4579*100000000000000^3555 ≤ 11188474882031^3555*625000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114123191 625000000 11188474882031 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085949021/2000000000 : ℝ)^4579 ≤ (45539051954611/100000000000000 : ℝ)^3555 := by
    have hnat : (1085949021 : ℕ)^4579*100000000000000^3555 ≤ 45539051954611^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085949021 2000000000 45539051954611 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218738673/10000000000 : ℝ)^4579 ≤ (1730898926067/4000000000000 : ℝ)^3555 := by
    have hnat : (5218738673 : ℕ)^4579*4000000000000^3555 ≤ 1730898926067^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218738673 10000000000 1730898926067 4000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114123191/625000000 : ℝ), (1085949021/2000000000 : ℝ), (5218738673/10000000000 : ℝ)] ![(11188474882031/100000000000000 : ℝ), (45539051954611/100000000000000 : ℝ), (1730898926067/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114123191/625000000 : ℝ)|^4579 ≤ (11188474882031/100000000000000 : ℝ)^3555
        have hw : |(-114123191/625000000 : ℝ)|=(114123191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085949021/2000000000 : ℝ)|^4579 ≤ (45539051954611/100000000000000 : ℝ)^3555
        have hw : |(1085949021/2000000000 : ℝ)|=(1085949021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218738673/10000000000 : ℝ)|^4579 ≤ (1730898926067/4000000000000 : ℝ)^3555
        have hw : |(5218738673/10000000000 : ℝ)|=(5218738673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_1 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675000431/5000000000 : ℝ)*x 0 + (-386796579/2000000000 : ℝ)*x 1 + (20385697/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675000431/5000000000 : ℝ)^4579 ≤ (2792463805551/6250000000000 : ℝ)^3555 := by
    have hnat : (2675000431 : ℕ)^4579*6250000000000^3555 ≤ 2792463805551^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675000431 5000000000 2792463805551 6250000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386796579/2000000000 : ℝ)^4579 ≤ (12048108531591/100000000000000 : ℝ)^3555 := by
    have hnat : (386796579 : ℕ)^4579*100000000000000^3555 ≤ 12048108531591^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386796579 2000000000 12048108531591 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20385697/39062500 : ℝ)^4579 ≤ (270452941111/625000000000 : ℝ)^3555 := by
    have hnat : (20385697 : ℕ)^4579*625000000000^3555 ≤ 270452941111^3555*39062500^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20385697 39062500 270452941111 625000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675000431/5000000000 : ℝ), (-386796579/2000000000 : ℝ), (20385697/39062500 : ℝ)] ![(2792463805551/6250000000000 : ℝ), (12048108531591/100000000000000 : ℝ), (270452941111/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675000431/5000000000 : ℝ)|^4579 ≤ (2792463805551/6250000000000 : ℝ)^3555
        have hw : |(2675000431/5000000000 : ℝ)|=(2675000431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-386796579/2000000000 : ℝ)|^4579 ≤ (12048108531591/100000000000000 : ℝ)^3555
        have hw : |(-386796579/2000000000 : ℝ)|=(386796579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20385697/39062500 : ℝ)|^4579 ≤ (270452941111/625000000000 : ℝ)^3555
        have hw : |(20385697/39062500 : ℝ)|=(20385697/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_2 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350000837/10000000000 : ℝ)*x 0 + (5218738541/10000000000 : ℝ)*x 1 + (-966991391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350000837/10000000000 : ℝ)^4579 ≤ (8935884123979/20000000000000 : ℝ)^3555 := by
    have hnat : (5350000837 : ℕ)^4579*20000000000000^3555 ≤ 8935884123979^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350000837 10000000000 8935884123979 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218738541/10000000000 : ℝ)^4579 ≤ (8654494348379/20000000000000 : ℝ)^3555 := by
    have hnat : (5218738541 : ℕ)^4579*20000000000000^3555 ≤ 8654494348379^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218738541 10000000000 8654494348379 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966991391/5000000000 : ℝ)^4579 ≤ (6024053812433/50000000000000 : ℝ)^3555 := by
    have hnat : (966991391 : ℕ)^4579*50000000000000^3555 ≤ 6024053812433^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966991391 5000000000 6024053812433 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350000837/10000000000 : ℝ), (5218738541/10000000000 : ℝ), (-966991391/5000000000 : ℝ)] ![(8935884123979/20000000000000 : ℝ), (8654494348379/20000000000000 : ℝ), (6024053812433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350000837/10000000000 : ℝ)|^4579 ≤ (8935884123979/20000000000000 : ℝ)^3555
        have hw : |(5350000837/10000000000 : ℝ)|=(5350000837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218738541/10000000000 : ℝ)|^4579 ≤ (8654494348379/20000000000000 : ℝ)^3555
        have hw : |(5218738541/10000000000 : ℝ)|=(5218738541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966991391/5000000000 : ℝ)|^4579 ≤ (6024053812433/50000000000000 : ℝ)^3555
        have hw : |(-966991391/5000000000 : ℝ)|=(966991391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_3 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (851286173/2000000000 : ℝ)*x 0 + (2009050537/5000000000 : ℝ)*x 1 + (901274051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851286173/2000000000 : ℝ)^4579 ≤ (4160102481611/12500000000000 : ℝ)^3555 := by
    have hnat : (851286173 : ℕ)^4579*12500000000000^3555 ≤ 4160102481611^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851286173 2000000000 4160102481611 12500000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009050537/5000000000 : ℝ)^4579 ≤ (6180036466589/20000000000000 : ℝ)^3555 := by
    have hnat : (2009050537 : ℕ)^4579*20000000000000^3555 ≤ 6180036466589^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009050537 5000000000 6180036466589 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901274051/2000000000 : ℝ)^4579 ≤ (35818997807771/100000000000000 : ℝ)^3555 := by
    have hnat : (901274051 : ℕ)^4579*100000000000000^3555 ≤ 35818997807771^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901274051 2000000000 35818997807771 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(851286173/2000000000 : ℝ), (2009050537/5000000000 : ℝ), (901274051/2000000000 : ℝ)] ![(4160102481611/12500000000000 : ℝ), (6180036466589/20000000000000 : ℝ), (35818997807771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(851286173/2000000000 : ℝ)|^4579 ≤ (4160102481611/12500000000000 : ℝ)^3555
        have hw : |(851286173/2000000000 : ℝ)|=(851286173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2009050537/5000000000 : ℝ)|^4579 ≤ (6180036466589/20000000000000 : ℝ)^3555
        have hw : |(2009050537/5000000000 : ℝ)|=(2009050537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901274051/2000000000 : ℝ)|^4579 ≤ (35818997807771/100000000000000 : ℝ)^3555
        have hw : |(901274051/2000000000 : ℝ)|=(901274051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_4 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-456499731/2500000000 : ℝ)*x 0 + (5219833591/10000000000 : ℝ)*x 1 + (5428642191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456499731/2500000000 : ℝ)^4579 ≤ (11188694827387/100000000000000 : ℝ)^3555 := by
    have hnat : (456499731 : ℕ)^4579*100000000000000^3555 ≤ 11188694827387^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456499731 2500000000 11188694827387 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219833591/10000000000 : ℝ)^4579 ≤ (43284167389529/100000000000000 : ℝ)^3555 := by
    have hnat : (5219833591 : ℕ)^4579*100000000000000^3555 ≤ 43284167389529^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219833591 10000000000 43284167389529 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428642191/10000000000 : ℝ)^4579 ≤ (22763568882263/50000000000000 : ℝ)^3555 := by
    have hnat : (5428642191 : ℕ)^4579*50000000000000^3555 ≤ 22763568882263^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428642191 10000000000 22763568882263 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456499731/2500000000 : ℝ), (5219833591/10000000000 : ℝ), (5428642191/10000000000 : ℝ)] ![(11188694827387/100000000000000 : ℝ), (43284167389529/100000000000000 : ℝ), (22763568882263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456499731/2500000000 : ℝ)|^4579 ≤ (11188694827387/100000000000000 : ℝ)^3555
        have hw : |(-456499731/2500000000 : ℝ)|=(456499731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219833591/10000000000 : ℝ)|^4579 ≤ (43284167389529/100000000000000 : ℝ)^3555
        have hw : |(5219833591/10000000000 : ℝ)|=(5219833591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428642191/10000000000 : ℝ)|^4579 ≤ (22763568882263/50000000000000 : ℝ)^3555
        have hw : |(5428642191/10000000000 : ℝ)|=(5428642191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_5 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294379381/10000000000 : ℝ)*x 0 + (-344815803/2000000000 : ℝ)*x 1 + (5428642191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294379381/10000000000 : ℝ)^4579 ≤ (22041003796129/50000000000000 : ℝ)^3555 := by
    have hnat : (5294379381 : ℕ)^4579*50000000000000^3555 ≤ 22041003796129^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294379381 10000000000 22041003796129 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344815803/2000000000 : ℝ)^4579 ≤ (5195427317633/50000000000000 : ℝ)^3555 := by
    have hnat : (344815803 : ℕ)^4579*50000000000000^3555 ≤ 5195427317633^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344815803 2000000000 5195427317633 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428642191/10000000000 : ℝ)^4579 ≤ (22763568882263/50000000000000 : ℝ)^3555 := by
    have hnat : (5428642191 : ℕ)^4579*50000000000000^3555 ≤ 22763568882263^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428642191 10000000000 22763568882263 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294379381/10000000000 : ℝ), (-344815803/2000000000 : ℝ), (5428642191/10000000000 : ℝ)] ![(22041003796129/50000000000000 : ℝ), (5195427317633/50000000000000 : ℝ), (22763568882263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294379381/10000000000 : ℝ)|^4579 ≤ (22041003796129/50000000000000 : ℝ)^3555
        have hw : |(5294379381/10000000000 : ℝ)|=(5294379381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344815803/2000000000 : ℝ)|^4579 ≤ (5195427317633/50000000000000 : ℝ)^3555
        have hw : |(-344815803/2000000000 : ℝ)|=(344815803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428642191/10000000000 : ℝ)|^4579 ≤ (22763568882263/50000000000000 : ℝ)^3555
        have hw : |(5428642191/10000000000 : ℝ)|=(5428642191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_6 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294379377/10000000000 : ℝ)*x 0 + (5428642191/10000000000 : ℝ)*x 1 + (-86203951/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294379377/10000000000 : ℝ)^4579 ≤ (551025094367/1250000000000 : ℝ)^3555 := by
    have hnat : (5294379377 : ℕ)^4579*1250000000000^3555 ≤ 551025094367^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294379377 10000000000 551025094367 1250000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428642191/10000000000 : ℝ)^4579 ≤ (22763568882263/50000000000000 : ℝ)^3555 := by
    have hnat : (5428642191 : ℕ)^4579*50000000000000^3555 ≤ 22763568882263^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428642191 10000000000 22763568882263 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86203951/500000000 : ℝ)^4579 ≤ (10390854674081/100000000000000 : ℝ)^3555 := by
    have hnat : (86203951 : ℕ)^4579*100000000000000^3555 ≤ 10390854674081^3555*500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86203951 500000000 10390854674081 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294379377/10000000000 : ℝ), (5428642191/10000000000 : ℝ), (-86203951/500000000 : ℝ)] ![(551025094367/1250000000000 : ℝ), (22763568882263/50000000000000 : ℝ), (10390854674081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294379377/10000000000 : ℝ)|^4579 ≤ (551025094367/1250000000000 : ℝ)^3555
        have hw : |(5294379377/10000000000 : ℝ)|=(5294379377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428642191/10000000000 : ℝ)|^4579 ≤ (22763568882263/50000000000000 : ℝ)^3555
        have hw : |(5428642191/10000000000 : ℝ)|=(5428642191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86203951/500000000 : ℝ)|^4579 ≤ (10390854674081/100000000000000 : ℝ)^3555
        have hw : |(-86203951/500000000 : ℝ)|=(86203951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s4_7 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2128247999/5000000000 : ℝ)*x 0 + (900767277/2000000000 : ℝ)*x 1 + (32165227/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128247999/5000000000 : ℝ)^4579 ≤ (33281475819161/100000000000000 : ℝ)^3555 := by
    have hnat : (2128247999 : ℕ)^4579*100000000000000^3555 ≤ 33281475819161^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128247999 5000000000 33281475819161 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900767277/2000000000 : ℝ)^4579 ≤ (4474132250019/12500000000000 : ℝ)^3555 := by
    have hnat : (900767277 : ℕ)^4579*12500000000000^3555 ≤ 4474132250019^3555*2000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900767277 2000000000 4474132250019 12500000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32165227/80000000 : ℝ)^4579 ≤ (7731366540377/25000000000000 : ℝ)^3555 := by
    have hnat : (32165227 : ℕ)^4579*25000000000000^3555 ≤ 7731366540377^3555*80000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32165227 80000000 7731366540377 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128247999/5000000000 : ℝ), (900767277/2000000000 : ℝ), (32165227/80000000 : ℝ)] ![(33281475819161/100000000000000 : ℝ), (4474132250019/12500000000000 : ℝ), (7731366540377/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128247999/5000000000 : ℝ)|^4579 ≤ (33281475819161/100000000000000 : ℝ)^3555
        have hw : |(2128247999/5000000000 : ℝ)|=(2128247999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900767277/2000000000 : ℝ)|^4579 ≤ (4474132250019/12500000000000 : ℝ)^3555
        have hw : |(900767277/2000000000 : ℝ)|=(900767277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32165227/80000000 : ℝ)|^4579 ≤ (7731366540377/25000000000000 : ℝ)^3555
        have hw : |(32165227/80000000 : ℝ)|=(32165227/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1541_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7767/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5509/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7767/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7767/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7767/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7767/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7767/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7767/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5489/50000 : ℝ) ^ (4577/1024 : ℝ) ≤ (2572593591683313/50000000000000000000 : ℝ) := by
    have hpowers : (5489/50000 : ℝ)^4577 ≤ (2572593591683313/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5489 : ℕ)^4577*50000000000000000000^1024 ≤ 2572593591683313^1024*50000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5489 50000 2572593591683313 50000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5489/50000 : ℝ)) (X := (2572593591683313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7767/50000 : ℝ) ^ (4577/1024 : ℝ) ≤ (151753076904781/625000000000000000 : ℝ) := by
    have hpowers : (7767/50000 : ℝ)^4577 ≤ (151753076904781/625000000000000000 : ℝ)^1024 := by
      have hnat : (7767 : ℕ)^4577*625000000000000000^1024 ≤ 151753076904781^1024*50000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7767 50000 151753076904781 625000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7767/50000 : ℝ)) (X := (151753076904781/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002572593591683313/25000000000000000000 : ℝ) ≤ (10000230214605823/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (25002572593591683313/25000000000000000000 : ℝ)^1024 ≤ (10000230214605823/10000000000000000 : ℝ)^4577 := by
      have hnat : (25002572593591683313 : ℕ)^1024*10000000000000000^4577 ≤ 10000230214605823^4577*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002572593591683313 25000000000000000000 10000230214605823 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000230214605823/10000000000000000 : ℝ)) (X := (25002572593591683313/25000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014712839744065793/50000000000000000000 : ℝ) ≤ (2000131651540217/2000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (50014712839744065793/50000000000000000000 : ℝ)^1024 ≤ (2000131651540217/2000000000000000 : ℝ)^4577 := by
      have hnat : (50014712839744065793 : ℕ)^1024*2000000000000000^4577 ≤ 2000131651540217^4577*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014712839744065793 50000000000000000000 2000131651540217 2000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000131651540217/2000000000000000 : ℝ)) (X := (50014712839744065793/50000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312651753076904781/312500000000000000 : ℝ) ≤ (10001086300796347/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (312651753076904781/312500000000000000 : ℝ)^1024 ≤ (10001086300796347/10000000000000000 : ℝ)^4577 := by
      have hnat : (312651753076904781 : ℕ)^1024*10000000000000000^4577 ≤ 10001086300796347^4577*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312651753076904781 312500000000000000 10001086300796347 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001086300796347/10000000000000000 : ℝ)) (X := (312651753076904781/312500000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2572593591683313/50000000000000000000 : ℝ) ≤ ((11387912685886139279/11390000000000000000 : ℝ)+2*(214021547631/227800000000000 : ℝ)*(5489/50000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (11387912685886139279/11390000000000000000 : ℝ)+2*(214021547631/227800000000000 : ℝ)*(5489/50000 : ℝ)=(10000230214605823/10000000000000000 : ℝ) by norm_num, show 1+2*(2572593591683313/50000000000000000000 : ℝ)=(25002572593591683313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(151753076904781/625000000000000000 : ℝ)+(2572593591683313/50000000000000000000 : ℝ) ≤ ((11387912685886139279/11390000000000000000 : ℝ)+(214021547631/227800000000000 : ℝ)*((7767/50000 : ℝ)+(5489/50000 : ℝ)))^(4577/1024 : ℝ) := by
    rw [show (11387912685886139279/11390000000000000000 : ℝ)+(214021547631/227800000000000 : ℝ)*((7767/50000 : ℝ)+(5489/50000 : ℝ))=(2000131651540217/2000000000000000 : ℝ) by norm_num, show 1+(151753076904781/625000000000000000 : ℝ)+(2572593591683313/50000000000000000000 : ℝ)=(50014712839744065793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(151753076904781/625000000000000000 : ℝ) ≤ ((11387912685886139279/11390000000000000000 : ℝ)+2*(214021547631/227800000000000 : ℝ)*(7767/50000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (11387912685886139279/11390000000000000000 : ℝ)+2*(214021547631/227800000000000 : ℝ)*(7767/50000 : ℝ)=(10001086300796347/10000000000000000 : ℝ) by norm_num, show 1+2*(151753076904781/625000000000000000 : ℝ)=(312651753076904781/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11387912685886139279/11390000000000000000 : ℝ)*(X 1 0+X 2 0)+(214021547631/227800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (7767/50000 : ℝ)) (c := (11387912685886139279/11390000000000000000 : ℝ)) (alpha := (214021547631/227800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11387912685886139279/11390000000000000000 : ℝ)*(X 0 1+X 2 1)+(214021547631/227800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (7767/50000 : ℝ)) (c := (11387912685886139279/11390000000000000000 : ℝ)) (alpha := (214021547631/227800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11387912685886139279/11390000000000000000 : ℝ)*(X 0 2+X 1 2)+(214021547631/227800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (7767/50000 : ℝ)) (c := (11387912685886139279/11390000000000000000 : ℝ)) (alpha := (214021547631/227800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-114123191/625000000 : ℝ)*X 0 0+(1085949021/2000000000 : ℝ)*X 0 1+(5218738673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675000431/5000000000 : ℝ)*X 1 0+(-386796579/2000000000 : ℝ)*X 1 1+(20385697/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350000837/10000000000 : ℝ)*X 2 0+(5218738541/10000000000 : ℝ)*X 2 1+(-966991391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((851286173/2000000000 : ℝ)*X 0 0+(2009050537/5000000000 : ℝ)*X 0 1+(901274051/2000000000 : ℝ)*X 0 2+(851286173/2000000000 : ℝ)*X 1 0+(2009050537/5000000000 : ℝ)*X 1 1+(901274051/2000000000 : ℝ)*X 1 2+(851286173/2000000000 : ℝ)*X 2 0+(2009050537/5000000000 : ℝ)*X 2 1+(901274051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-456499731/2500000000 : ℝ)*X 0 0+(5219833591/10000000000 : ℝ)*X 0 1+(5428642191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294379381/10000000000 : ℝ)*X 1 0+(-344815803/2000000000 : ℝ)*X 1 1+(5428642191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294379377/10000000000 : ℝ)*X 2 0+(5428642191/10000000000 : ℝ)*X 2 1+(-86203951/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2128247999/5000000000 : ℝ)*X 0 0+(900767277/2000000000 : ℝ)*X 0 1+(32165227/80000000 : ℝ)*X 0 2+(2128247999/5000000000 : ℝ)*X 1 0+(900767277/2000000000 : ℝ)*X 1 1+(32165227/80000000 : ℝ)*X 1 2+(2128247999/5000000000 : ℝ)*X 2 0+(900767277/2000000000 : ℝ)*X 2 1+(32165227/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1365118903305124094831717289/142375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761612757/50000000000000 : ℝ)*(base19) + (685335249/50000000000000 : ℝ)*(base23) + (381677/200000000000 : ℝ)*(upper3) + (34884437/50000000000000 : ℝ)*(upper4) + (206944811/100000000000000 : ℝ)*(upper5) + (848412472853397/25000000000000 : ℝ)*(major0) + (848412472853397/25000000000000 : ℝ)*(major1) + (848412472853397/25000000000000 : ℝ)*(major2) + (2369605103862589/50000000000000 : ℝ)*(sp0) + (4739228848049783/100000000000000 : ℝ)*(sp1) + (4739229000604799/100000000000000 : ℝ)*(sp2) + (512014931752621/25000000000000 : ℝ)*(sp3) + (20163550119/100000000000000 : ℝ)*(sp4) + (374597399/4000000000000 : ℝ)*(sp7) + (2048069091945459/100000000000000 : ℝ)*(f.failure) + (4739230371275297/100000000000000 : ℝ)*(f.sum) + (2415724347657/711875000000000000000000000 : ℝ)*base66 + (384236855618130763/284750000000000000000000000000000 : ℝ)*base67 + (549514592072369237/284750000000000000000000000000000 : ℝ)*base70 + (564010670130369237/284750000000000000000000000000000 : ℝ)*base72 + (2637736551961/1423750000000000000000000000 : ℝ)*base73 + (3818413519205880763/284750000000000000000000000000000 : ℝ)*base75 + (1158370432021119237/284750000000000000000000000000000 : ℝ)*base78 + (598679493471869237/284750000000000000000000000000000 : ℝ)*base80 + (19069471277249/5695000000000000000000000000 : ℝ)*base81 + (89881689/10000000000000000000000 : ℝ)*base89 + (89881689/10000000000000000000000 : ℝ)*base91 + (89881689/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2227908935324487191251660239/284750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1253836869/100000000000000 : ℝ)*(base19) + (341225141/25000000000000 : ℝ)*(base23) + (1633697/1000000000000 : ℝ)*(upper3) + (5193491/10000000000000 : ℝ)*(lower4) + (6323597/4000000000000 : ℝ)*(upper5) + (1714670726873751/50000000000000 : ℝ)*(major0) + (1714670726873751/50000000000000 : ℝ)*(major1) + (1714670726873751/50000000000000 : ℝ)*(major2) + (4880855851/25000000000000 : ℝ)*(sp1) + (10551163637/50000000000000 : ℝ)*(sp2) + (119726842058459/2500000000000 : ℝ)*(sp4) + (4789052905078087/100000000000000 : ℝ)*(sp5) + (4789051215110521/100000000000000 : ℝ)*(sp6) + (129350560272107/6250000000000 : ℝ)*(sp7) + (129350560272107/6250000000000 : ℝ)*(f.failure) + (119726842058459/2500000000000 : ℝ)*(f.sum) + (27337509098361/5695000000000000000000000000 : ℝ)*base65 + (7405160612669215529/569500000000000000000000000000000 : ℝ)*base67 + (4505230802509215529/569500000000000000000000000000000 : ℝ)*base69 + (4391434331344715529/569500000000000000000000000000000 : ℝ)*base71 + (10275335713889/1423750000000000000000000000 : ℝ)*base73 + (3783626245251715529/569500000000000000000000000000000 : ℝ)*base75 + (6038795453824715529/569500000000000000000000000000000 : ℝ)*base77 + (9858562065211715529/569500000000000000000000000000000 : ℝ)*base79 + (6511818982959/5695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5491103/625000000000000000000 : ℝ)*base90 + (5491103/625000000000000000000 : ℝ)*base92 + (5491103/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1541_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7767/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1541_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1541_s5_0 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1826007043/10000000000 : ℝ)*x 0 + (5429511327/10000000000 : ℝ)*x 1 + (2609474269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826007043/10000000000 : ℝ)^4579 ≤ (11188758905951/100000000000000 : ℝ)^3555 := by
    have hnat : (1826007043 : ℕ)^4579*100000000000000^3555 ≤ 11188758905951^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826007043 10000000000 11188758905951 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429511327/10000000000 : ℝ)^4579 ≤ (45536526517681/100000000000000 : ℝ)^3555 := by
    have hnat : (5429511327 : ℕ)^4579*100000000000000^3555 ≤ 45536526517681^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429511327 10000000000 45536526517681 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609474269/5000000000 : ℝ)^4579 ≤ (21637357276789/50000000000000 : ℝ)^3555 := by
    have hnat : (2609474269 : ℕ)^4579*50000000000000^3555 ≤ 21637357276789^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609474269 5000000000 21637357276789 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1826007043/10000000000 : ℝ), (5429511327/10000000000 : ℝ), (2609474269/5000000000 : ℝ)] ![(11188758905951/100000000000000 : ℝ), (45536526517681/100000000000000 : ℝ), (21637357276789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1826007043/10000000000 : ℝ)|^4579 ≤ (11188758905951/100000000000000 : ℝ)^3555
        have hw : |(-1826007043/10000000000 : ℝ)|=(1826007043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429511327/10000000000 : ℝ)|^4579 ≤ (45536526517681/100000000000000 : ℝ)^3555
        have hw : |(5429511327/10000000000 : ℝ)|=(5429511327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609474269/5000000000 : ℝ)|^4579 ≤ (21637357276789/50000000000000 : ℝ)^3555
        have hw : |(2609474269/5000000000 : ℝ)|=(2609474269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_1 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349938857/10000000000 : ℝ)*x 0 + (-241723291/1250000000 : ℝ)*x 1 + (65236857/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349938857/10000000000 : ℝ)^4579 ≤ (8935750782409/20000000000000 : ℝ)^3555 := by
    have hnat : (5349938857 : ℕ)^4579*20000000000000^3555 ≤ 8935750782409^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349938857 10000000000 8935750782409 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241723291/1250000000 : ℝ)^4579 ≤ (12046531277971/100000000000000 : ℝ)^3555 := by
    have hnat : (241723291 : ℕ)^4579*100000000000000^3555 ≤ 12046531277971^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241723291 1250000000 12046531277971 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65236857/125000000 : ℝ)^4579 ≤ (676167418571/1562500000000 : ℝ)^3555 := by
    have hnat : (65236857 : ℕ)^4579*1562500000000^3555 ≤ 676167418571^3555*125000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65236857 125000000 676167418571 1562500000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349938857/10000000000 : ℝ), (-241723291/1250000000 : ℝ), (65236857/125000000 : ℝ)] ![(8935750782409/20000000000000 : ℝ), (12046531277971/100000000000000 : ℝ), (676167418571/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349938857/10000000000 : ℝ)|^4579 ≤ (8935750782409/20000000000000 : ℝ)^3555
        have hw : |(5349938857/10000000000 : ℝ)|=(5349938857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-241723291/1250000000 : ℝ)|^4579 ≤ (12046531277971/100000000000000 : ℝ)^3555
        have hw : |(-241723291/1250000000 : ℝ)|=(241723291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65236857/125000000 : ℝ)|^4579 ≤ (676167418571/1562500000000 : ℝ)^3555
        have hw : |(65236857/125000000 : ℝ)|=(65236857/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_2 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349938881/10000000000 : ℝ)*x 0 + (32618429/62500000 : ℝ)*x 1 + (-193378619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349938881/10000000000 : ℝ)^4579 ≤ (44678754170209/100000000000000 : ℝ)^3555 := by
    have hnat : (5349938881 : ℕ)^4579*100000000000000^3555 ≤ 44678754170209^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349938881 10000000000 44678754170209 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32618429/62500000 : ℝ)^4579 ≤ (8654943128593/20000000000000 : ℝ)^3555 := by
    have hnat : (32618429 : ℕ)^4579*20000000000000^3555 ≤ 8654943128593^3555*62500000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32618429 62500000 8654943128593 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193378619/1000000000 : ℝ)^4579 ≤ (481861206827/4000000000000 : ℝ)^3555 := by
    have hnat : (193378619 : ℕ)^4579*4000000000000^3555 ≤ 481861206827^3555*1000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193378619 1000000000 481861206827 4000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349938881/10000000000 : ℝ), (32618429/62500000 : ℝ), (-193378619/1000000000 : ℝ)] ![(44678754170209/100000000000000 : ℝ), (8654943128593/20000000000000 : ℝ), (481861206827/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349938881/10000000000 : ℝ)|^4579 ≤ (44678754170209/100000000000000 : ℝ)^3555
        have hw : |(5349938881/10000000000 : ℝ)|=(5349938881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32618429/62500000 : ℝ)|^4579 ≤ (8654943128593/20000000000000 : ℝ)^3555
        have hw : |(32618429/62500000 : ℝ)|=(32618429/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-193378619/1000000000 : ℝ)|^4579 ≤ (481861206827/4000000000000 : ℝ)^3555
        have hw : |(-193378619/1000000000 : ℝ)|=(193378619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_3 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (532056657/1250000000 : ℝ)*x 0 + (1004653033/2500000000 : ℝ)*x 1 + (4505853759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532056657/1250000000 : ℝ)^4579 ≤ (3328104535639/10000000000000 : ℝ)^3555 := by
    have hnat : (532056657 : ℕ)^4579*10000000000000^3555 ≤ 3328104535639^3555*1250000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532056657 1250000000 3328104535639 10000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004653033/2500000000 : ℝ)^4579 ≤ (1236209786013/4000000000000 : ℝ)^3555 := by
    have hnat : (1004653033 : ℕ)^4579*4000000000000^3555 ≤ 1236209786013^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004653033 2500000000 1236209786013 4000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505853759/10000000000 : ℝ)^4579 ≤ (17906854989457/50000000000000 : ℝ)^3555 := by
    have hnat : (4505853759 : ℕ)^4579*50000000000000^3555 ≤ 17906854989457^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505853759 10000000000 17906854989457 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532056657/1250000000 : ℝ), (1004653033/2500000000 : ℝ), (4505853759/10000000000 : ℝ)] ![(3328104535639/10000000000000 : ℝ), (1236209786013/4000000000000 : ℝ), (17906854989457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532056657/1250000000 : ℝ)|^4579 ≤ (3328104535639/10000000000000 : ℝ)^3555
        have hw : |(532056657/1250000000 : ℝ)|=(532056657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004653033/2500000000 : ℝ)|^4579 ≤ (1236209786013/4000000000000 : ℝ)^3555
        have hw : |(1004653033/2500000000 : ℝ)|=(1004653033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505853759/10000000000 : ℝ)|^4579 ≤ (17906854989457/50000000000000 : ℝ)^3555
        have hw : |(4505853759/10000000000 : ℝ)|=(4505853759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_4 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14265901/78125000 : ℝ)*x 0 + (5220038917/10000000000 : ℝ)*x 1 + (1357103143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14265901/78125000 : ℝ)^4579 ≤ (349655691991/3125000000000 : ℝ)^3555 := by
    have hnat : (14265901 : ℕ)^4579*3125000000000^3555 ≤ 349655691991^3555*78125000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14265901 78125000 349655691991 3125000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220038917/10000000000 : ℝ)^4579 ≤ (21643180223103/50000000000000 : ℝ)^3555 := by
    have hnat : (5220038917 : ℕ)^4579*50000000000000^3555 ≤ 21643180223103^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220038917 10000000000 21643180223103 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357103143/2500000000 : ℝ)^4579 ≤ (45524657400957/100000000000000 : ℝ)^3555 := by
    have hnat : (1357103143 : ℕ)^4579*100000000000000^3555 ≤ 45524657400957^3555*2500000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357103143 2500000000 45524657400957 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14265901/78125000 : ℝ), (5220038917/10000000000 : ℝ), (1357103143/2500000000 : ℝ)] ![(349655691991/3125000000000 : ℝ), (21643180223103/50000000000000 : ℝ), (45524657400957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14265901/78125000 : ℝ)|^4579 ≤ (349655691991/3125000000000 : ℝ)^3555
        have hw : |(-14265901/78125000 : ℝ)|=(14265901/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220038917/10000000000 : ℝ)|^4579 ≤ (21643180223103/50000000000000 : ℝ)^3555
        have hw : |(5220038917/10000000000 : ℝ)|=(5220038917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357103143/2500000000 : ℝ)|^4579 ≤ (45524657400957/100000000000000 : ℝ)^3555
        have hw : |(1357103143/2500000000 : ℝ)|=(1357103143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_5 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294434363/10000000000 : ℝ)*x 0 + (-107770149/625000000 : ℝ)*x 1 + (2714206351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294434363/10000000000 : ℝ)^4579 ≤ (22041298623997/50000000000000 : ℝ)^3555 := by
    have hnat : (5294434363 : ℕ)^4579*50000000000000^3555 ≤ 22041298623997^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294434363 10000000000 22041298623997 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107770149/625000000 : ℝ)^4579 ≤ (10392743927887/100000000000000 : ℝ)^3555 := by
    have hnat : (107770149 : ℕ)^4579*100000000000000^3555 ≤ 10392743927887^3555*625000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107770149 625000000 10392743927887 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714206351/5000000000 : ℝ)^4579 ≤ (45524658805219/100000000000000 : ℝ)^3555 := by
    have hnat : (2714206351 : ℕ)^4579*100000000000000^3555 ≤ 45524658805219^3555*5000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714206351 5000000000 45524658805219 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294434363/10000000000 : ℝ), (-107770149/625000000 : ℝ), (2714206351/5000000000 : ℝ)] ![(22041298623997/50000000000000 : ℝ), (10392743927887/100000000000000 : ℝ), (45524658805219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294434363/10000000000 : ℝ)|^4579 ≤ (22041298623997/50000000000000 : ℝ)^3555
        have hw : |(5294434363/10000000000 : ℝ)|=(5294434363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107770149/625000000 : ℝ)|^4579 ≤ (10392743927887/100000000000000 : ℝ)^3555
        have hw : |(-107770149/625000000 : ℝ)|=(107770149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714206351/5000000000 : ℝ)|^4579 ≤ (45524658805219/100000000000000 : ℝ)^3555
        have hw : |(2714206351/5000000000 : ℝ)|=(2714206351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_6 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294434469/10000000000 : ℝ)*x 0 + (5428412763/10000000000 : ℝ)*x 1 + (-1724322153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294434469/10000000000 : ℝ)^4579 ≤ (8816519676959/20000000000000 : ℝ)^3555 := by
    have hnat : (5294434469 : ℕ)^4579*20000000000000^3555 ≤ 8816519676959^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294434469 10000000000 8816519676959 20000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428412763/10000000000 : ℝ)^4579 ≤ (22762329732071/50000000000000 : ℝ)^3555 := by
    have hnat : (5428412763 : ℕ)^4579*50000000000000^3555 ≤ 22762329732071^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428412763 10000000000 22762329732071 50000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724322153/10000000000 : ℝ)^4579 ≤ (519637106729/5000000000000 : ℝ)^3555 := by
    have hnat : (1724322153 : ℕ)^4579*5000000000000^3555 ≤ 519637106729^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724322153 10000000000 519637106729 5000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294434469/10000000000 : ℝ), (5428412763/10000000000 : ℝ), (-1724322153/10000000000 : ℝ)] ![(8816519676959/20000000000000 : ℝ), (22762329732071/50000000000000 : ℝ), (519637106729/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294434469/10000000000 : ℝ)|^4579 ≤ (8816519676959/20000000000000 : ℝ)^3555
        have hw : |(5294434469/10000000000 : ℝ)|=(5294434469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428412763/10000000000 : ℝ)|^4579 ≤ (22762329732071/50000000000000 : ℝ)^3555
        have hw : |(5428412763/10000000000 : ℝ)|=(5428412763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1724322153/10000000000 : ℝ)|^4579 ≤ (519637106729/5000000000000 : ℝ)^3555
        have hw : |(-1724322153/10000000000 : ℝ)|=(1724322153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1541_s5_7 (p : ℝ) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4256517457/10000000000 : ℝ)*x 0 + (281458167/625000000 : ℝ)*x 1 + (4021154061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256517457/10000000000 : ℝ)^4579 ≤ (33281691937281/100000000000000 : ℝ)^3555 := by
    have hnat : (4256517457 : ℕ)^4579*100000000000000^3555 ≤ 33281691937281^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256517457 10000000000 33281691937281 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281458167/625000000 : ℝ)^4579 ≤ (35787881403443/100000000000000 : ℝ)^3555 := by
    have hnat : (281458167 : ℕ)^4579*100000000000000^3555 ≤ 35787881403443^3555*625000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281458167 625000000 35787881403443 100000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021154061/10000000000 : ℝ)^4579 ≤ (7732606660929/25000000000000 : ℝ)^3555 := by
    have hnat : (4021154061 : ℕ)^4579*25000000000000^3555 ≤ 7732606660929^3555*10000000000^4579 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021154061 10000000000 7732606660929 25000000000000 4579 3555 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4579/1024 : ℝ)) 4579 3555 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256517457/10000000000 : ℝ), (281458167/625000000 : ℝ), (4021154061/10000000000 : ℝ)] ![(33281691937281/100000000000000 : ℝ), (35787881403443/100000000000000 : ℝ), (7732606660929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256517457/10000000000 : ℝ)|^4579 ≤ (33281691937281/100000000000000 : ℝ)^3555
        have hw : |(4256517457/10000000000 : ℝ)|=(4256517457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281458167/625000000 : ℝ)|^4579 ≤ (35787881403443/100000000000000 : ℝ)^3555
        have hw : |(281458167/625000000 : ℝ)|=(281458167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021154061/10000000000 : ℝ)|^4579 ≤ (7732606660929/25000000000000 : ℝ)^3555
        have hw : |(4021154061/10000000000 : ℝ)|=(4021154061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1541_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11023/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5509/50000 : ℝ) ^ (4577/1024 : ℝ) ≤ (5229513616609201/100000000000000000000 : ℝ) := by
    have hpowers : (5509/50000 : ℝ)^4577 ≤ (5229513616609201/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5509 : ℕ)^4577*100000000000000000000^1024 ≤ 5229513616609201^1024*50000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5509 50000 5229513616609201 100000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5509/50000 : ℝ)) (X := (5229513616609201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4577/1024 : ℝ) ≤ (5993649140286277/25000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4577 ≤ (5993649140286277/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4577*25000000000000000000^1024 ≤ 5993649140286277^1024*10000^4577 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 5993649140286277 25000000000000000000 4577 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (5993649140286277/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005229513616609201/50000000000000000000 : ℝ) ≤ (10000233987527561/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (50005229513616609201/50000000000000000000 : ℝ)^1024 ≤ (10000233987527561/10000000000000000 : ℝ)^4577 := by
      have hnat : (50005229513616609201 : ℕ)^1024*10000000000000000^4577 ≤ 10000233987527561^4577*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005229513616609201 50000000000000000000 10000233987527561 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000233987527561/10000000000000000 : ℝ)) (X := (50005229513616609201/50000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029204110177754309/100000000000000000000 : ℝ) ≤ (625040831357361/625000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (100029204110177754309/100000000000000000000 : ℝ)^1024 ≤ (625040831357361/625000000000000 : ℝ)^4577 := by
      have hnat : (100029204110177754309 : ℕ)^1024*625000000000000^4577 ≤ 625040831357361^4577*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029204110177754309 100000000000000000000 625040831357361 625000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625040831357361/625000000000000 : ℝ)) (X := (100029204110177754309/100000000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505993649140286277/12500000000000000000 : ℝ) ≤ (10001072615907991/10000000000000000 : ℝ) ^ (4577/1024 : ℝ) := by
    have hpowers : (12505993649140286277/12500000000000000000 : ℝ)^1024 ≤ (10001072615907991/10000000000000000 : ℝ)^4577 := by
      have hnat : (12505993649140286277 : ℕ)^1024*10000000000000000^4577 ≤ 10001072615907991^4577*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505993649140286277 12500000000000000000 10001072615907991 10000000000000000 1024 4577 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072615907991/10000000000000000 : ℝ)) (X := (12505993649140286277/12500000000000000000 : ℝ)) (by norm_num) 4577 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5229513616609201/100000000000000000000 : ℝ) ≤ ((11177951596181918763/11180000000000000000 : ℝ)+2*(83862838043/89440000000000 : ℝ)*(5509/50000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (11177951596181918763/11180000000000000000 : ℝ)+2*(83862838043/89440000000000 : ℝ)*(5509/50000 : ℝ)=(10000233987527561/10000000000000000 : ℝ) by norm_num, show 1+2*(5229513616609201/100000000000000000000 : ℝ)=(50005229513616609201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5993649140286277/25000000000000000000 : ℝ)+(5229513616609201/100000000000000000000 : ℝ) ≤ ((11177951596181918763/11180000000000000000 : ℝ)+(83862838043/89440000000000 : ℝ)*((1549/10000 : ℝ)+(5509/50000 : ℝ)))^(4577/1024 : ℝ) := by
    rw [show (11177951596181918763/11180000000000000000 : ℝ)+(83862838043/89440000000000 : ℝ)*((1549/10000 : ℝ)+(5509/50000 : ℝ))=(625040831357361/625000000000000 : ℝ) by norm_num, show 1+(5993649140286277/25000000000000000000 : ℝ)+(5229513616609201/100000000000000000000 : ℝ)=(100029204110177754309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5993649140286277/25000000000000000000 : ℝ) ≤ ((11177951596181918763/11180000000000000000 : ℝ)+2*(83862838043/89440000000000 : ℝ)*(1549/10000 : ℝ))^(4577/1024 : ℝ) := by
    rw [show (11177951596181918763/11180000000000000000 : ℝ)+2*(83862838043/89440000000000 : ℝ)*(1549/10000 : ℝ)=(10001072615907991/10000000000000000 : ℝ) by norm_num, show 1+2*(5993649140286277/25000000000000000000 : ℝ)=(12505993649140286277/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11177951596181918763/11180000000000000000 : ℝ)*(X 1 0+X 2 0)+(83862838043/89440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11177951596181918763/11180000000000000000 : ℝ)) (alpha := (83862838043/89440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11177951596181918763/11180000000000000000 : ℝ)*(X 0 1+X 2 1)+(83862838043/89440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11177951596181918763/11180000000000000000 : ℝ)) (alpha := (83862838043/89440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11177951596181918763/11180000000000000000 : ℝ)*(X 0 2+X 1 2)+(83862838043/89440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4577/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11177951596181918763/11180000000000000000 : ℝ)) (alpha := (83862838043/89440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1826007043/10000000000 : ℝ)*X 0 0+(5429511327/10000000000 : ℝ)*X 0 1+(2609474269/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349938857/10000000000 : ℝ)*X 1 0+(-241723291/1250000000 : ℝ)*X 1 1+(65236857/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349938881/10000000000 : ℝ)*X 2 0+(32618429/62500000 : ℝ)*X 2 1+(-193378619/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((532056657/1250000000 : ℝ)*X 0 0+(1004653033/2500000000 : ℝ)*X 0 1+(4505853759/10000000000 : ℝ)*X 0 2+(532056657/1250000000 : ℝ)*X 1 0+(1004653033/2500000000 : ℝ)*X 1 1+(4505853759/10000000000 : ℝ)*X 1 2+(532056657/1250000000 : ℝ)*X 2 0+(1004653033/2500000000 : ℝ)*X 2 1+(4505853759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-14265901/78125000 : ℝ)*X 0 0+(5220038917/10000000000 : ℝ)*X 0 1+(1357103143/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294434363/10000000000 : ℝ)*X 1 0+(-107770149/625000000 : ℝ)*X 1 1+(2714206351/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294434469/10000000000 : ℝ)*X 2 0+(5428412763/10000000000 : ℝ)*X 2 1+(-1724322153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256517457/10000000000 : ℝ)*X 0 0+(281458167/625000000 : ℝ)*X 0 1+(4021154061/10000000000 : ℝ)*X 0 2+(4256517457/10000000000 : ℝ)*X 1 0+(281458167/625000000 : ℝ)*X 1 1+(4021154061/10000000000 : ℝ)*X 1 2+(4256517457/10000000000 : ℝ)*X 2 0+(281458167/625000000 : ℝ)*X 2 1+(4021154061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1541_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (577659747386130524464954503/139750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48220351/6250000000000 : ℝ)*(base19) + (547797963/100000000000000 : ℝ)*(base23) + (131091013/100000000000000 : ℝ)*(lower2) + (350209/390625000000 : ℝ)*(upper3) + (51488481/100000000000000 : ℝ)*(upper5) + (1700395556680173/50000000000000 : ℝ)*(major0) + (1700395556680173/50000000000000 : ℝ)*(major1) + (1700395556680173/50000000000000 : ℝ)*(major2) + (237459471888313/5000000000000 : ℝ)*(sp0) + (474920249511153/10000000000000 : ℝ)*(sp1) + (4749202718839183/100000000000000 : ℝ)*(sp2) + (256546707942403/12500000000000 : ℝ)*(sp3) + (6914435443/50000000000000 : ℝ)*(sp4) + (1031752047/20000000000000 : ℝ)*(sp7) + (102618941114973/5000000000000 : ℝ)*(f.failure) + (2374601633318573/50000000000000 : ℝ)*(f.sum) + (5006329084997/2236000000000000000000000000 : ℝ)*base66 + (10017863936908660999/559000000000000000000000000000000 : ℝ)*base67 + (2799484050281660999/559000000000000000000000000000000 : ℝ)*base69 + (3884870354647660999/559000000000000000000000000000000 : ℝ)*base71 + (8978675456511/2236000000000000000000000000 : ℝ)*base73 + (1556797431270339001/559000000000000000000000000000000 : ℝ)*base76 + (4207830920380660999/559000000000000000000000000000000 : ℝ)*base77 + (8251500163266660999/559000000000000000000000000000000 : ℝ)*base79 + (841663658323/2236000000000000000000000000 : ℝ)*base81 + (3765783/500000000000000000000 : ℝ)*base89 + (3765783/500000000000000000000 : ℝ)*base91 + (3765783/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1766137029725474128465916241/279500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (988284049/100000000000000 : ℝ)*(base19) + (697646317/50000000000000 : ℝ)*(base23) + (77459909/25000000000000 : ℝ)*(lower1) + (113827083/100000000000000 : ℝ)*(upper2) + (204350761/100000000000000 : ℝ)*(upper3) + (198903737/100000000000000 : ℝ)*(upper5) + (1718244365406923/50000000000000 : ℝ)*(major0) + (1718244365406923/50000000000000 : ℝ)*(major1) + (1718244365406923/50000000000000 : ℝ)*(major2) + (9150799411/100000000000000 : ℝ)*(sp2) + (959810980404459/20000000000000 : ℝ)*(sp4) + (2399526956869123/50000000000000 : ℝ)*(sp5) + (4799044355930251/100000000000000 : ℝ)*(sp6) + (2073922348974851/100000000000000 : ℝ)*(sp7) + (2073922348974851/100000000000000 : ℝ)*(f.failure) + (959810980404459/20000000000000 : ℝ)*(f.sum) + (5793485653003/2236000000000000000000000000 : ℝ)*base66 + (4539413520448078751/559000000000000000000000000000000 : ℝ)*base68 + (22016117120024078751/559000000000000000000000000000000 : ℝ)*base70 + (18701710078751/559000000000000000000000000000000 : ℝ)*base72 + (9255697456599/2236000000000000000000000000 : ℝ)*base74 + (6636522265192078751/559000000000000000000000000000000 : ℝ)*base76 + (5134586594918078751/559000000000000000000000000000000 : ℝ)*base78 + (3597940151690078751/559000000000000000000000000000000 : ℝ)*base80 + (37297829622959/2236000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (90429321/10000000000000000000000 : ℝ)*base89 + (90429321/10000000000000000000000 : ℝ)*base91 + (90429321/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1541_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1541_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1541_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1541_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1541_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1541_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4577/1024 : ℝ) ≤ p) (hpb : p ≤ (4579/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (165699971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1987/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1541_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

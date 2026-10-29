-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1574_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:31.784076+00:00
-- url     : https://prove2.me/submissions/d543924b-15f5-4978-959d-76f29e3acb14

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
theorem support_rectangle_w1574_s0_0 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1622004289/10000000000 : ℝ)*x 0 + (2933330437/5000000000 : ℝ)*x 1 + (4880952673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1622004289/10000000000 : ℝ)^4645 ≤ (9697478038253/100000000000000 : ℝ)^3621 := by
    have hnat : (1622004289 : ℕ)^4645*100000000000000^3621 ≤ 9697478038253^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1622004289 10000000000 9697478038253 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2933330437/5000000000 : ℝ)^4645 ≤ (50453715868699/100000000000000 : ℝ)^3621 := by
    have hnat : (2933330437 : ℕ)^4645*100000000000000^3621 ≤ 50453715868699^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933330437 5000000000 50453715868699 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880952673/10000000000 : ℝ)^4645 ≤ (19924403036169/50000000000000 : ℝ)^3621 := by
    have hnat : (4880952673 : ℕ)^4645*50000000000000^3621 ≤ 19924403036169^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880952673 10000000000 19924403036169 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1622004289/10000000000 : ℝ), (2933330437/5000000000 : ℝ), (4880952673/10000000000 : ℝ)] ![(9697478038253/100000000000000 : ℝ), (50453715868699/100000000000000 : ℝ), (19924403036169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1622004289/10000000000 : ℝ)|^4645 ≤ (9697478038253/100000000000000 : ℝ)^3621
        have hw : |(-1622004289/10000000000 : ℝ)|=(1622004289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2933330437/5000000000 : ℝ)|^4645 ≤ (50453715868699/100000000000000 : ℝ)^3621
        have hw : |(2933330437/5000000000 : ℝ)|=(2933330437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880952673/10000000000 : ℝ)|^4645 ≤ (19924403036169/50000000000000 : ℝ)^3621
        have hw : |(4880952673/10000000000 : ℝ)|=(4880952673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_1 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5464625803/10000000000 : ℝ)*x 0 + (-2170267201/10000000000 : ℝ)*x 1 + (4880952669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464625803/10000000000 : ℝ)^4645 ≤ (11515528880587/25000000000000 : ℝ)^3621 := by
    have hnat : (5464625803 : ℕ)^4645*25000000000000^3621 ≤ 11515528880587^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464625803 10000000000 11515528880587 25000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170267201/10000000000 : ℝ)^4645 ≤ (7044539215169/50000000000000 : ℝ)^3621 := by
    have hnat : (2170267201 : ℕ)^4645*50000000000000^3621 ≤ 7044539215169^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170267201 10000000000 7044539215169 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4880952669/10000000000 : ℝ)^4645 ≤ (19924403015223/50000000000000 : ℝ)^3621 := by
    have hnat : (4880952669 : ℕ)^4645*50000000000000^3621 ≤ 19924403015223^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4880952669 10000000000 19924403015223 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5464625803/10000000000 : ℝ), (-2170267201/10000000000 : ℝ), (4880952669/10000000000 : ℝ)] ![(11515528880587/25000000000000 : ℝ), (7044539215169/50000000000000 : ℝ), (19924403015223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5464625803/10000000000 : ℝ)|^4645 ≤ (11515528880587/25000000000000 : ℝ)^3621
        have hw : |(5464625803/10000000000 : ℝ)|=(5464625803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170267201/10000000000 : ℝ)|^4645 ≤ (7044539215169/50000000000000 : ℝ)^3621
        have hw : |(-2170267201/10000000000 : ℝ)|=(2170267201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4880952669/10000000000 : ℝ)|^4645 ≤ (19924403015223/50000000000000 : ℝ)^3621
        have hw : |(4880952669/10000000000 : ℝ)|=(4880952669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_2 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5464625863/10000000000 : ℝ)*x 0 + (976190519/2000000000 : ℝ)*x 1 + (-135641701/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464625863/10000000000 : ℝ)^4645 ≤ (575776452139/1250000000000 : ℝ)^3621 := by
    have hnat : (5464625863 : ℕ)^4645*1250000000000^3621 ≤ 575776452139^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464625863 10000000000 575776452139 1250000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976190519/2000000000 : ℝ)^4645 ≤ (796976105109/2000000000000 : ℝ)^3621 := by
    have hnat : (976190519 : ℕ)^4645*2000000000000^3621 ≤ 796976105109^3621*2000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976190519 2000000000 796976105109 2000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135641701/625000000 : ℝ)^4645 ≤ (7044539277627/50000000000000 : ℝ)^3621 := by
    have hnat : (135641701 : ℕ)^4645*50000000000000^3621 ≤ 7044539277627^3621*625000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135641701 625000000 7044539277627 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5464625863/10000000000 : ℝ), (976190519/2000000000 : ℝ), (-135641701/625000000 : ℝ)] ![(575776452139/1250000000000 : ℝ), (796976105109/2000000000000 : ℝ), (7044539277627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5464625863/10000000000 : ℝ)|^4645 ≤ (575776452139/1250000000000 : ℝ)^3621
        have hw : |(5464625863/10000000000 : ℝ)|=(5464625863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(976190519/2000000000 : ℝ)|^4645 ≤ (796976105109/2000000000000 : ℝ)^3621
        have hw : |(976190519/2000000000 : ℝ)|=(976190519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135641701/625000000 : ℝ)|^4645 ≤ (7044539277627/50000000000000 : ℝ)^3621
        have hw : |(-135641701/625000000 : ℝ)|=(135641701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_3 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128820077/10000000000 : ℝ)*x 0 + (3093388991/10000000000 : ℝ)*x 1 + (1085311223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128820077/10000000000 : ℝ)^4645 ≤ (32150189225733/100000000000000 : ℝ)^3621 := by
    have hnat : (4128820077 : ℕ)^4645*100000000000000^3621 ≤ 32150189225733^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128820077 10000000000 32150189225733 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3093388991/10000000000 : ℝ)^4645 ≤ (11099465668497/50000000000000 : ℝ)^3621 := by
    have hnat : (3093388991 : ℕ)^4645*50000000000000^3621 ≤ 11099465668497^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3093388991 10000000000 11099465668497 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085311223/2000000000 : ℝ)^4645 ≤ (45650879421391/100000000000000 : ℝ)^3621 := by
    have hnat : (1085311223 : ℕ)^4645*100000000000000^3621 ≤ 45650879421391^3621*2000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085311223 2000000000 45650879421391 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128820077/10000000000 : ℝ), (3093388991/10000000000 : ℝ), (1085311223/2000000000 : ℝ)] ![(32150189225733/100000000000000 : ℝ), (11099465668497/50000000000000 : ℝ), (45650879421391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128820077/10000000000 : ℝ)|^4645 ≤ (32150189225733/100000000000000 : ℝ)^3621
        have hw : |(4128820077/10000000000 : ℝ)|=(4128820077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3093388991/10000000000 : ℝ)|^4645 ≤ (11099465668497/50000000000000 : ℝ)^3621
        have hw : |(3093388991/10000000000 : ℝ)|=(3093388991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085311223/2000000000 : ℝ)|^4645 ≤ (45650879421391/100000000000000 : ℝ)^3621
        have hw : |(1085311223/2000000000 : ℝ)|=(1085311223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_4 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1625029029/10000000000 : ℝ)*x 0 + (4905771359/10000000000 : ℝ)*x 1 + (2920482021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1625029029/10000000000 : ℝ)^4645 ≤ (4860341116409/50000000000000 : ℝ)^3621 := by
    have hnat : (1625029029 : ℕ)^4645*50000000000000^3621 ≤ 4860341116409^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625029029 10000000000 4860341116409 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4905771359/10000000000 : ℝ)^4645 ≤ (40108916913013/100000000000000 : ℝ)^3621 := by
    have hnat : (4905771359 : ℕ)^4645*100000000000000^3621 ≤ 40108916913013^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4905771359 10000000000 40108916913013 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2920482021/5000000000 : ℝ)^4645 ≤ (1003408016843/2000000000000 : ℝ)^3621 := by
    have hnat : (2920482021 : ℕ)^4645*2000000000000^3621 ≤ 1003408016843^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2920482021 5000000000 1003408016843 2000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1625029029/10000000000 : ℝ), (4905771359/10000000000 : ℝ), (2920482021/5000000000 : ℝ)] ![(4860341116409/50000000000000 : ℝ), (40108916913013/100000000000000 : ℝ), (1003408016843/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1625029029/10000000000 : ℝ)|^4645 ≤ (4860341116409/50000000000000 : ℝ)^3621
        have hw : |(-1625029029/10000000000 : ℝ)|=(1625029029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4905771359/10000000000 : ℝ)|^4645 ≤ (40108916913013/100000000000000 : ℝ)^3621
        have hw : |(4905771359/10000000000 : ℝ)|=(4905771359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2920482021/5000000000 : ℝ)|^4645 ≤ (1003408016843/2000000000000 : ℝ)^3621
        have hw : |(2920482021/5000000000 : ℝ)|=(2920482021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_5 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195152871/10000000000 : ℝ)*x 0 + (-605128143/5000000000 : ℝ)*x 1 + (5840963731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195152871/10000000000 : ℝ)^4645 ≤ (5396112920421/12500000000000 : ℝ)^3621 := by
    have hnat : (5195152871 : ℕ)^4645*12500000000000^3621 ≤ 5396112920421^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195152871 10000000000 5396112920421 12500000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605128143/5000000000 : ℝ)^4645 ≤ (6660699218727/100000000000000 : ℝ)^3621 := by
    have hnat : (605128143 : ℕ)^4645*100000000000000^3621 ≤ 6660699218727^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605128143 5000000000 6660699218727 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5840963731/10000000000 : ℝ)^4645 ≤ (25085198707707/50000000000000 : ℝ)^3621 := by
    have hnat : (5840963731 : ℕ)^4645*50000000000000^3621 ≤ 25085198707707^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5840963731 10000000000 25085198707707 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195152871/10000000000 : ℝ), (-605128143/5000000000 : ℝ), (5840963731/10000000000 : ℝ)] ![(5396112920421/12500000000000 : ℝ), (6660699218727/100000000000000 : ℝ), (25085198707707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195152871/10000000000 : ℝ)|^4645 ≤ (5396112920421/12500000000000 : ℝ)^3621
        have hw : |(5195152871/10000000000 : ℝ)|=(5195152871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605128143/5000000000 : ℝ)|^4645 ≤ (6660699218727/100000000000000 : ℝ)^3621
        have hw : |(-605128143/5000000000 : ℝ)|=(605128143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5840963731/10000000000 : ℝ)|^4645 ≤ (25085198707707/50000000000000 : ℝ)^3621
        have hw : |(5840963731/10000000000 : ℝ)|=(5840963731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_6 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195152393/10000000000 : ℝ)*x 0 + (5840964439/10000000000 : ℝ)*x 1 + (-12102559/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195152393/10000000000 : ℝ)^4645 ≤ (43168898268209/100000000000000 : ℝ)^3621 := by
    have hnat : (5195152393 : ℕ)^4645*100000000000000^3621 ≤ 43168898268209^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195152393 10000000000 43168898268209 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5840964439/10000000000 : ℝ)^4645 ≤ (6271300652059/12500000000000 : ℝ)^3621 := by
    have hnat : (5840964439 : ℕ)^4645*12500000000000^3621 ≤ 6271300652059^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5840964439 10000000000 6271300652059 12500000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12102559/100000000 : ℝ)^4645 ≤ (3330348246799/50000000000000 : ℝ)^3621 := by
    have hnat : (12102559 : ℕ)^4645*50000000000000^3621 ≤ 3330348246799^3621*100000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12102559 100000000 3330348246799 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195152393/10000000000 : ℝ), (5840964439/10000000000 : ℝ), (-12102559/100000000 : ℝ)] ![(43168898268209/100000000000000 : ℝ), (6271300652059/12500000000000 : ℝ), (3330348246799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195152393/10000000000 : ℝ)|^4645 ≤ (43168898268209/100000000000000 : ℝ)^3621
        have hw : |(5195152393/10000000000 : ℝ)|=(5195152393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5840964439/10000000000 : ℝ)|^4645 ≤ (6271300652059/12500000000000 : ℝ)^3621
        have hw : |(5840964439/10000000000 : ℝ)|=(5840964439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12102559/100000000 : ℝ)|^4645 ≤ (3330348246799/50000000000000 : ℝ)^3621
        have hw : |(-12102559/100000000 : ℝ)|=(12102559/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s0_7 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129249319/312500000 : ℝ)*x 0 + (5367808893/10000000000 : ℝ)*x 1 + (1577106757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129249319/312500000 : ℝ)^4645 ≤ (32221708124251/100000000000000 : ℝ)^3621 := by
    have hnat : (129249319 : ℕ)^4645*100000000000000^3621 ≤ 32221708124251^3621*312500000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129249319 312500000 32221708124251 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5367808893/10000000000 : ℝ)^4645 ≤ (11254470354193/25000000000000 : ℝ)^3621 := by
    have hnat : (5367808893 : ℕ)^4645*25000000000000^3621 ≤ 11254470354193^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367808893 10000000000 11254470354193 25000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577106757/5000000000 : ℝ)^4645 ≤ (711262826409/3125000000000 : ℝ)^3621 := by
    have hnat : (1577106757 : ℕ)^4645*3125000000000^3621 ≤ 711262826409^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577106757 5000000000 711262826409 3125000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129249319/312500000 : ℝ), (5367808893/10000000000 : ℝ), (1577106757/5000000000 : ℝ)] ![(32221708124251/100000000000000 : ℝ), (11254470354193/25000000000000 : ℝ), (711262826409/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129249319/312500000 : ℝ)|^4645 ≤ (32221708124251/100000000000000 : ℝ)^3621
        have hw : |(129249319/312500000 : ℝ)|=(129249319/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5367808893/10000000000 : ℝ)|^4645 ≤ (11254470354193/25000000000000 : ℝ)^3621
        have hw : |(5367808893/10000000000 : ℝ)|=(5367808893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577106757/5000000000 : ℝ)|^4645 ≤ (711262826409/3125000000000 : ℝ)^3621
        have hw : |(1577106757/5000000000 : ℝ)|=(1577106757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1574_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (449/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12353/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4643/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4643 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4643*1^1024 ≤ 0^1024*1^4643 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4643 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4643/1024 : ℝ) ≤ (1569164577791394271/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4643 ≤ (1569164577791394271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4643*100000000000000000000^1024 ≤ 1569164577791394271^1024*5^4643 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1569164577791394271 100000000000000000000 4643 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1569164577791394271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4643 := by
      have hnat : (1 : ℕ)^1024*1^4643 ≤ 1^4643*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101569164577791394271/100000000000000000000 : ℝ) ≤ (10034397771858183/10000000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (101569164577791394271/100000000000000000000 : ℝ)^1024 ≤ (10034397771858183/10000000000000000 : ℝ)^4643 := by
      have hnat : (101569164577791394271 : ℕ)^1024*10000000000000000^4643 ≤ 10034397771858183^4643*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101569164577791394271 100000000000000000000 10034397771858183 10000000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034397771858183/10000000000000000 : ℝ)) (X := (101569164577791394271/100000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51569164577791394271/50000000000000000000 : ℝ) ≤ (5034397771858183/5000000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (51569164577791394271/50000000000000000000 : ℝ)^1024 ≤ (5034397771858183/5000000000000000 : ℝ)^4643 := by
      have hnat : (51569164577791394271 : ℕ)^1024*5000000000000000^4643 ≤ 5034397771858183^4643*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51569164577791394271 50000000000000000000 5034397771858183 5000000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5034397771858183/5000000000000000 : ℝ)) (X := (51569164577791394271/50000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(34397771858183/4000000000000000 : ℝ)*(0 : ℝ))^(4643/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34397771858183/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1569164577791394271/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(34397771858183/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4643/1024 : ℝ) := by
    rw [show (1 : ℝ)+(34397771858183/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10034397771858183/10000000000000000 : ℝ) by norm_num, show 1+(1569164577791394271/100000000000000000000 : ℝ)+(0 : ℝ)=(101569164577791394271/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1569164577791394271/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(34397771858183/4000000000000000 : ℝ)*(2/5 : ℝ))^(4643/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34397771858183/4000000000000000 : ℝ)*(2/5 : ℝ)=(5034397771858183/5000000000000000 : ℝ) by norm_num, show 1+2*(1569164577791394271/100000000000000000000 : ℝ)=(51569164577791394271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(34397771858183/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34397771858183/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(34397771858183/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34397771858183/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(34397771858183/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34397771858183/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1622004289/10000000000 : ℝ)*X 0 0+(2933330437/5000000000 : ℝ)*X 0 1+(4880952673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5464625803/10000000000 : ℝ)*X 1 0+(-2170267201/10000000000 : ℝ)*X 1 1+(4880952669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5464625863/10000000000 : ℝ)*X 2 0+(976190519/2000000000 : ℝ)*X 2 1+(-135641701/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4128820077/10000000000 : ℝ)*X 0 0+(3093388991/10000000000 : ℝ)*X 0 1+(1085311223/2000000000 : ℝ)*X 0 2+(4128820077/10000000000 : ℝ)*X 1 0+(3093388991/10000000000 : ℝ)*X 1 1+(1085311223/2000000000 : ℝ)*X 1 2+(4128820077/10000000000 : ℝ)*X 2 0+(3093388991/10000000000 : ℝ)*X 2 1+(1085311223/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1625029029/10000000000 : ℝ)*X 0 0+(4905771359/10000000000 : ℝ)*X 0 1+(2920482021/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195152871/10000000000 : ℝ)*X 1 0+(-605128143/5000000000 : ℝ)*X 1 1+(5840963731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5195152393/10000000000 : ℝ)*X 2 0+(5840964439/10000000000 : ℝ)*X 2 1+(-12102559/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((129249319/312500000 : ℝ)*X 0 0+(5367808893/10000000000 : ℝ)*X 0 1+(1577106757/5000000000 : ℝ)*X 0 2+(129249319/312500000 : ℝ)*X 1 0+(5367808893/10000000000 : ℝ)*X 1 1+(1577106757/5000000000 : ℝ)*X 1 2+(129249319/312500000 : ℝ)*X 2 0+(5367808893/10000000000 : ℝ)*X 2 1+(1577106757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29949045924610375208133/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2746413/10000000000000 : ℝ)*(base1) + (580214093/100000000000000 : ℝ)*(base19) + (147838259/25000000000000 : ℝ)*(base23) + (37259237/50000000000000 : ℝ)*(upper3) + (36501281/50000000000000 : ℝ)*(upper5) + (144310710530783/20000000000000 : ℝ)*(major0) + (144310710530783/20000000000000 : ℝ)*(major1) + (144310710530783/20000000000000 : ℝ)*(major2) + (507250537730879/50000000000000 : ℝ)*(sp0) + (507251320779693/50000000000000 : ℝ)*(sp1) + (1014502630420443/100000000000000 : ℝ)*(sp2) + (428602828679347/100000000000000 : ℝ)*(sp3) + (2173775851/100000000000000 : ℝ)*(sp4) + (463780359/50000000000000 : ℝ)*(sp7) + (85720756740839/20000000000000 : ℝ)*(f.failure) + (1014503221773479/100000000000000 : ℝ)*(f.sum) + (121059159067289/40000000000000000000000000000 : ℝ)*base65 + (254960767787289/80000000000000000000000000000 : ℝ)*base67 + (153657825307289/80000000000000000000000000000 : ℝ)*base69 + (46490530267289/80000000000000000000000000000 : ℝ)*base71 + (279490713347289/40000000000000000000000000000 : ℝ)*base73 + (1571963332711/80000000000000000000000000000 : ℝ)*base76 + (152651897812711/80000000000000000000000000000 : ℝ)*base78 + (307889441067289/80000000000000000000000000000 : ℝ)*base79 + (245816001187289/40000000000000000000000000000 : ℝ)*base81 + (1555227/1000000000000000000000 : ℝ)*base89 + (1555227/1000000000000000000000 : ℝ)*base91 + (1555227/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (886427250620148090338847/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (995418367/50000000000000 : ℝ)*(base19) + (496991091/25000000000000 : ℝ)*(base23) + (47815701/50000000000000 : ℝ)*(base39) + (258242667/100000000000000 : ℝ)*(upper3) + (177331161/50000000000000 : ℝ)*(upper5) + (760525924235533/100000000000000 : ℝ)*(major0) + (760525924235533/100000000000000 : ℝ)*(major1) + (760525828604131/100000000000000 : ℝ)*(major2) + (2794230209/50000000000000 : ℝ)*(sp1) + (2808335793/50000000000000 : ℝ)*(sp2) + (1069298032363693/100000000000000 : ℝ)*(sp4) + (53464522653327/5000000000000 : ℝ)*(sp5) + (133661315419893/12500000000000 : ℝ)*(sp6) + (90350685000043/20000000000000 : ℝ)*(sp7) + (90350685000043/20000000000000 : ℝ)*(f.failure) + (534649063997547/50000000000000 : ℝ)*(f.sum) + (31782993510657/25000000000000000000000000000 : ℝ)*base65 + (2567048667153973/400000000000000000000000000000 : ℝ)*base67 + (159342119016539/400000000000000000000000000000 : ℝ)*base69 + (1718034294353973/400000000000000000000000000000 : ℝ)*base71 + (124387470660657/25000000000000000000000000000 : ℝ)*base73 + (1108026408616539/400000000000000000000000000000 : ℝ)*base75 + (2106165153416539/400000000000000000000000000000 : ℝ)*base77 + (1040292013016539/400000000000000000000000000000 : ℝ)*base79 + (508148898616539/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5479601/1000000000000000000000 : ℝ)*base90 + (5479601/1000000000000000000000 : ℝ)*base92 + (5479601/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1574_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (449/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1574_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1574_s1_0 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219949981/1250000000 : ℝ)*x 0 + (1383144617/2500000000 : ℝ)*x 1 + (320395551/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219949981/1250000000 : ℝ)^4645 ≤ (5382584956479/50000000000000 : ℝ)^3621 := by
    have hnat : (219949981 : ℕ)^4645*50000000000000^3621 ≤ 5382584956479^3621*1250000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219949981 1250000000 5382584956479 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383144617/2500000000 : ℝ)^4645 ≤ (2339908319143/5000000000000 : ℝ)^3621 := by
    have hnat : (1383144617 : ℕ)^4645*5000000000000^3621 ≤ 2339908319143^3621*2500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383144617 2500000000 2339908319143 5000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320395551/625000000 : ℝ)^4645 ≤ (424366636873/1000000000000 : ℝ)^3621 := by
    have hnat : (320395551 : ℕ)^4645*1000000000000^3621 ≤ 424366636873^3621*625000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320395551 625000000 424366636873 1000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219949981/1250000000 : ℝ), (1383144617/2500000000 : ℝ), (320395551/625000000 : ℝ)] ![(5382584956479/50000000000000 : ℝ), (2339908319143/5000000000000 : ℝ), (424366636873/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219949981/1250000000 : ℝ)|^4645 ≤ (5382584956479/50000000000000 : ℝ)^3621
        have hw : |(-219949981/1250000000 : ℝ)|=(219949981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383144617/2500000000 : ℝ)|^4645 ≤ (2339908319143/5000000000000 : ℝ)^3621
        have hw : |(1383144617/2500000000 : ℝ)|=(1383144617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(320395551/625000000 : ℝ)|^4645 ≤ (424366636873/1000000000000 : ℝ)^3621
        have hw : |(320395551/625000000 : ℝ)|=(320395551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_1 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343941407/2500000000 : ℝ)*x 0 + (-1972007733/10000000000 : ℝ)*x 1 + (1025265701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343941407/2500000000 : ℝ)^4645 ≤ (22551750299827/50000000000000 : ℝ)^3621 := by
    have hnat : (1343941407 : ℕ)^4645*50000000000000^3621 ≤ 22551750299827^3621*2500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343941407 2500000000 22551750299827 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972007733/10000000000 : ℝ)^4645 ≤ (12459838992979/100000000000000 : ℝ)^3621 := by
    have hnat : (1972007733 : ℕ)^4645*100000000000000^3621 ≤ 12459838992979^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972007733 10000000000 12459838992979 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025265701/2000000000 : ℝ)^4645 ≤ (42436660384727/100000000000000 : ℝ)^3621 := by
    have hnat : (1025265701 : ℕ)^4645*100000000000000^3621 ≤ 42436660384727^3621*2000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025265701 2000000000 42436660384727 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343941407/2500000000 : ℝ), (-1972007733/10000000000 : ℝ), (1025265701/2000000000 : ℝ)] ![(22551750299827/50000000000000 : ℝ), (12459838992979/100000000000000 : ℝ), (42436660384727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343941407/2500000000 : ℝ)|^4645 ≤ (22551750299827/50000000000000 : ℝ)^3621
        have hw : |(1343941407/2500000000 : ℝ)|=(1343941407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972007733/10000000000 : ℝ)|^4645 ≤ (12459838992979/100000000000000 : ℝ)^3621
        have hw : |(-1972007733/10000000000 : ℝ)|=(1972007733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1025265701/2000000000 : ℝ)|^4645 ≤ (42436660384727/100000000000000 : ℝ)^3621
        have hw : |(1025265701/2000000000 : ℝ)|=(1025265701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_2 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375765503/10000000000 : ℝ)*x 0 + (64079109/125000000 : ℝ)*x 1 + (-1972007619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375765503/10000000000 : ℝ)^4645 ≤ (45103499254299/100000000000000 : ℝ)^3621 := by
    have hnat : (5375765503 : ℕ)^4645*100000000000000^3621 ≤ 45103499254299^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375765503 10000000000 45103499254299 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64079109/125000000 : ℝ)^4645 ≤ (2652291416741/6250000000000 : ℝ)^3621 := by
    have hnat : (64079109 : ℕ)^4645*6250000000000^3621 ≤ 2652291416741^3621*125000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64079109 125000000 2652291416741 6250000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972007619/10000000000 : ℝ)^4645 ≤ (48671242457/390625000000 : ℝ)^3621 := by
    have hnat : (1972007619 : ℕ)^4645*390625000000^3621 ≤ 48671242457^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972007619 10000000000 48671242457 390625000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375765503/10000000000 : ℝ), (64079109/125000000 : ℝ), (-1972007619/10000000000 : ℝ)] ![(45103499254299/100000000000000 : ℝ), (2652291416741/6250000000000 : ℝ), (48671242457/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375765503/10000000000 : ℝ)|^4645 ≤ (45103499254299/100000000000000 : ℝ)^3621
        have hw : |(5375765503/10000000000 : ℝ)|=(5375765503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64079109/125000000 : ℝ)|^4645 ≤ (2652291416741/6250000000000 : ℝ)^3621
        have hw : |(64079109/125000000 : ℝ)|=(64079109/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972007619/10000000000 : ℝ)|^4645 ≤ (48671242457/390625000000 : ℝ)^3621
        have hw : |(-1972007619/10000000000 : ℝ)|=(1972007619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_3 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227003687/10000000000 : ℝ)*x 0 + (3768181261/10000000000 : ℝ)*x 1 + (2364886867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227003687/10000000000 : ℝ)^4645 ≤ (6626841613269/20000000000000 : ℝ)^3621 := by
    have hnat : (4227003687 : ℕ)^4645*20000000000000^3621 ≤ 6626841613269^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227003687 10000000000 6626841613269 20000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3768181261/10000000000 : ℝ)^4645 ≤ (14296642568677/50000000000000 : ℝ)^3621 := by
    have hnat : (3768181261 : ℕ)^4645*50000000000000^3621 ≤ 14296642568677^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3768181261 10000000000 14296642568677 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364886867/5000000000 : ℝ)^4645 ≤ (19136253389617/50000000000000 : ℝ)^3621 := by
    have hnat : (2364886867 : ℕ)^4645*50000000000000^3621 ≤ 19136253389617^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364886867 5000000000 19136253389617 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227003687/10000000000 : ℝ), (3768181261/10000000000 : ℝ), (2364886867/5000000000 : ℝ)] ![(6626841613269/20000000000000 : ℝ), (14296642568677/50000000000000 : ℝ), (19136253389617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227003687/10000000000 : ℝ)|^4645 ≤ (6626841613269/20000000000000 : ℝ)^3621
        have hw : |(4227003687/10000000000 : ℝ)|=(4227003687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3768181261/10000000000 : ℝ)|^4645 ≤ (14296642568677/50000000000000 : ℝ)^3621
        have hw : |(3768181261/10000000000 : ℝ)|=(3768181261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2364886867/5000000000 : ℝ)|^4645 ≤ (19136253389617/50000000000000 : ℝ)^3621
        have hw : |(2364886867/5000000000 : ℝ)|=(2364886867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_4 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87990303/500000000 : ℝ)*x 0 + (5130497181/10000000000 : ℝ)*x 1 + (5528348963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87990303/500000000 : ℝ)^4645 ≤ (430671532433/4000000000000 : ℝ)^3621 := by
    have hnat : (87990303 : ℕ)^4645*4000000000000^3621 ≤ 430671532433^3621*500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87990303 500000000 430671532433 4000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130497181/10000000000 : ℝ)^4645 ≤ (42480933494207/100000000000000 : ℝ)^3621 := by
    have hnat : (5130497181 : ℕ)^4645*100000000000000^3621 ≤ 42480933494207^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130497181 10000000000 42480933494207 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528348963/10000000000 : ℝ)^4645 ≤ (9350455636303/20000000000000 : ℝ)^3621 := by
    have hnat : (5528348963 : ℕ)^4645*20000000000000^3621 ≤ 9350455636303^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528348963 10000000000 9350455636303 20000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87990303/500000000 : ℝ), (5130497181/10000000000 : ℝ), (5528348963/10000000000 : ℝ)] ![(430671532433/4000000000000 : ℝ), (42480933494207/100000000000000 : ℝ), (9350455636303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87990303/500000000 : ℝ)|^4645 ≤ (430671532433/4000000000000 : ℝ)^3621
        have hw : |(-87990303/500000000 : ℝ)|=(87990303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130497181/10000000000 : ℝ)|^4645 ≤ (42480933494207/100000000000000 : ℝ)^3621
        have hw : |(5130497181/10000000000 : ℝ)|=(5130497181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528348963/10000000000 : ℝ)|^4645 ≤ (9350455636303/20000000000000 : ℝ)^3621
        have hw : |(5528348963/10000000000 : ℝ)|=(5528348963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_5 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268038999/10000000000 : ℝ)*x 0 + (-1569987273/10000000000 : ℝ)*x 1 + (5528349489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268038999/10000000000 : ℝ)^4645 ≤ (43947356676437/100000000000000 : ℝ)^3621 := by
    have hnat : (5268038999 : ℕ)^4645*100000000000000^3621 ≤ 43947356676437^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268038999 10000000000 43947356676437 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1569987273/10000000000 : ℝ)^4645 ≤ (4650179712577/50000000000000 : ℝ)^3621 := by
    have hnat : (1569987273 : ℕ)^4645*50000000000000^3621 ≤ 4650179712577^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569987273 10000000000 4650179712577 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528349489/10000000000 : ℝ)^4645 ≤ (23376141943879/50000000000000 : ℝ)^3621 := by
    have hnat : (5528349489 : ℕ)^4645*50000000000000^3621 ≤ 23376141943879^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528349489 10000000000 23376141943879 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268038999/10000000000 : ℝ), (-1569987273/10000000000 : ℝ), (5528349489/10000000000 : ℝ)] ![(43947356676437/100000000000000 : ℝ), (4650179712577/50000000000000 : ℝ), (23376141943879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268038999/10000000000 : ℝ)|^4645 ≤ (43947356676437/100000000000000 : ℝ)^3621
        have hw : |(5268038999/10000000000 : ℝ)|=(5268038999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1569987273/10000000000 : ℝ)|^4645 ≤ (4650179712577/50000000000000 : ℝ)^3621
        have hw : |(-1569987273/10000000000 : ℝ)|=(1569987273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528349489/10000000000 : ℝ)|^4645 ≤ (23376141943879/50000000000000 : ℝ)^3621
        have hw : |(5528349489/10000000000 : ℝ)|=(5528349489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_6 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2634019193/5000000000 : ℝ)*x 0 + (5528349721/10000000000 : ℝ)*x 1 + (-313997561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634019193/5000000000 : ℝ)^4645 ≤ (21973675058237/50000000000000 : ℝ)^3621 := by
    have hnat : (2634019193 : ℕ)^4645*50000000000000^3621 ≤ 21973675058237^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634019193 5000000000 21973675058237 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528349721/10000000000 : ℝ)^4645 ≤ (2337614320229/5000000000000 : ℝ)^3621 := by
    have hnat : (5528349721 : ℕ)^4645*5000000000000^3621 ≤ 2337614320229^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528349721 10000000000 2337614320229 5000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313997561/2000000000 : ℝ)^4645 ≤ (9300363467863/100000000000000 : ℝ)^3621 := by
    have hnat : (313997561 : ℕ)^4645*100000000000000^3621 ≤ 9300363467863^3621*2000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313997561 2000000000 9300363467863 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2634019193/5000000000 : ℝ), (5528349721/10000000000 : ℝ), (-313997561/2000000000 : ℝ)] ![(21973675058237/50000000000000 : ℝ), (2337614320229/5000000000000 : ℝ), (9300363467863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2634019193/5000000000 : ℝ)|^4645 ≤ (21973675058237/50000000000000 : ℝ)^3621
        have hw : |(2634019193/5000000000 : ℝ)|=(2634019193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528349721/10000000000 : ℝ)|^4645 ≤ (2337614320229/5000000000000 : ℝ)^3621
        have hw : |(5528349721/10000000000 : ℝ)|=(5528349721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-313997561/2000000000 : ℝ)|^4645 ≤ (9300363467863/100000000000000 : ℝ)^3621
        have hw : |(-313997561/2000000000 : ℝ)|=(313997561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s1_7 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4227490819/10000000000 : ℝ)*x 0 + (4719907621/10000000000 : ℝ)*x 1 + (3778192251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227490819/10000000000 : ℝ)^4645 ≤ (1035597077303/3125000000000 : ℝ)^3621 := by
    have hnat : (4227490819 : ℕ)^4645*3125000000000^3621 ≤ 1035597077303^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227490819 10000000000 1035597077303 3125000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4719907621/10000000000 : ℝ)^4645 ≤ (7634025048469/20000000000000 : ℝ)^3621 := by
    have hnat : (4719907621 : ℕ)^4645*20000000000000^3621 ≤ 7634025048469^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719907621 10000000000 7634025048469 20000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3778192251/10000000000 : ℝ)^4645 ≤ (1793173017207/6250000000000 : ℝ)^3621 := by
    have hnat : (3778192251 : ℕ)^4645*6250000000000^3621 ≤ 1793173017207^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3778192251 10000000000 1793173017207 6250000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227490819/10000000000 : ℝ), (4719907621/10000000000 : ℝ), (3778192251/10000000000 : ℝ)] ![(1035597077303/3125000000000 : ℝ), (7634025048469/20000000000000 : ℝ), (1793173017207/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227490819/10000000000 : ℝ)|^4645 ≤ (1035597077303/3125000000000 : ℝ)^3621
        have hw : |(4227490819/10000000000 : ℝ)|=(4227490819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4719907621/10000000000 : ℝ)|^4645 ≤ (7634025048469/20000000000000 : ℝ)^3621
        have hw : |(4719907621/10000000000 : ℝ)|=(4719907621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3778192251/10000000000 : ℝ)|^4645 ≤ (1793173017207/6250000000000 : ℝ)^3621
        have hw : |(3778192251/10000000000 : ℝ)|=(3778192251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1574_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (4557/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (449/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12353/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (449/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (449/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12353/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (449/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (449/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12353/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (449/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (449/12500 : ℝ) ^ (4643/1024 : ℝ) ≤ (5632034659547/20000000000000000000 : ℝ) := by
    have hpowers : (449/12500 : ℝ)^4643 ≤ (5632034659547/20000000000000000000 : ℝ)^1024 := by
      have hnat : (449 : ℕ)^4643*20000000000000000000^1024 ≤ 5632034659547^1024*12500^4643 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        449 12500 5632034659547 20000000000000000000 4643 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (449/12500 : ℝ)) (X := (5632034659547/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12353/50000 : ℝ) ^ (4643/1024 : ℝ) ≤ (88272849939820611/50000000000000000000 : ℝ) := by
    have hpowers : (12353/50000 : ℝ)^4643 ≤ (88272849939820611/50000000000000000000 : ℝ)^1024 := by
      have hnat : (12353 : ℕ)^4643*50000000000000000000^1024 ≤ 88272849939820611^1024*50000^4643 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12353 50000 88272849939820611 50000000000000000000 4643 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12353/50000 : ℝ)) (X := (88272849939820611/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000005632034659547/10000000000000000000 : ℝ) ≤ (5000000621064207/5000000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (10000005632034659547/10000000000000000000 : ℝ)^1024 ≤ (5000000621064207/5000000000000000 : ℝ)^4643 := by
      have hnat : (10000005632034659547 : ℕ)^1024*5000000000000000^4643 ≤ 5000000621064207^4643*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000005632034659547 10000000000000000000 5000000621064207 5000000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000621064207/5000000000000000 : ℝ)) (X := (10000005632034659547/10000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100176573860052938957/100000000000000000000 : ℝ) ≤ (2000778321500799/2000000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (100176573860052938957/100000000000000000000 : ℝ)^1024 ≤ (2000778321500799/2000000000000000 : ℝ)^4643 := by
      have hnat : (100176573860052938957 : ℕ)^1024*2000000000000000^4643 ≤ 2000778321500799^4643*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100176573860052938957 100000000000000000000 2000778321500799 2000000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000778321500799/2000000000000000 : ℝ)) (X := (100176573860052938957/100000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25088272849939820611/25000000000000000000 : ℝ) ≤ (1250972746609947/1250000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (25088272849939820611/25000000000000000000 : ℝ)^1024 ≤ (1250972746609947/1250000000000000 : ℝ)^4643 := by
      have hnat : (25088272849939820611 : ℕ)^1024*1250000000000000^4643 ≤ 1250972746609947^4643*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25088272849939820611 25000000000000000000 1250972746609947 1250000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250972746609947/1250000000000000 : ℝ)) (X := (25088272849939820611/25000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5632034659547/20000000000000000000 : ℝ) ≤ ((114984791852636797/115000000000000000 : ℝ)+2*(8475741559/4600000000000 : ℝ)*(449/12500 : ℝ))^(4643/1024 : ℝ) := by
    rw [show (114984791852636797/115000000000000000 : ℝ)+2*(8475741559/4600000000000 : ℝ)*(449/12500 : ℝ)=(5000000621064207/5000000000000000 : ℝ) by norm_num, show 1+2*(5632034659547/20000000000000000000 : ℝ)=(10000005632034659547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(88272849939820611/50000000000000000000 : ℝ)+(5632034659547/20000000000000000000 : ℝ) ≤ ((114984791852636797/115000000000000000 : ℝ)+(8475741559/4600000000000 : ℝ)*((12353/50000 : ℝ)+(449/12500 : ℝ)))^(4643/1024 : ℝ) := by
    rw [show (114984791852636797/115000000000000000 : ℝ)+(8475741559/4600000000000 : ℝ)*((12353/50000 : ℝ)+(449/12500 : ℝ))=(2000778321500799/2000000000000000 : ℝ) by norm_num, show 1+(88272849939820611/50000000000000000000 : ℝ)+(5632034659547/20000000000000000000 : ℝ)=(100176573860052938957/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(88272849939820611/50000000000000000000 : ℝ) ≤ ((114984791852636797/115000000000000000 : ℝ)+2*(8475741559/4600000000000 : ℝ)*(12353/50000 : ℝ))^(4643/1024 : ℝ) := by
    rw [show (114984791852636797/115000000000000000 : ℝ)+2*(8475741559/4600000000000 : ℝ)*(12353/50000 : ℝ)=(1250972746609947/1250000000000000 : ℝ) by norm_num, show 1+2*(88272849939820611/50000000000000000000 : ℝ)=(25088272849939820611/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (114984791852636797/115000000000000000 : ℝ)*(X 1 0+X 2 0)+(8475741559/4600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (449/12500 : ℝ)) (hi := (12353/50000 : ℝ)) (c := (114984791852636797/115000000000000000 : ℝ)) (alpha := (8475741559/4600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (114984791852636797/115000000000000000 : ℝ)*(X 0 1+X 2 1)+(8475741559/4600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (449/12500 : ℝ)) (hi := (12353/50000 : ℝ)) (c := (114984791852636797/115000000000000000 : ℝ)) (alpha := (8475741559/4600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (114984791852636797/115000000000000000 : ℝ)*(X 0 2+X 1 2)+(8475741559/4600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (449/12500 : ℝ)) (hi := (12353/50000 : ℝ)) (c := (114984791852636797/115000000000000000 : ℝ)) (alpha := (8475741559/4600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219949981/1250000000 : ℝ)*X 0 0+(1383144617/2500000000 : ℝ)*X 0 1+(320395551/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343941407/2500000000 : ℝ)*X 1 0+(-1972007733/10000000000 : ℝ)*X 1 1+(1025265701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375765503/10000000000 : ℝ)*X 2 0+(64079109/125000000 : ℝ)*X 2 1+(-1972007619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4227003687/10000000000 : ℝ)*X 0 0+(3768181261/10000000000 : ℝ)*X 0 1+(2364886867/5000000000 : ℝ)*X 0 2+(4227003687/10000000000 : ℝ)*X 1 0+(3768181261/10000000000 : ℝ)*X 1 1+(2364886867/5000000000 : ℝ)*X 1 2+(4227003687/10000000000 : ℝ)*X 2 0+(3768181261/10000000000 : ℝ)*X 2 1+(2364886867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-87990303/500000000 : ℝ)*X 0 0+(5130497181/10000000000 : ℝ)*X 0 1+(5528348963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268038999/10000000000 : ℝ)*X 1 0+(-1569987273/10000000000 : ℝ)*X 1 1+(5528349489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2634019193/5000000000 : ℝ)*X 2 0+(5528349721/10000000000 : ℝ)*X 2 1+(-313997561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4227490819/10000000000 : ℝ)*X 0 0+(4719907621/10000000000 : ℝ)*X 0 1+(3778192251/10000000000 : ℝ)*X 0 2+(4227490819/10000000000 : ℝ)*X 1 0+(4719907621/10000000000 : ℝ)*X 1 1+(3778192251/10000000000 : ℝ)*X 1 2+(4227490819/10000000000 : ℝ)*X 2 0+(4719907621/10000000000 : ℝ)*X 2 1+(3778192251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12202895114385357498717633/2875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1367802309/100000000000000 : ℝ)*(base19) + (1301511243/100000000000000 : ℝ)*(base23) + (95331997/100000000000000 : ℝ)*(upper3) + (4866987/100000000000000 : ℝ)*(upper4) + (144216531/100000000000000 : ℝ)*(upper5) + (875379351256021/50000000000000 : ℝ)*(major0) + (875379351256021/50000000000000 : ℝ)*(major1) + (875379351256021/50000000000000 : ℝ)*(major2) + (49231038522373/2000000000000 : ℝ)*(sp0) + (1230781432273521/50000000000000 : ℝ)*(sp1) + (615390732709527/25000000000000 : ℝ)*(sp2) + (1039947426153247/100000000000000 : ℝ)*(sp3) + (6153115351/50000000000000 : ℝ)*(sp4) + (5605038633/100000000000000 : ℝ)*(sp7) + (25998825779797/2500000000000 : ℝ)*(f.failure) + (307695529043669/12500000000000 : ℝ)*(f.sum) + (400625794801/115000000000000000000000000 : ℝ)*base66 + (98233208885620263/5750000000000000000000000000000 : ℝ)*base68 + (46240684149370263/5750000000000000000000000000000 : ℝ)*base70 + (67752451238120263/5750000000000000000000000000000 : ℝ)*base72 + (475759662271/115000000000000000000000000 : ℝ)*base74 + (28689106907370263/5750000000000000000000000000000 : ℝ)*base76 + (54478667939120263/5750000000000000000000000000000 : ℝ)*base78 + (49708858249120263/5750000000000000000000000000000 : ℝ)*base80 + (14495863613/14375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1536721/125000000000000000000 : ℝ)*base89 + (1536721/125000000000000000000 : ℝ)*base91 + (1536721/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (965140920023640623709/115000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148104807/10000000000000 : ℝ)*(base19) + (1330528701/100000000000000 : ℝ)*(base23) + (1316883/1562500000000 : ℝ)*(upper2) + (29708123/10000000000000 : ℝ)*(upper3) + (142655553/100000000000000 : ℝ)*(upper5) + (6983177575607/390625000000 : ℝ)*(major0) + (6983177575607/390625000000 : ℝ)*(major1) + (6983177575607/390625000000 : ℝ)*(major2) + (12372525963/100000000000000 : ℝ)*(sp1) + (11490836437/100000000000000 : ℝ)*(sp2) + (2513494312375307/100000000000000 : ℝ)*(sp4) + (1256740229400637/50000000000000 : ℝ)*(sp5) + (314185186376271/12500000000000 : ℝ)*(sp6) + (1061892326584479/100000000000000 : ℝ)*(sp7) + (1061892326584479/100000000000000 : ℝ)*(f.failure) + (2513494312375307/100000000000000 : ℝ)*(f.sum) + (506707211749/115000000000000000000000000 : ℝ)*base65 + (138195394121241/179687500000000000000000000000 : ℝ)*base67 + (567935148714991/179687500000000000000000000000 : ℝ)*base69 + (705263142929393/359375000000000000000000000000 : ℝ)*base72 + (242456269297/57500000000000000000000000 : ℝ)*base73 + (353802008941259/179687500000000000000000000000 : ℝ)*base76 + (182227191372577/22460937500000000000000000000 : ℝ)*base77 + (1200289783991893/359375000000000000000000000000 : ℝ)*base80 + (243611978587/57500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (24714253/5000000000000000000000 : ℝ)*base90 + (24714253/5000000000000000000000 : ℝ)*base92 + (24714253/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1574_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12353/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (449/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4557/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1574_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1574_s2_0 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88892089/500000000 : ℝ)*x 0 + (2720225443/5000000000 : ℝ)*x 1 + (5206564099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88892089/500000000 : ℝ)^4645 ≤ (10908543644271/100000000000000 : ℝ)^3621 := by
    have hnat : (88892089 : ℕ)^4645*100000000000000^3621 ≤ 10908543644271^3621*500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88892089 500000000 10908543644271 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720225443/5000000000 : ℝ)^4645 ≤ (2862554948503/6250000000000 : ℝ)^3621 := by
    have hnat : (2720225443 : ℕ)^4645*6250000000000^3621 ≤ 2862554948503^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720225443 5000000000 2862554948503 6250000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206564099/10000000000 : ℝ)^4645 ≤ (5411322144771/12500000000000 : ℝ)^3621 := by
    have hnat : (5206564099 : ℕ)^4645*12500000000000^3621 ≤ 5411322144771^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206564099 10000000000 5411322144771 12500000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88892089/500000000 : ℝ), (2720225443/5000000000 : ℝ), (5206564099/10000000000 : ℝ)] ![(10908543644271/100000000000000 : ℝ), (2862554948503/6250000000000 : ℝ), (5411322144771/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88892089/500000000 : ℝ)|^4645 ≤ (10908543644271/100000000000000 : ℝ)^3621
        have hw : |(-88892089/500000000 : ℝ)|=(88892089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720225443/5000000000 : ℝ)|^4645 ≤ (2862554948503/6250000000000 : ℝ)^3621
        have hw : |(2720225443/5000000000 : ℝ)|=(2720225443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206564099/10000000000 : ℝ)|^4645 ≤ (5411322144771/12500000000000 : ℝ)^3621
        have hw : |(5206564099/10000000000 : ℝ)|=(5206564099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_1 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267597329/500000000 : ℝ)*x 0 + (-1897865083/10000000000 : ℝ)*x 1 + (2603281887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267597329/500000000 : ℝ)^4645 ≤ (22423650320771/50000000000000 : ℝ)^3621 := by
    have hnat : (267597329 : ℕ)^4645*50000000000000^3621 ≤ 22423650320771^3621*500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267597329 500000000 22423650320771 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1897865083/10000000000 : ℝ)^4645 ≤ (11862125645609/100000000000000 : ℝ)^3621 := by
    have hnat : (1897865083 : ℕ)^4645*100000000000000^3621 ≤ 11862125645609^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897865083 10000000000 11862125645609 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603281887/5000000000 : ℝ)^4645 ≤ (5411321711467/12500000000000 : ℝ)^3621 := by
    have hnat : (2603281887 : ℕ)^4645*12500000000000^3621 ≤ 5411321711467^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603281887 5000000000 5411321711467 12500000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267597329/500000000 : ℝ), (-1897865083/10000000000 : ℝ), (2603281887/5000000000 : ℝ)] ![(22423650320771/50000000000000 : ℝ), (11862125645609/100000000000000 : ℝ), (5411321711467/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267597329/500000000 : ℝ)|^4645 ≤ (22423650320771/50000000000000 : ℝ)^3621
        have hw : |(267597329/500000000 : ℝ)|=(267597329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1897865083/10000000000 : ℝ)|^4645 ≤ (11862125645609/100000000000000 : ℝ)^3621
        have hw : |(-1897865083/10000000000 : ℝ)|=(1897865083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603281887/5000000000 : ℝ)|^4645 ≤ (5411321711467/12500000000000 : ℝ)^3621
        have hw : |(2603281887/5000000000 : ℝ)|=(2603281887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_2 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351946937/10000000000 : ℝ)*x 0 + (1301640891/2500000000 : ℝ)*x 1 + (-474466221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351946937/10000000000 : ℝ)^4645 ≤ (2802956529941/6250000000000 : ℝ)^3621 := by
    have hnat : (5351946937 : ℕ)^4645*6250000000000^3621 ≤ 2802956529941^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351946937 10000000000 2802956529941 6250000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1301640891/2500000000 : ℝ)^4645 ≤ (43290571451887/100000000000000 : ℝ)^3621 := by
    have hnat : (1301640891 : ℕ)^4645*100000000000000^3621 ≤ 43290571451887^3621*2500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301640891 2500000000 43290571451887 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474466221/2500000000 : ℝ)^4645 ≤ (1186212405007/10000000000000 : ℝ)^3621 := by
    have hnat : (474466221 : ℕ)^4645*10000000000000^3621 ≤ 1186212405007^3621*2500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474466221 2500000000 1186212405007 10000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351946937/10000000000 : ℝ), (1301640891/2500000000 : ℝ), (-474466221/2500000000 : ℝ)] ![(2802956529941/6250000000000 : ℝ), (43290571451887/100000000000000 : ℝ), (1186212405007/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351946937/10000000000 : ℝ)|^4645 ≤ (2802956529941/6250000000000 : ℝ)^3621
        have hw : |(5351946937/10000000000 : ℝ)|=(5351946937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1301640891/2500000000 : ℝ)|^4645 ≤ (43290571451887/100000000000000 : ℝ)^3621
        have hw : |(1301640891/2500000000 : ℝ)|=(1301640891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474466221/2500000000 : ℝ)|^4645 ≤ (1186212405007/10000000000000 : ℝ)^3621
        have hw : |(-474466221/2500000000 : ℝ)|=(474466221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_3 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848046439/2000000000 : ℝ)*x 0 + (1985358151/5000000000 : ℝ)*x 1 + (4524326239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848046439/2000000000 : ℝ)^4645 ≤ (1663364268891/5000000000000 : ℝ)^3621 := by
    have hnat : (848046439 : ℕ)^4645*5000000000000^3621 ≤ 1663364268891^3621*2000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848046439 2000000000 1663364268891 5000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1985358151/5000000000 : ℝ)^4645 ≤ (30579547511849/100000000000000 : ℝ)^3621 := by
    have hnat : (1985358151 : ℕ)^4645*100000000000000^3621 ≤ 30579547511849^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985358151 5000000000 30579547511849 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524326239/10000000000 : ℝ)^4645 ≤ (36153167095239/100000000000000 : ℝ)^3621 := by
    have hnat : (4524326239 : ℕ)^4645*100000000000000^3621 ≤ 36153167095239^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524326239 10000000000 36153167095239 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848046439/2000000000 : ℝ), (1985358151/5000000000 : ℝ), (4524326239/10000000000 : ℝ)] ![(1663364268891/5000000000000 : ℝ), (30579547511849/100000000000000 : ℝ), (36153167095239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848046439/2000000000 : ℝ)|^4645 ≤ (1663364268891/5000000000000 : ℝ)^3621
        have hw : |(848046439/2000000000 : ℝ)|=(848046439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1985358151/5000000000 : ℝ)|^4645 ≤ (30579547511849/100000000000000 : ℝ)^3621
        have hw : |(1985358151/5000000000 : ℝ)|=(1985358151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524326239/10000000000 : ℝ)|^4645 ≤ (36153167095239/100000000000000 : ℝ)^3621
        have hw : |(4524326239/10000000000 : ℝ)|=(4524326239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_4 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-888940219/5000000000 : ℝ)*x 0 + (2603976837/5000000000 : ℝ)*x 1 + (2719525097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888940219/5000000000 : ℝ)^4645 ≤ (10908847922987/100000000000000 : ℝ)^3621 := by
    have hnat : (888940219 : ℕ)^4645*100000000000000^3621 ≤ 10908847922987^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888940219 5000000000 10908847922987 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603976837/5000000000 : ℝ)^4645 ≤ (43305398848313/100000000000000 : ℝ)^3621 := by
    have hnat : (2603976837 : ℕ)^4645*100000000000000^3621 ≤ 43305398848313^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603976837 5000000000 43305398848313 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719525097/5000000000 : ℝ)^4645 ≤ (45785753215929/100000000000000 : ℝ)^3621 := by
    have hnat : (2719525097 : ℕ)^4645*100000000000000^3621 ≤ 45785753215929^3621*5000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719525097 5000000000 45785753215929 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-888940219/5000000000 : ℝ), (2603976837/5000000000 : ℝ), (2719525097/5000000000 : ℝ)] ![(10908847922987/100000000000000 : ℝ), (43305398848313/100000000000000 : ℝ), (45785753215929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-888940219/5000000000 : ℝ)|^4645 ≤ (10908847922987/100000000000000 : ℝ)^3621
        have hw : |(-888940219/5000000000 : ℝ)|=(888940219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603976837/5000000000 : ℝ)|^4645 ≤ (43305398848313/100000000000000 : ℝ)^3621
        have hw : |(2603976837/5000000000 : ℝ)|=(2603976837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719525097/5000000000 : ℝ)|^4645 ≤ (45785753215929/100000000000000 : ℝ)^3621
        have hw : |(2719525097/5000000000 : ℝ)|=(2719525097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_5 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322507937/2500000000 : ℝ)*x 0 + (-1665378941/10000000000 : ℝ)*x 1 + (5439051159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322507937/2500000000 : ℝ)^4645 ≤ (4418284887321/10000000000000 : ℝ)^3621 := by
    have hnat : (1322507937 : ℕ)^4645*10000000000000^3621 ≤ 4418284887321^3621*2500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322507937 2500000000 4418284887321 10000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1665378941/10000000000 : ℝ)^4645 ≤ (313480858871/3125000000000 : ℝ)^3621 := by
    have hnat : (1665378941 : ℕ)^4645*3125000000000^3621 ≤ 313480858871^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665378941 10000000000 313480858871 3125000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439051159/10000000000 : ℝ)^4645 ≤ (45785763636507/100000000000000 : ℝ)^3621 := by
    have hnat : (5439051159 : ℕ)^4645*100000000000000^3621 ≤ 45785763636507^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439051159 10000000000 45785763636507 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322507937/2500000000 : ℝ), (-1665378941/10000000000 : ℝ), (5439051159/10000000000 : ℝ)] ![(4418284887321/10000000000000 : ℝ), (313480858871/3125000000000 : ℝ), (45785763636507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322507937/2500000000 : ℝ)|^4645 ≤ (4418284887321/10000000000000 : ℝ)^3621
        have hw : |(1322507937/2500000000 : ℝ)|=(1322507937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1665378941/10000000000 : ℝ)|^4645 ≤ (313480858871/3125000000000 : ℝ)^3621
        have hw : |(-1665378941/10000000000 : ℝ)|=(1665378941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439051159/10000000000 : ℝ)|^4645 ≤ (45785763636507/100000000000000 : ℝ)^3621
        have hw : |(5439051159/10000000000 : ℝ)|=(5439051159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_6 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290032151/10000000000 : ℝ)*x 0 + (5439052271/10000000000 : ℝ)*x 1 + (-416344207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290032151/10000000000 : ℝ)^4645 ≤ (22091426595481/50000000000000 : ℝ)^3621 := by
    have hnat : (5290032151 : ℕ)^4645*50000000000000^3621 ≤ 22091426595481^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290032151 10000000000 22091426595481 50000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439052271/10000000000 : ℝ)^4645 ≤ (45785775644469/100000000000000 : ℝ)^3621 := by
    have hnat : (5439052271 : ℕ)^4645*100000000000000^3621 ≤ 45785775644469^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439052271 10000000000 45785775644469 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416344207/2500000000 : ℝ)^4645 ≤ (10031371156941/100000000000000 : ℝ)^3621 := by
    have hnat : (416344207 : ℕ)^4645*100000000000000^3621 ≤ 10031371156941^3621*2500000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416344207 2500000000 10031371156941 100000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290032151/10000000000 : ℝ), (5439052271/10000000000 : ℝ), (-416344207/2500000000 : ℝ)] ![(22091426595481/50000000000000 : ℝ), (45785775644469/100000000000000 : ℝ), (10031371156941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290032151/10000000000 : ℝ)|^4645 ≤ (22091426595481/50000000000000 : ℝ)^3621
        have hw : |(5290032151/10000000000 : ℝ)|=(5290032151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439052271/10000000000 : ℝ)|^4645 ≤ (45785775644469/100000000000000 : ℝ)^3621
        have hw : |(5439052271/10000000000 : ℝ)|=(5439052271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416344207/2500000000 : ℝ)|^4645 ≤ (10031371156941/100000000000000 : ℝ)^3621
        have hw : |(-416344207/2500000000 : ℝ)|=(416344207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1574_s2_7 (p : ℝ) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265020321/625000000 : ℝ)*x 0 + (4521038129/10000000000 : ℝ)*x 1 + (3974032621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265020321/625000000 : ℝ)^4645 ≤ (831705519243/2500000000000 : ℝ)^3621 := by
    have hnat : (265020321 : ℕ)^4645*2500000000000^3621 ≤ 831705519243^3621*625000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265020321 625000000 831705519243 2500000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521038129/10000000000 : ℝ)^4645 ≤ (7223893086513/20000000000000 : ℝ)^3621 := by
    have hnat : (4521038129 : ℕ)^4645*20000000000000^3621 ≤ 7223893086513^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521038129 10000000000 7223893086513 20000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3974032621/10000000000 : ℝ)^4645 ≤ (6122462755727/20000000000000 : ℝ)^3621 := by
    have hnat : (3974032621 : ℕ)^4645*20000000000000^3621 ≤ 6122462755727^3621*10000000000^4645 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3974032621 10000000000 6122462755727 20000000000000 4645 3621 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4645/1024 : ℝ)) 4645 3621 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265020321/625000000 : ℝ), (4521038129/10000000000 : ℝ), (3974032621/10000000000 : ℝ)] ![(831705519243/2500000000000 : ℝ), (7223893086513/20000000000000 : ℝ), (6122462755727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265020321/625000000 : ℝ)|^4645 ≤ (831705519243/2500000000000 : ℝ)^3621
        have hw : |(265020321/625000000 : ℝ)|=(265020321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521038129/10000000000 : ℝ)|^4645 ≤ (7223893086513/20000000000000 : ℝ)^3621
        have hw : |(4521038129/10000000000 : ℝ)|=(4521038129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3974032621/10000000000 : ℝ)|^4645 ≤ (6122462755727/20000000000000 : ℝ)^3621
        have hw : |(3974032621/10000000000 : ℝ)|=(3974032621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1574_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5421/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15801/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4557/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4557/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4557/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4557/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4557/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4557/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4557/50000 : ℝ) ^ (4643/1024 : ℝ) ≤ (959629948164897/50000000000000000000 : ℝ) := by
    have hpowers : (4557/50000 : ℝ)^4643 ≤ (959629948164897/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4557 : ℕ)^4643*50000000000000000000^1024 ≤ 959629948164897^1024*50000^4643 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4557 50000 959629948164897 50000000000000000000 4643 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4557/50000 : ℝ)) (X := (959629948164897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17719/100000 : ℝ) ^ (4643/1024 : ℝ) ≤ (39110045718845921/100000000000000000000 : ℝ) := by
    have hpowers : (17719/100000 : ℝ)^4643 ≤ (39110045718845921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17719 : ℕ)^4643*100000000000000000000^1024 ≤ 39110045718845921^1024*100000^4643 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17719 100000 39110045718845921 100000000000000000000 4643 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17719/100000 : ℝ)) (X := (39110045718845921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000959629948164897/25000000000000000000 : ℝ) ≤ (5000042328079557/5000000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (25000959629948164897/25000000000000000000 : ℝ)^1024 ≤ (5000042328079557/5000000000000000 : ℝ)^4643 := by
      have hnat : (25000959629948164897 : ℕ)^1024*5000000000000000^4643 ≤ 5000042328079557^4643*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000959629948164897 25000000000000000000 5000042328079557 5000000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042328079557/5000000000000000 : ℝ)) (X := (25000959629948164897/25000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008205861123035143/20000000000000000000 : ℝ) ≤ (10000904744614639/10000000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (20008205861123035143/20000000000000000000 : ℝ)^1024 ≤ (10000904744614639/10000000000000000 : ℝ)^4643 := by
      have hnat : (20008205861123035143 : ℕ)^1024*10000000000000000^4643 ≤ 10000904744614639^4643*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008205861123035143 20000000000000000000 10000904744614639 10000000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000904744614639/10000000000000000 : ℝ)) (X := (20008205861123035143/20000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039110045718845921/50000000000000000000 : ℝ) ≤ (2500431208267541/2500000000000000 : ℝ) ^ (4643/1024 : ℝ) := by
    have hpowers : (50039110045718845921/50000000000000000000 : ℝ)^1024 ≤ (2500431208267541/2500000000000000 : ℝ)^4643 := by
      have hnat : (50039110045718845921 : ℕ)^1024*2500000000000000^4643 ≤ 2500431208267541^4643*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039110045718845921 50000000000000000000 2500431208267541 2500000000000000 1024 4643 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500431208267541/2500000000000000 : ℝ)) (X := (50039110045718845921/50000000000000000000 : ℝ)) (by norm_num) 4643 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(959629948164897/50000000000000000000 : ℝ) ≤ ((8603577989388186627/8605000000000000000 : ℝ)+2*(32803538221/34420000000000 : ℝ)*(4557/50000 : ℝ))^(4643/1024 : ℝ) := by
    rw [show (8603577989388186627/8605000000000000000 : ℝ)+2*(32803538221/34420000000000 : ℝ)*(4557/50000 : ℝ)=(5000042328079557/5000000000000000 : ℝ) by norm_num, show 1+2*(959629948164897/50000000000000000000 : ℝ)=(25000959629948164897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39110045718845921/100000000000000000000 : ℝ)+(959629948164897/50000000000000000000 : ℝ) ≤ ((8603577989388186627/8605000000000000000 : ℝ)+(32803538221/34420000000000 : ℝ)*((17719/100000 : ℝ)+(4557/50000 : ℝ)))^(4643/1024 : ℝ) := by
    rw [show (8603577989388186627/8605000000000000000 : ℝ)+(32803538221/34420000000000 : ℝ)*((17719/100000 : ℝ)+(4557/50000 : ℝ))=(10000904744614639/10000000000000000 : ℝ) by norm_num, show 1+(39110045718845921/100000000000000000000 : ℝ)+(959629948164897/50000000000000000000 : ℝ)=(20008205861123035143/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39110045718845921/100000000000000000000 : ℝ) ≤ ((8603577989388186627/8605000000000000000 : ℝ)+2*(32803538221/34420000000000 : ℝ)*(17719/100000 : ℝ))^(4643/1024 : ℝ) := by
    rw [show (8603577989388186627/8605000000000000000 : ℝ)+2*(32803538221/34420000000000 : ℝ)*(17719/100000 : ℝ)=(2500431208267541/2500000000000000 : ℝ) by norm_num, show 1+2*(39110045718845921/100000000000000000000 : ℝ)=(50039110045718845921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8603577989388186627/8605000000000000000 : ℝ)*(X 1 0+X 2 0)+(32803538221/34420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (4557/50000 : ℝ)) (hi := (17719/100000 : ℝ)) (c := (8603577989388186627/8605000000000000000 : ℝ)) (alpha := (32803538221/34420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8603577989388186627/8605000000000000000 : ℝ)*(X 0 1+X 2 1)+(32803538221/34420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (4557/50000 : ℝ)) (hi := (17719/100000 : ℝ)) (c := (8603577989388186627/8605000000000000000 : ℝ)) (alpha := (32803538221/34420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8603577989388186627/8605000000000000000 : ℝ)*(X 0 2+X 1 2)+(32803538221/34420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4643/1024 : ℝ)) (lo := (4557/50000 : ℝ)) (hi := (17719/100000 : ℝ)) (c := (8603577989388186627/8605000000000000000 : ℝ)) (alpha := (32803538221/34420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88892089/500000000 : ℝ)*X 0 0+(2720225443/5000000000 : ℝ)*X 0 1+(5206564099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267597329/500000000 : ℝ)*X 1 0+(-1897865083/10000000000 : ℝ)*X 1 1+(2603281887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351946937/10000000000 : ℝ)*X 2 0+(1301640891/2500000000 : ℝ)*X 2 1+(-474466221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((848046439/2000000000 : ℝ)*X 0 0+(1985358151/5000000000 : ℝ)*X 0 1+(4524326239/10000000000 : ℝ)*X 0 2+(848046439/2000000000 : ℝ)*X 1 0+(1985358151/5000000000 : ℝ)*X 1 1+(4524326239/10000000000 : ℝ)*X 1 2+(848046439/2000000000 : ℝ)*X 2 0+(1985358151/5000000000 : ℝ)*X 2 1+(4524326239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-888940219/5000000000 : ℝ)*X 0 0+(2603976837/5000000000 : ℝ)*X 0 1+(2719525097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322507937/2500000000 : ℝ)*X 1 0+(-1665378941/10000000000 : ℝ)*X 1 1+(5439051159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290032151/10000000000 : ℝ)*X 2 0+(5439052271/10000000000 : ℝ)*X 2 1+(-416344207/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265020321/625000000 : ℝ)*X 0 0+(4521038129/10000000000 : ℝ)*X 0 1+(3974032621/10000000000 : ℝ)*X 0 2+(265020321/625000000 : ℝ)*X 1 0+(4521038129/10000000000 : ℝ)*X 1 1+(3974032621/10000000000 : ℝ)*X 1 2+(265020321/625000000 : ℝ)*X 2 0+(4521038129/10000000000 : ℝ)*X 2 1+(3974032621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1574_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1401645054989957812289594907/215125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1178783639/100000000000000 : ℝ)*(base19) + (279638483/20000000000000 : ℝ)*(base23) + (48123363/50000000000000 : ℝ)*(upper3) + (8803063/25000000000000 : ℝ)*(upper4) + (276542457/100000000000000 : ℝ)*(upper5) + (1520483051046849/50000000000000 : ℝ)*(major0) + (1520483051046849/50000000000000 : ℝ)*(major1) + (1520483051046849/50000000000000 : ℝ)*(major2) + (2137789916205389/50000000000000 : ℝ)*(sp0) + (267224552568407/6250000000000 : ℝ)*(sp1) + (534449077710717/12500000000000 : ℝ)*(sp2) + (1806332413437717/100000000000000 : ℝ)*(sp3) + (14187467373/100000000000000 : ℝ)*(sp4) + (2776844239/50000000000000 : ℝ)*(sp7) + (903168983563097/50000000000000 : ℝ)*(f.failure) + (4275594019878151/100000000000000 : ℝ)*(f.sum) + (9230178283831/1721000000000000000000000000 : ℝ)*base66 + (5931064881516961677/430250000000000000000000000000000 : ℝ)*base68 + (6957300915656711677/430250000000000000000000000000000 : ℝ)*base70 + (5391610064346211677/430250000000000000000000000000000 : ℝ)*base72 + (2889604294221/860500000000000000000000000 : ℝ)*base74 + (4311103751602711677/430250000000000000000000000000000 : ℝ)*base76 + (4361859038724211677/430250000000000000000000000000000 : ℝ)*base78 + (1912355799785461677/430250000000000000000000000000000 : ℝ)*base80 + (8996251303759/1721000000000000000000000000 : ℝ)*base82 + (1276379/2500000000000000000000 : ℝ)*base90 + (1276379/2500000000000000000000 : ℝ)*base92 + (1276379/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10837485790389269662107/1721000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16103289/25000000000000 : ℝ)*(base8) + (38329321/5000000000000 : ℝ)*(base15) + (105294371/100000000000000 : ℝ)*(lower2) + (1343249/2000000000000 : ℝ)*(lower4) + (384708247041307/12500000000000 : ℝ)*(major0) + (384708247041307/12500000000000 : ℝ)*(major1) + (384708247041307/12500000000000 : ℝ)*(major2) + (1533785721/100000000000000 : ℝ)*(sp1) + (4730335771/12500000000000 : ℝ)*(sp2) + (1807084343/100000000000000 : ℝ)*(sp3) + (432719393640739/10000000000000 : ℝ)*(sp4) + (1081797925112101/25000000000000 : ℝ)*(sp5) + (4327156158134377/100000000000000 : ℝ)*(sp6) + (914067967424631/50000000000000 : ℝ)*(sp7) + (365627548386721/20000000000000 : ℝ)*(f.failure) + (2163597000410273/50000000000000 : ℝ)*(f.sum) + (14140361924239/1721000000000000000000000000 : ℝ)*base65 + (845419615651998511/107562500000000000000000000000000 : ℝ)*base68 + (214064115129563989/107562500000000000000000000000000 : ℝ)*base69 + (315807317157688989/107562500000000000000000000000000 : ℝ)*base71 + (2745630079959/1721000000000000000000000000 : ℝ)*base73 + (473307332447311011/107562500000000000000000000000000 : ℝ)*base76 + (75565616027001489/107562500000000000000000000000000 : ℝ)*base77 + (353789296498186011/107562500000000000000000000000000 : ℝ)*base80 + (156400481769/344200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2795853/1000000000000000000000 : ℝ)*base89 + (2795853/1000000000000000000000 : ℝ)*base91 + (2795853/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1574_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4557/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5421/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15801/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1574_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1574_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5421/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15801/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1574_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1574_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1574_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4643/1024 : ℝ) ≤ p) (hpb : p ≤ (4645/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84174893/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5421/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15801/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1574_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

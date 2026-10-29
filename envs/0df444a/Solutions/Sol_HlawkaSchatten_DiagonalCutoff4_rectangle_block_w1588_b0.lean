-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1588_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:16.404997+00:00
-- url     : https://prove2.me/submissions/533eac48-06f6-4047-af37-84be15a3ba5f

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
theorem support_rectangle_w1588_s0_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1608108441/10000000000 : ℝ)*x 0 + (1171332067/2000000000 : ℝ)*x 1 + (4886498727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1608108441/10000000000 : ℝ)^4673 ≤ (2407286143961/25000000000000 : ℝ)^3649 := by
    have hnat : (1608108441 : ℕ)^4673*25000000000000^3649 ≤ 2407286143961^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608108441 10000000000 2407286143961 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1171332067/2000000000 : ℝ)^4673 ≤ (25200947702733/50000000000000 : ℝ)^3649 := by
    have hnat : (1171332067 : ℕ)^4673*50000000000000^3649 ≤ 25200947702733^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171332067 2000000000 25200947702733 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886498727/10000000000 : ℝ)^4673 ≤ (39968960005797/100000000000000 : ℝ)^3649 := by
    have hnat : (4886498727 : ℕ)^4673*100000000000000^3649 ≤ 39968960005797^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886498727 10000000000 39968960005797 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1608108441/10000000000 : ℝ), (1171332067/2000000000 : ℝ), (4886498727/10000000000 : ℝ)] ![(2407286143961/25000000000000 : ℝ), (25200947702733/50000000000000 : ℝ), (39968960005797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1608108441/10000000000 : ℝ)|^4673 ≤ (2407286143961/25000000000000 : ℝ)^3649
        have hw : |(-1608108441/10000000000 : ℝ)|=(1608108441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1171332067/2000000000 : ℝ)|^4673 ≤ (25200947702733/50000000000000 : ℝ)^3649
        have hw : |(1171332067/2000000000 : ℝ)|=(1171332067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886498727/10000000000 : ℝ)|^4673 ≤ (39968960005797/100000000000000 : ℝ)^3649
        have hw : |(4886498727/10000000000 : ℝ)|=(4886498727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092330419/2000000000 : ℝ)*x 0 + (-1073412591/5000000000 : ℝ)*x 1 + (4886498589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092330419/2000000000 : ℝ)^4673 ≤ (5761302078143/12500000000000 : ℝ)^3649 := by
    have hnat : (1092330419 : ℕ)^4673*12500000000000^3649 ≤ 5761302078143^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092330419 2000000000 5761302078143 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073412591/5000000000 : ℝ)^4673 ≤ (13940624806213/100000000000000 : ℝ)^3649 := by
    have hnat : (1073412591 : ℕ)^4673*100000000000000^3649 ≤ 13940624806213^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073412591 5000000000 13940624806213 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886498589/10000000000 : ℝ)^4673 ≤ (3996895856027/10000000000000 : ℝ)^3649 := by
    have hnat : (4886498589 : ℕ)^4673*10000000000000^3649 ≤ 3996895856027^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886498589 10000000000 3996895856027 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092330419/2000000000 : ℝ), (-1073412591/5000000000 : ℝ), (4886498589/10000000000 : ℝ)] ![(5761302078143/12500000000000 : ℝ), (13940624806213/100000000000000 : ℝ), (3996895856027/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092330419/2000000000 : ℝ)|^4673 ≤ (5761302078143/12500000000000 : ℝ)^3649
        have hw : |(1092330419/2000000000 : ℝ)|=(1092330419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1073412591/5000000000 : ℝ)|^4673 ≤ (13940624806213/100000000000000 : ℝ)^3649
        have hw : |(-1073412591/5000000000 : ℝ)|=(1073412591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886498589/10000000000 : ℝ)|^4673 ≤ (3996895856027/10000000000000 : ℝ)^3649
        have hw : |(4886498589/10000000000 : ℝ)|=(4886498589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2730826081/5000000000 : ℝ)*x 0 + (195459939/400000000 : ℝ)*x 1 + (-1073412619/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2730826081/5000000000 : ℝ)^4673 ≤ (46090417349219/100000000000000 : ℝ)^3649 := by
    have hnat : (2730826081 : ℕ)^4673*100000000000000^3649 ≤ 46090417349219^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730826081 5000000000 46090417349219 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195459939/400000000 : ℝ)^4673 ≤ (1998447868307/5000000000000 : ℝ)^3649 := by
    have hnat : (195459939 : ℕ)^4673*5000000000000^3649 ≤ 1998447868307^3649*400000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195459939 400000000 1998447868307 5000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073412619/5000000000 : ℝ)^4673 ≤ (6970312635951/50000000000000 : ℝ)^3649 := by
    have hnat : (1073412619 : ℕ)^4673*50000000000000^3649 ≤ 6970312635951^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073412619 5000000000 6970312635951 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2730826081/5000000000 : ℝ), (195459939/400000000 : ℝ), (-1073412619/5000000000 : ℝ)] ![(46090417349219/100000000000000 : ℝ), (1998447868307/5000000000000 : ℝ), (6970312635951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2730826081/5000000000 : ℝ)|^4673 ≤ (46090417349219/100000000000000 : ℝ)^3649
        have hw : |(2730826081/5000000000 : ℝ)|=(2730826081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195459939/400000000 : ℝ)|^4673 ≤ (1998447868307/5000000000000 : ℝ)^3649
        have hw : |(195459939/400000000 : ℝ)|=(195459939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073412619/5000000000 : ℝ)|^4673 ≤ (6970312635951/50000000000000 : ℝ)^3649
        have hw : |(-1073412619/5000000000 : ℝ)|=(1073412619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (25782721/62500000 : ℝ)*x 0 + (618856499/2000000000 : ℝ)*x 1 + (5412518027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25782721/62500000 : ℝ)^4673 ≤ (6435230296933/20000000000000 : ℝ)^3649 := by
    have hnat : (25782721 : ℕ)^4673*20000000000000^3649 ≤ 6435230296933^3649*62500000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25782721 62500000 6435230296933 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618856499/2000000000 : ℝ)^4673 ≤ (695742379639/3125000000000 : ℝ)^3649 := by
    have hnat : (618856499 : ℕ)^4673*3125000000000^3649 ≤ 695742379639^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618856499 2000000000 695742379639 3125000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412518027/10000000000 : ℝ)^4673 ≤ (5695011543799/12500000000000 : ℝ)^3649 := by
    have hnat : (5412518027 : ℕ)^4673*12500000000000^3649 ≤ 5695011543799^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412518027 10000000000 5695011543799 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(25782721/62500000 : ℝ), (618856499/2000000000 : ℝ), (5412518027/10000000000 : ℝ)] ![(6435230296933/20000000000000 : ℝ), (695742379639/3125000000000 : ℝ), (5695011543799/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(25782721/62500000 : ℝ)|^4673 ≤ (6435230296933/20000000000000 : ℝ)^3649
        have hw : |(25782721/62500000 : ℝ)|=(25782721/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(618856499/2000000000 : ℝ)|^4673 ≤ (695742379639/3125000000000 : ℝ)^3649
        have hw : |(618856499/2000000000 : ℝ)|=(618856499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412518027/10000000000 : ℝ)|^4673 ≤ (5695011543799/12500000000000 : ℝ)^3649
        have hw : |(5412518027/10000000000 : ℝ)|=(5412518027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-322205917/2000000000 : ℝ)*x 0 + (306927987/625000000 : ℝ)*x 1 + (1166290683/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322205917/2000000000 : ℝ)^4673 ≤ (2412887560879/25000000000000 : ℝ)^3649 := by
    have hnat : (322205917 : ℕ)^4673*25000000000000^3649 ≤ 2412887560879^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322205917 2000000000 2412887560879 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306927987/625000000 : ℝ)^4673 ≤ (2011209521463/5000000000000 : ℝ)^3649 := by
    have hnat : (306927987 : ℕ)^4673*5000000000000^3649 ≤ 2011209521463^3649*625000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306927987 625000000 2011209521463 5000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166290683/2000000000 : ℝ)^4673 ≤ (6265532415137/12500000000000 : ℝ)^3649 := by
    have hnat : (1166290683 : ℕ)^4673*12500000000000^3649 ≤ 6265532415137^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166290683 2000000000 6265532415137 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-322205917/2000000000 : ℝ), (306927987/625000000 : ℝ), (1166290683/2000000000 : ℝ)] ![(2412887560879/25000000000000 : ℝ), (2011209521463/5000000000000 : ℝ), (6265532415137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-322205917/2000000000 : ℝ)|^4673 ≤ (2412887560879/25000000000000 : ℝ)^3649
        have hw : |(-322205917/2000000000 : ℝ)|=(322205917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(306927987/625000000 : ℝ)|^4673 ≤ (2011209521463/5000000000000 : ℝ)^3649
        have hw : |(306927987/625000000 : ℝ)|=(306927987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1166290683/2000000000 : ℝ)|^4673 ≤ (6265532415137/12500000000000 : ℝ)^3649
        have hw : |(1166290683/2000000000 : ℝ)|=(1166290683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64955219/125000000 : ℝ)*x 0 + (-1201869943/10000000000 : ℝ)*x 1 + (1166290701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64955219/125000000 : ℝ)^4673 ≤ (1729750736269/4000000000000 : ℝ)^3649 := by
    have hnat : (64955219 : ℕ)^4673*4000000000000^3649 ≤ 1729750736269^3649*125000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64955219 125000000 1729750736269 4000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201869943/10000000000 : ℝ)^4673 ≤ (6631971260737/100000000000000 : ℝ)^3649 := by
    have hnat : (1201869943 : ℕ)^4673*100000000000000^3649 ≤ 6631971260737^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201869943 10000000000 6631971260737 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166290701/2000000000 : ℝ)^4673 ≤ (50124260311781/100000000000000 : ℝ)^3649 := by
    have hnat : (1166290701 : ℕ)^4673*100000000000000^3649 ≤ 50124260311781^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166290701 2000000000 50124260311781 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64955219/125000000 : ℝ), (-1201869943/10000000000 : ℝ), (1166290701/2000000000 : ℝ)] ![(1729750736269/4000000000000 : ℝ), (6631971260737/100000000000000 : ℝ), (50124260311781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64955219/125000000 : ℝ)|^4673 ≤ (1729750736269/4000000000000 : ℝ)^3649
        have hw : |(64955219/125000000 : ℝ)|=(64955219/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1201869943/10000000000 : ℝ)|^4673 ≤ (6631971260737/100000000000000 : ℝ)^3649
        have hw : |(-1201869943/10000000000 : ℝ)|=(1201869943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1166290701/2000000000 : ℝ)|^4673 ≤ (50124260311781/100000000000000 : ℝ)^3649
        have hw : |(1166290701/2000000000 : ℝ)|=(1166290701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519641749/1000000000 : ℝ)*x 0 + (5831453403/10000000000 : ℝ)*x 1 + (-1201870147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519641749/1000000000 : ℝ)^4673 ≤ (4324376808701/10000000000000 : ℝ)^3649 := by
    have hnat : (519641749 : ℕ)^4673*10000000000000^3649 ≤ 4324376808701^3649*1000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519641749 1000000000 4324376808701 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5831453403/10000000000 : ℝ)^4673 ≤ (10024851837801/20000000000000 : ℝ)^3649 := by
    have hnat : (5831453403 : ℕ)^4673*20000000000000^3649 ≤ 10024851837801^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5831453403 10000000000 10024851837801 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201870147/10000000000 : ℝ)^4673 ≤ (828996587789/12500000000000 : ℝ)^3649 := by
    have hnat : (1201870147 : ℕ)^4673*12500000000000^3649 ≤ 828996587789^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201870147 10000000000 828996587789 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519641749/1000000000 : ℝ), (5831453403/10000000000 : ℝ), (-1201870147/10000000000 : ℝ)] ![(4324376808701/10000000000000 : ℝ), (10024851837801/20000000000000 : ℝ), (828996587789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519641749/1000000000 : ℝ)|^4673 ≤ (4324376808701/10000000000000 : ℝ)^3649
        have hw : |(519641749/1000000000 : ℝ)|=(519641749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5831453403/10000000000 : ℝ)|^4673 ≤ (10024851837801/20000000000000 : ℝ)^3649
        have hw : |(5831453403/10000000000 : ℝ)|=(5831453403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1201870147/10000000000 : ℝ)|^4673 ≤ (828996587789/12500000000000 : ℝ)^3649
        have hw : |(-1201870147/10000000000 : ℝ)|=(1201870147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s0_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (826443203/2000000000 : ℝ)*x 0 + (1338583687/2500000000 : ℝ)*x 1 + (630902997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826443203/2000000000 : ℝ)^4673 ≤ (16122947715777/50000000000000 : ℝ)^3649 := by
    have hnat : (826443203 : ℕ)^4673*50000000000000^3649 ≤ 16122947715777^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826443203 2000000000 16122947715777 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338583687/2500000000 : ℝ)^4673 ≤ (44933841830057/100000000000000 : ℝ)^3649 := by
    have hnat : (1338583687 : ℕ)^4673*100000000000000^3649 ≤ 44933841830057^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338583687 2500000000 44933841830057 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630902997/2000000000 : ℝ)^4673 ≤ (11410131361777/50000000000000 : ℝ)^3649 := by
    have hnat : (630902997 : ℕ)^4673*50000000000000^3649 ≤ 11410131361777^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630902997 2000000000 11410131361777 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(826443203/2000000000 : ℝ), (1338583687/2500000000 : ℝ), (630902997/2000000000 : ℝ)] ![(16122947715777/50000000000000 : ℝ), (44933841830057/100000000000000 : ℝ), (11410131361777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(826443203/2000000000 : ℝ)|^4673 ≤ (16122947715777/50000000000000 : ℝ)^3649
        have hw : |(826443203/2000000000 : ℝ)|=(826443203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1338583687/2500000000 : ℝ)|^4673 ≤ (44933841830057/100000000000000 : ℝ)^3649
        have hw : |(1338583687/2500000000 : ℝ)|=(1338583687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630902997/2000000000 : ℝ)|^4673 ≤ (11410131361777/50000000000000 : ℝ)^3649
        have hw : |(630902997/2000000000 : ℝ)|=(630902997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (751/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3067/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4671/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4671 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4671*1^1024 ≤ 0^1024*1^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4671/1024 : ℝ) ≤ (765168931854980447/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4671 ≤ (765168931854980447/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4671*50000000000000000000^1024 ≤ 765168931854980447^1024*5^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 765168931854980447 50000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (765168931854980447/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4671 := by
      have hnat : (1 : ℕ)^1024*1^4671 ≤ 1^4671*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50765168931854980447/50000000000000000000 : ℝ) ≤ (2006670041028179/2000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50765168931854980447/50000000000000000000 : ℝ)^1024 ≤ (2006670041028179/2000000000000000 : ℝ)^4671 := by
      have hnat : (50765168931854980447 : ℕ)^1024*2000000000000000^4671 ≤ 2006670041028179^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50765168931854980447 50000000000000000000 2006670041028179 2000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006670041028179/2000000000000000 : ℝ)) (X := (50765168931854980447/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25765168931854980447/25000000000000000000 : ℝ) ≤ (1006670041028179/1000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (25765168931854980447/25000000000000000000 : ℝ)^1024 ≤ (1006670041028179/1000000000000000 : ℝ)^4671 := by
      have hnat : (25765168931854980447 : ℕ)^1024*1000000000000000^4671 ≤ 1006670041028179^4671*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25765168931854980447 25000000000000000000 1006670041028179 1000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006670041028179/1000000000000000 : ℝ)) (X := (25765168931854980447/25000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6670041028179/800000000000000 : ℝ)*(0 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6670041028179/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(765168931854980447/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6670041028179/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6670041028179/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2006670041028179/2000000000000000 : ℝ) by norm_num, show 1+(765168931854980447/50000000000000000000 : ℝ)+(0 : ℝ)=(50765168931854980447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(765168931854980447/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6670041028179/800000000000000 : ℝ)*(2/5 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6670041028179/800000000000000 : ℝ)*(2/5 : ℝ)=(1006670041028179/1000000000000000 : ℝ) by norm_num, show 1+2*(765168931854980447/50000000000000000000 : ℝ)=(25765168931854980447/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6670041028179/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6670041028179/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6670041028179/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6670041028179/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6670041028179/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6670041028179/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1608108441/10000000000 : ℝ)*X 0 0+(1171332067/2000000000 : ℝ)*X 0 1+(4886498727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1092330419/2000000000 : ℝ)*X 1 0+(-1073412591/5000000000 : ℝ)*X 1 1+(4886498589/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2730826081/5000000000 : ℝ)*X 2 0+(195459939/400000000 : ℝ)*X 2 1+(-1073412619/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((25782721/62500000 : ℝ)*X 0 0+(618856499/2000000000 : ℝ)*X 0 1+(5412518027/10000000000 : ℝ)*X 0 2+(25782721/62500000 : ℝ)*X 1 0+(618856499/2000000000 : ℝ)*X 1 1+(5412518027/10000000000 : ℝ)*X 1 2+(25782721/62500000 : ℝ)*X 2 0+(618856499/2000000000 : ℝ)*X 2 1+(5412518027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-322205917/2000000000 : ℝ)*X 0 0+(306927987/625000000 : ℝ)*X 0 1+(1166290683/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((64955219/125000000 : ℝ)*X 1 0+(-1201869943/10000000000 : ℝ)*X 1 1+(1166290701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519641749/1000000000 : ℝ)*X 2 0+(5831453403/10000000000 : ℝ)*X 2 1+(-1201870147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((826443203/2000000000 : ℝ)*X 0 0+(1338583687/2500000000 : ℝ)*X 0 1+(630902997/2000000000 : ℝ)*X 0 2+(826443203/2000000000 : ℝ)*X 1 0+(1338583687/2500000000 : ℝ)*X 1 1+(630902997/2000000000 : ℝ)*X 1 2+(826443203/2000000000 : ℝ)*X 2 0+(1338583687/2500000000 : ℝ)*X 2 1+(630902997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1574098769904086994549/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6813601/12500000000000 : ℝ)*(base1) + (18379113/1562500000000 : ℝ)*(base19) + (1188907967/100000000000000 : ℝ)*(base23) + (77723171/50000000000000 : ℝ)*(upper3) + (707711/500000000000 : ℝ)*(upper5) + (9138318484809/1250000000000 : ℝ)*(major0) + (9138318484809/1250000000000 : ℝ)*(major1) + (9138318484809/1250000000000 : ℝ)*(major2) + (515380131156151/50000000000000 : ℝ)*(sp0) + (103076331931999/10000000000000 : ℝ)*(sp1) + (206152661335051/20000000000000 : ℝ)*(sp2) + (431364304075119/100000000000000 : ℝ)*(sp3) + (267986233/6250000000000 : ℝ)*(sp4) + (1893522451/100000000000000 : ℝ)*(sp7) + (215683126053189/50000000000000 : ℝ)*(f.failure) + (515382247791611/50000000000000 : ℝ)*(f.sum) + (908080838689/500000000000000000000000000 : ℝ)*base66 + (7147518566189/1000000000000000000000000000 : ℝ)*base68 + (2092156689189/1000000000000000000000000000 : ℝ)*base70 + (4554387222189/1000000000000000000000000000 : ℝ)*base72 + (3289338103689/500000000000000000000000000 : ℝ)*base74 + (2253840125189/1000000000000000000000000000 : ℝ)*base76 + (2698159482189/1000000000000000000000000000 : ℝ)*base78 + (3688152945189/1000000000000000000000000000 : ℝ)*base80 + (395753946189/500000000000000000000000000 : ℝ)*base82 + (5317077/625000000000000000000 : ℝ)*base89 + (5317077/625000000000000000000 : ℝ)*base91 + (5317077/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14939867904717359898687/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40928927/6250000000000 : ℝ)*(base19) + (130085029/20000000000000 : ℝ)*(base23) + (42516261/50000000000000 : ℝ)*(base32) + (1691677/1562500000000 : ℝ)*(upper3) + (751663/2000000000000 : ℝ)*(upper5) + (96301473207049/12500000000000 : ℝ)*(major0) + (96301473207049/12500000000000 : ℝ)*(major1) + (96301473207049/12500000000000 : ℝ)*(major2) + (923279263/50000000000000 : ℝ)*(sp1) + (470619369/25000000000000 : ℝ)*(sp2) + (543120436923097/50000000000000 : ℝ)*(sp4) + (271559593106209/25000000000000 : ℝ)*(sp5) + (1086238340943573/100000000000000 : ℝ)*(sp6) + (227291256417471/50000000000000 : ℝ)*(sp7) + (90916519573493/20000000000000 : ℝ)*(f.failure) + (543120436923097/50000000000000 : ℝ)*(f.sum) + (1980777233771/5000000000000000000000000000 : ℝ)*base65 + (34615827793771/10000000000000000000000000000 : ℝ)*base67 + (18034073366229/10000000000000000000000000000 : ℝ)*base70 + (53722837766229/10000000000000000000000000000 : ℝ)*base72 + (38180217753771/5000000000000000000000000000 : ℝ)*base73 + (66635248206229/10000000000000000000000000000 : ℝ)*base76 + (31827399686229/10000000000000000000000000000 : ℝ)*base78 + (28835915916229/10000000000000000000000000000 : ℝ)*base80 + (18897253678771/5000000000000000000000000000 : ℝ)*base81 + (2793349/250000000000000000000 : ℝ)*base89 + (2793349/250000000000000000000 : ℝ)*base91 + (2793349/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1588_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (751/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3067/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1588_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1588_s1_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742218729/10000000000 : ℝ)*x 0 + (5524857169/10000000000 : ℝ)*x 1 + (5131776263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742218729/10000000000 : ℝ)^4673 ≤ (5334666218493/50000000000000 : ℝ)^3649 := by
    have hnat : (1742218729 : ℕ)^4673*50000000000000^3649 ≤ 5334666218493^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742218729 10000000000 5334666218493 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5524857169/10000000000 : ℝ)^4673 ≤ (46774585229199/100000000000000 : ℝ)^3649 := by
    have hnat : (5524857169 : ℕ)^4673*100000000000000^3649 ≤ 46774585229199^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5524857169 10000000000 46774585229199 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131776263/10000000000 : ℝ)^4673 ≤ (340448658583/800000000000 : ℝ)^3649 := by
    have hnat : (5131776263 : ℕ)^4673*800000000000^3649 ≤ 340448658583^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131776263 10000000000 340448658583 800000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742218729/10000000000 : ℝ), (5524857169/10000000000 : ℝ), (5131776263/10000000000 : ℝ)] ![(5334666218493/50000000000000 : ℝ), (46774585229199/100000000000000 : ℝ), (340448658583/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742218729/10000000000 : ℝ)|^4673 ≤ (5334666218493/50000000000000 : ℝ)^3649
        have hw : |(-1742218729/10000000000 : ℝ)|=(1742218729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5524857169/10000000000 : ℝ)|^4673 ≤ (46774585229199/100000000000000 : ℝ)^3649
        have hw : |(5524857169/10000000000 : ℝ)|=(5524857169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131776263/10000000000 : ℝ)|^4673 ≤ (340448658583/800000000000 : ℝ)^3649
        have hw : |(5131776263/10000000000 : ℝ)|=(5131776263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686716123/5000000000 : ℝ)*x 0 + (-973723873/5000000000 : ℝ)*x 1 + (256588793/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686716123/5000000000 : ℝ)^4673 ≤ (9027837309001/20000000000000 : ℝ)^3649 := by
    have hnat : (2686716123 : ℕ)^4673*20000000000000^3649 ≤ 9027837309001^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686716123 5000000000 9027837309001 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973723873/5000000000 : ℝ)^4673 ≤ (2460947079987/20000000000000 : ℝ)^3649 := by
    have hnat : (973723873 : ℕ)^4673*20000000000000^3649 ≤ 2460947079987^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973723873 5000000000 2460947079987 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256588793/500000000 : ℝ)^4673 ≤ (42556078043101/100000000000000 : ℝ)^3649 := by
    have hnat : (256588793 : ℕ)^4673*100000000000000^3649 ≤ 42556078043101^3649*500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256588793 500000000 42556078043101 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686716123/5000000000 : ℝ), (-973723873/5000000000 : ℝ), (256588793/500000000 : ℝ)] ![(9027837309001/20000000000000 : ℝ), (2460947079987/20000000000000 : ℝ), (42556078043101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686716123/5000000000 : ℝ)|^4673 ≤ (9027837309001/20000000000000 : ℝ)^3649
        have hw : |(2686716123/5000000000 : ℝ)|=(2686716123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-973723873/5000000000 : ℝ)|^4673 ≤ (2460947079987/20000000000000 : ℝ)^3649
        have hw : |(-973723873/5000000000 : ℝ)|=(973723873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256588793/500000000 : ℝ)|^4673 ≤ (42556078043101/100000000000000 : ℝ)^3649
        have hw : |(256588793/500000000 : ℝ)|=(256588793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686715867/5000000000 : ℝ)*x 0 + (5131776329/10000000000 : ℝ)*x 1 + (-1947447811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686715867/5000000000 : ℝ)^4673 ≤ (45139181037007/100000000000000 : ℝ)^3649 := by
    have hnat : (2686715867 : ℕ)^4673*100000000000000^3649 ≤ 45139181037007^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686715867 5000000000 45139181037007 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5131776329/10000000000 : ℝ)^4673 ≤ (42556083023781/100000000000000 : ℝ)^3649 := by
    have hnat : (5131776329 : ℕ)^4673*100000000000000^3649 ≤ 42556083023781^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131776329 10000000000 42556083023781 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1947447811/10000000000 : ℝ)^4673 ≤ (6152367962941/50000000000000 : ℝ)^3649 := by
    have hnat : (1947447811 : ℕ)^4673*50000000000000^3649 ≤ 6152367962941^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947447811 10000000000 6152367962941 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686715867/5000000000 : ℝ), (5131776329/10000000000 : ℝ), (-1947447811/10000000000 : ℝ)] ![(45139181037007/100000000000000 : ℝ), (42556083023781/100000000000000 : ℝ), (6152367962941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686715867/5000000000 : ℝ)|^4673 ≤ (45139181037007/100000000000000 : ℝ)^3649
        have hw : |(2686715867/5000000000 : ℝ)|=(2686715867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5131776329/10000000000 : ℝ)|^4673 ≤ (42556083023781/100000000000000 : ℝ)^3649
        have hw : |(5131776329/10000000000 : ℝ)|=(5131776329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1947447811/10000000000 : ℝ)|^4673 ≤ (6152367962941/50000000000000 : ℝ)^3649
        have hw : |(-1947447811/10000000000 : ℝ)|=(1947447811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168876733/400000000 : ℝ)*x 0 + (3773042209/10000000000 : ℝ)*x 1 + (4712323253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168876733/400000000 : ℝ)^4673 ≤ (33145043008227/100000000000000 : ℝ)^3649 := by
    have hnat : (168876733 : ℕ)^4673*100000000000000^3649 ≤ 33145043008227^3649*400000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168876733 400000000 33145043008227 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3773042209/10000000000 : ℝ)^4673 ≤ (14350625750573/50000000000000 : ℝ)^3649 := by
    have hnat : (3773042209 : ℕ)^4673*50000000000000^3649 ≤ 14350625750573^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3773042209 10000000000 14350625750573 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4712323253/10000000000 : ℝ)^4673 ≤ (9538426370333/25000000000000 : ℝ)^3649 := by
    have hnat : (4712323253 : ℕ)^4673*25000000000000^3649 ≤ 9538426370333^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4712323253 10000000000 9538426370333 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168876733/400000000 : ℝ), (3773042209/10000000000 : ℝ), (4712323253/10000000000 : ℝ)] ![(33145043008227/100000000000000 : ℝ), (14350625750573/50000000000000 : ℝ), (9538426370333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168876733/400000000 : ℝ)|^4673 ≤ (33145043008227/100000000000000 : ℝ)^3649
        have hw : |(168876733/400000000 : ℝ)|=(168876733/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3773042209/10000000000 : ℝ)|^4673 ≤ (14350625750573/50000000000000 : ℝ)^3649
        have hw : |(3773042209/10000000000 : ℝ)|=(3773042209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4712323253/10000000000 : ℝ)|^4673 ≤ (9538426370333/25000000000000 : ℝ)^3649
        have hw : |(4712323253/10000000000 : ℝ)|=(4712323253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742408371/10000000000 : ℝ)*x 0 + (1283933431/2500000000 : ℝ)*x 1 + (5520842823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742408371/10000000000 : ℝ)^4673 ≤ (2667704933449/25000000000000 : ℝ)^3649 := by
    have hnat : (1742408371 : ℕ)^4673*25000000000000^3649 ≤ 2667704933449^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742408371 10000000000 2667704933449 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283933431/2500000000 : ℝ)^4673 ≤ (42598114266161/100000000000000 : ℝ)^3649 := by
    have hnat : (1283933431 : ℕ)^4673*100000000000000^3649 ≤ 42598114266161^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283933431 2500000000 42598114266161 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520842823/10000000000 : ℝ)^4673 ≤ (46731065987113/100000000000000 : ℝ)^3649 := by
    have hnat : (5520842823 : ℕ)^4673*100000000000000^3649 ≤ 46731065987113^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520842823 10000000000 46731065987113 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742408371/10000000000 : ℝ), (1283933431/2500000000 : ℝ), (5520842823/10000000000 : ℝ)] ![(2667704933449/25000000000000 : ℝ), (42598114266161/100000000000000 : ℝ), (46731065987113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742408371/10000000000 : ℝ)|^4673 ≤ (2667704933449/25000000000000 : ℝ)^3649
        have hw : |(-1742408371/10000000000 : ℝ)|=(1742408371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283933431/2500000000 : ℝ)|^4673 ≤ (42598114266161/100000000000000 : ℝ)^3649
        have hw : |(1283933431/2500000000 : ℝ)|=(1283933431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520842823/10000000000 : ℝ)|^4673 ≤ (46731065987113/100000000000000 : ℝ)^3649
        have hw : |(5520842823/10000000000 : ℝ)|=(5520842823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5269059193/10000000000 : ℝ)*x 0 + (-311676163/2000000000 : ℝ)*x 1 + (5520843653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5269059193/10000000000 : ℝ)^4673 ≤ (4401943561333/10000000000000 : ℝ)^3649 := by
    have hnat : (5269059193 : ℕ)^4673*10000000000000^3649 ≤ 4401943561333^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269059193 10000000000 4401943561333 10000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311676163/2000000000 : ℝ)^4673 ≤ (9249489385779/100000000000000 : ℝ)^3649 := by
    have hnat : (311676163 : ℕ)^4673*100000000000000^3649 ≤ 9249489385779^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311676163 2000000000 9249489385779 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520843653/10000000000 : ℝ)^4673 ≤ (46731074984167/100000000000000 : ℝ)^3649 := by
    have hnat : (5520843653 : ℕ)^4673*100000000000000^3649 ≤ 46731074984167^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520843653 10000000000 46731074984167 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5269059193/10000000000 : ℝ), (-311676163/2000000000 : ℝ), (5520843653/10000000000 : ℝ)] ![(4401943561333/10000000000000 : ℝ), (9249489385779/100000000000000 : ℝ), (46731074984167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5269059193/10000000000 : ℝ)|^4673 ≤ (4401943561333/10000000000000 : ℝ)^3649
        have hw : |(5269059193/10000000000 : ℝ)|=(5269059193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-311676163/2000000000 : ℝ)|^4673 ≤ (9249489385779/100000000000000 : ℝ)^3649
        have hw : |(-311676163/2000000000 : ℝ)|=(311676163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520843653/10000000000 : ℝ)|^4673 ≤ (46731074984167/100000000000000 : ℝ)^3649
        have hw : |(5520843653/10000000000 : ℝ)|=(5520843653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5269058147/10000000000 : ℝ)*x 0 + (220833763/400000000 : ℝ)*x 1 + (-779190843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5269058147/10000000000 : ℝ)^4673 ≤ (44019424422431/100000000000000 : ℝ)^3649 := by
    have hnat : (5269058147 : ℕ)^4673*100000000000000^3649 ≤ 44019424422431^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5269058147 10000000000 44019424422431 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220833763/400000000 : ℝ)^4673 ≤ (46731079558573/100000000000000 : ℝ)^3649 := by
    have hnat : (220833763 : ℕ)^4673*100000000000000^3649 ≤ 46731079558573^3649*400000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220833763 400000000 46731079558573 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (779190843/5000000000 : ℝ)^4673 ≤ (9249496006179/100000000000000 : ℝ)^3649 := by
    have hnat : (779190843 : ℕ)^4673*100000000000000^3649 ≤ 9249496006179^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779190843 5000000000 9249496006179 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5269058147/10000000000 : ℝ), (220833763/400000000 : ℝ), (-779190843/5000000000 : ℝ)] ![(44019424422431/100000000000000 : ℝ), (46731079558573/100000000000000 : ℝ), (9249496006179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5269058147/10000000000 : ℝ)|^4673 ≤ (44019424422431/100000000000000 : ℝ)^3649
        have hw : |(5269058147/10000000000 : ℝ)|=(5269058147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(220833763/400000000 : ℝ)|^4673 ≤ (46731079558573/100000000000000 : ℝ)^3649
        have hw : |(220833763/400000000 : ℝ)|=(220833763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-779190843/5000000000 : ℝ)|^4673 ≤ (9249496006179/100000000000000 : ℝ)^3649
        have hw : |(-779190843/5000000000 : ℝ)|=(779190843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s1_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168894823/400000000 : ℝ)*x 0 + (2351434041/5000000000 : ℝ)*x 1 + (1891316501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168894823/400000000 : ℝ)^4673 ≤ (1325983596487/4000000000000 : ℝ)^3649 := by
    have hnat : (168894823 : ℕ)^4673*4000000000000^3649 ≤ 1325983596487^3649*400000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168894823 400000000 1325983596487 4000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2351434041/5000000000 : ℝ)^4673 ≤ (19027847715829/50000000000000 : ℝ)^3649 := by
    have hnat : (2351434041 : ℕ)^4673*50000000000000^3649 ≤ 19027847715829^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351434041 5000000000 19027847715829 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1891316501/5000000000 : ℝ)^4673 ≤ (899834832627/3125000000000 : ℝ)^3649 := by
    have hnat : (1891316501 : ℕ)^4673*3125000000000^3649 ≤ 899834832627^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891316501 5000000000 899834832627 3125000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168894823/400000000 : ℝ), (2351434041/5000000000 : ℝ), (1891316501/5000000000 : ℝ)] ![(1325983596487/4000000000000 : ℝ), (19027847715829/50000000000000 : ℝ), (899834832627/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168894823/400000000 : ℝ)|^4673 ≤ (1325983596487/4000000000000 : ℝ)^3649
        have hw : |(168894823/400000000 : ℝ)|=(168894823/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2351434041/5000000000 : ℝ)|^4673 ≤ (19027847715829/50000000000000 : ℝ)^3649
        have hw : |(2351434041/5000000000 : ℝ)|=(2351434041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1891316501/5000000000 : ℝ)|^4673 ≤ (899834832627/3125000000000 : ℝ)^3649
        have hw : |(1891316501/5000000000 : ℝ)|=(1891316501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3067/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (751/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3067/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (751/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3067/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (751/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3067/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (751/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3067/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (751/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3067/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (751/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3067/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (751/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (751/20000 : ℝ) ^ (4671/1024 : ℝ) ≤ (6296219143883/20000000000000000000 : ℝ) := by
    have hpowers : (751/20000 : ℝ)^4671 ≤ (6296219143883/20000000000000000000 : ℝ)^1024 := by
      have hnat : (751 : ℕ)^4671*20000000000000000000^1024 ≤ 6296219143883^1024*20000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        751 20000 6296219143883 20000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (751/20000 : ℝ)) (X := (6296219143883/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3067/12500 : ℝ) ^ (4671/1024 : ℝ) ≤ (164655242671900401/100000000000000000000 : ℝ) := by
    have hpowers : (3067/12500 : ℝ)^4671 ≤ (164655242671900401/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3067 : ℕ)^4671*100000000000000000000^1024 ≤ 164655242671900401^1024*12500^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3067 12500 164655242671900401 100000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3067/12500 : ℝ)) (X := (164655242671900401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000006296219143883/10000000000000000000 : ℝ) ≤ (10000001380288337/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (10000006296219143883/10000000000000000000 : ℝ)^1024 ≤ (10000001380288337/10000000000000000 : ℝ)^4671 := by
      have hnat : (10000006296219143883 : ℕ)^1024*10000000000000000^4671 ≤ 10000001380288337^4671*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000006296219143883 10000000000000000000 10000001380288337 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001380288337/10000000000000000 : ℝ)) (X := (10000006296219143883/10000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12520585840470952477/12500000000000000000 : ℝ) ≤ (10003608025906623/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (12520585840470952477/12500000000000000000 : ℝ)^1024 ≤ (10003608025906623/10000000000000000 : ℝ)^4671 := by
      have hnat : (12520585840470952477 : ℕ)^1024*10000000000000000^4671 ≤ 10003608025906623^4671*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12520585840470952477 12500000000000000000 10003608025906623 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003608025906623/10000000000000000 : ℝ)) (X := (12520585840470952477/12500000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50164655242671900401/50000000000000000000 : ℝ) ≤ (10007214671524909/10000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50164655242671900401/50000000000000000000 : ℝ)^1024 ≤ (10007214671524909/10000000000000000 : ℝ)^4671 := by
      have hnat : (50164655242671900401 : ℕ)^1024*10000000000000000^4671 ≤ 10007214671524909^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50164655242671900401 50000000000000000000 10007214671524909 10000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007214671524909/10000000000000000 : ℝ)) (X := (50164655242671900401/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6296219143883/20000000000000000000 : ℝ) ≤ ((207782942775178603337/207810000000000000000 : ℝ)+2*(1803322809143/1039050000000000 : ℝ)*(751/20000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (207782942775178603337/207810000000000000000 : ℝ)+2*(1803322809143/1039050000000000 : ℝ)*(751/20000 : ℝ)=(10000001380288337/10000000000000000 : ℝ) by norm_num, show 1+2*(6296219143883/20000000000000000000 : ℝ)=(10000006296219143883/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(164655242671900401/100000000000000000000 : ℝ)+(6296219143883/20000000000000000000 : ℝ) ≤ ((207782942775178603337/207810000000000000000 : ℝ)+(1803322809143/1039050000000000 : ℝ)*((3067/12500 : ℝ)+(751/20000 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (207782942775178603337/207810000000000000000 : ℝ)+(1803322809143/1039050000000000 : ℝ)*((3067/12500 : ℝ)+(751/20000 : ℝ))=(10003608025906623/10000000000000000 : ℝ) by norm_num, show 1+(164655242671900401/100000000000000000000 : ℝ)+(6296219143883/20000000000000000000 : ℝ)=(12520585840470952477/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(164655242671900401/100000000000000000000 : ℝ) ≤ ((207782942775178603337/207810000000000000000 : ℝ)+2*(1803322809143/1039050000000000 : ℝ)*(3067/12500 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (207782942775178603337/207810000000000000000 : ℝ)+2*(1803322809143/1039050000000000 : ℝ)*(3067/12500 : ℝ)=(10007214671524909/10000000000000000 : ℝ) by norm_num, show 1+2*(164655242671900401/100000000000000000000 : ℝ)=(50164655242671900401/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (207782942775178603337/207810000000000000000 : ℝ)*(X 1 0+X 2 0)+(1803322809143/1039050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (751/20000 : ℝ)) (hi := (3067/12500 : ℝ)) (c := (207782942775178603337/207810000000000000000 : ℝ)) (alpha := (1803322809143/1039050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (207782942775178603337/207810000000000000000 : ℝ)*(X 0 1+X 2 1)+(1803322809143/1039050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (751/20000 : ℝ)) (hi := (3067/12500 : ℝ)) (c := (207782942775178603337/207810000000000000000 : ℝ)) (alpha := (1803322809143/1039050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (207782942775178603337/207810000000000000000 : ℝ)*(X 0 2+X 1 2)+(1803322809143/1039050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (751/20000 : ℝ)) (hi := (3067/12500 : ℝ)) (c := (207782942775178603337/207810000000000000000 : ℝ)) (alpha := (1803322809143/1039050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1742218729/10000000000 : ℝ)*X 0 0+(5524857169/10000000000 : ℝ)*X 0 1+(5131776263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686716123/5000000000 : ℝ)*X 1 0+(-973723873/5000000000 : ℝ)*X 1 1+(256588793/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686715867/5000000000 : ℝ)*X 2 0+(5131776329/10000000000 : ℝ)*X 2 1+(-1947447811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((168876733/400000000 : ℝ)*X 0 0+(3773042209/10000000000 : ℝ)*X 0 1+(4712323253/10000000000 : ℝ)*X 0 2+(168876733/400000000 : ℝ)*X 1 0+(3773042209/10000000000 : ℝ)*X 1 1+(4712323253/10000000000 : ℝ)*X 1 2+(168876733/400000000 : ℝ)*X 2 0+(3773042209/10000000000 : ℝ)*X 2 1+(4712323253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1742408371/10000000000 : ℝ)*X 0 0+(1283933431/2500000000 : ℝ)*X 0 1+(5520842823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5269059193/10000000000 : ℝ)*X 1 0+(-311676163/2000000000 : ℝ)*X 1 1+(5520843653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5269058147/10000000000 : ℝ)*X 2 0+(220833763/400000000 : ℝ)*X 2 1+(-779190843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((168894823/400000000 : ℝ)*X 0 0+(2351434041/5000000000 : ℝ)*X 0 1+(1891316501/5000000000 : ℝ)*X 0 2+(168894823/400000000 : ℝ)*X 1 0+(2351434041/5000000000 : ℝ)*X 1 1+(1891316501/5000000000 : ℝ)*X 1 2+(168894823/400000000 : ℝ)*X 2 0+(2351434041/5000000000 : ℝ)*X 2 1+(1891316501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129872861905023289378921/34635000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409338361/25000000000000 : ℝ)*(base19) + (1245459489/100000000000000 : ℝ)*(base23) + (10425129/100000000000000 : ℝ)*(upper2) + (191633201/100000000000000 : ℝ)*(upper3) + (22688051/25000000000000 : ℝ)*(upper4) + (225543187619683/12500000000000 : ℝ)*(major0) + (225543187619683/12500000000000 : ℝ)*(major1) + (225543187619683/12500000000000 : ℝ)*(major2) + (1272010627659323/50000000000000 : ℝ)*(sp0) + (1272016272434219/50000000000000 : ℝ)*(sp1) + (318004117095299/12500000000000 : ℝ)*(sp2) + (53232489498003/5000000000000 : ℝ)*(sp3) + (3231725809/25000000000000 : ℝ)*(sp4) + (6904741051/100000000000000 : ℝ)*(sp7) + (1064656694701111/100000000000000 : ℝ)*(f.failure) + (2544034182221881/100000000000000 : ℝ)*(f.sum) + (834410574358529/103905000000000000000000000000 : ℝ)*base65 + (3880005500213505943/865875000000000000000000000000000 : ℝ)*base68 + (4373731449800505943/865875000000000000000000000000000 : ℝ)*base70 + (999793411080119057/865875000000000000000000000000000 : ℝ)*base71 + (108295637029117/51952500000000000000000000000 : ℝ)*base73 + (6862370109120255943/865875000000000000000000000000000 : ℝ)*base76 + (4624609404397619057/865875000000000000000000000000000 : ℝ)*base77 + (4414544547272744057/865875000000000000000000000000000 : ℝ)*base79 + (107356613419073/51952500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6817177/1250000000000000000000 : ℝ)*base90 + (6817177/1250000000000000000000 : ℝ)*base92 + (6817177/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107013794556932218462949/17317500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1069596803/100000000000000 : ℝ)*(base19) + (17898867/2000000000000 : ℝ)*(base23) + (47036679/25000000000000 : ℝ)*(upper2) + (633703/195312500000 : ℝ)*(upper3) + (13412077/25000000000000 : ℝ)*(upper5) + (920834422120589/50000000000000 : ℝ)*(major0) + (920834422120589/50000000000000 : ℝ)*(major1) + (920834422120589/50000000000000 : ℝ)*(major2) + (4756957827/50000000000000 : ℝ)*(sp1) + (8693514677/100000000000000 : ℝ)*(sp2) + (1298329047326027/50000000000000 : ℝ)*(sp4) + (2596647511139597/100000000000000 : ℝ)*(sp5) + (649162126548507/25000000000000 : ℝ)*(sp6) + (1086679387846381/100000000000000 : ℝ)*(sp7) + (1086679387846381/100000000000000 : ℝ)*(f.failure) + (1298329047326027/50000000000000 : ℝ)*(f.sum) + (199101367254197/103905000000000000000000000000 : ℝ)*base66 + (9534640075289401831/3463500000000000000000000000000000 : ℝ)*base67 + (1826295720398401831/3463500000000000000000000000000000 : ℝ)*base69 + (4647631732022401831/3463500000000000000000000000000000 : ℝ)*base71 + (56062498469807/103905000000000000000000000000 : ℝ)*base74 + (2190089153978098169/3463500000000000000000000000000000 : ℝ)*base76 + (9815119709069098169/3463500000000000000000000000000000 : ℝ)*base78 + (51953553359810098169/3463500000000000000000000000000000 : ℝ)*base80 + (57920382141073/103905000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3007933/1250000000000000000000 : ℝ)*base89 + (3007933/1250000000000000000000 : ℝ)*base91 + (3007933/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1588_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3067/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (751/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1588_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1588_s2_0 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351851393/2000000000 : ℝ)*x 0 + (2718533859/5000000000 : ℝ)*x 1 + (5208442533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351851393/2000000000 : ℝ)^4673 ≤ (10803138335173/100000000000000 : ℝ)^3649 := by
    have hnat : (351851393 : ℕ)^4673*100000000000000^3649 ≤ 10803138335173^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351851393 2000000000 10803138335173 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718533859/5000000000 : ℝ)^4673 ≤ (45824899186841/100000000000000 : ℝ)^3649 := by
    have hnat : (2718533859 : ℕ)^4673*100000000000000^3649 ≤ 45824899186841^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718533859 5000000000 45824899186841 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208442533/10000000000 : ℝ)^4673 ≤ (43371962460041/100000000000000 : ℝ)^3649 := by
    have hnat : (5208442533 : ℕ)^4673*100000000000000^3649 ≤ 43371962460041^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208442533 10000000000 43371962460041 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351851393/2000000000 : ℝ), (2718533859/5000000000 : ℝ), (5208442533/10000000000 : ℝ)] ![(10803138335173/100000000000000 : ℝ), (45824899186841/100000000000000 : ℝ), (43371962460041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351851393/2000000000 : ℝ)|^4673 ≤ (10803138335173/100000000000000 : ℝ)^3649
        have hw : |(-351851393/2000000000 : ℝ)|=(351851393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718533859/5000000000 : ℝ)|^4673 ≤ (45824899186841/100000000000000 : ℝ)^3649
        have hw : |(2718533859/5000000000 : ℝ)|=(2718533859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5208442533/10000000000 : ℝ)|^4673 ≤ (43371962460041/100000000000000 : ℝ)^3649
        have hw : |(5208442533/10000000000 : ℝ)|=(5208442533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_1 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350656973/10000000000 : ℝ)*x 0 + (-938255793/5000000000 : ℝ)*x 1 + (5208442651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350656973/10000000000 : ℝ)^4673 ≤ (22447160173117/50000000000000 : ℝ)^3649 := by
    have hnat : (5350656973 : ℕ)^4673*50000000000000^3649 ≤ 22447160173117^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350656973 10000000000 22447160173117 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938255793/5000000000 : ℝ)^4673 ≤ (5866857956537/50000000000000 : ℝ)^3649 := by
    have hnat : (938255793 : ℕ)^4673*50000000000000^3649 ≤ 5866857956537^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938255793 5000000000 5866857956537 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208442651/10000000000 : ℝ)^4673 ≤ (43371963718401/100000000000000 : ℝ)^3649 := by
    have hnat : (5208442651 : ℕ)^4673*100000000000000^3649 ≤ 43371963718401^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208442651 10000000000 43371963718401 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350656973/10000000000 : ℝ), (-938255793/5000000000 : ℝ), (5208442651/10000000000 : ℝ)] ![(22447160173117/50000000000000 : ℝ), (5866857956537/50000000000000 : ℝ), (43371963718401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350656973/10000000000 : ℝ)|^4673 ≤ (22447160173117/50000000000000 : ℝ)^3649
        have hw : |(5350656973/10000000000 : ℝ)|=(5350656973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-938255793/5000000000 : ℝ)|^4673 ≤ (5866857956537/50000000000000 : ℝ)^3649
        have hw : |(-938255793/5000000000 : ℝ)|=(938255793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5208442651/10000000000 : ℝ)|^4673 ≤ (43371963718401/100000000000000 : ℝ)^3649
        have hw : |(5208442651/10000000000 : ℝ)|=(5208442651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_2 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070131377/2000000000 : ℝ)*x 0 + (5208443093/10000000000 : ℝ)*x 1 + (-1876511117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070131377/2000000000 : ℝ)^4673 ≤ (22447159700337/50000000000000 : ℝ)^3649 := by
    have hnat : (1070131377 : ℕ)^4673*50000000000000^3649 ≤ 22447159700337^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070131377 2000000000 22447159700337 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5208443093/10000000000 : ℝ)^4673 ≤ (21685984215961/50000000000000 : ℝ)^3649 := by
    have hnat : (5208443093 : ℕ)^4673*50000000000000^3649 ≤ 21685984215961^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208443093 10000000000 21685984215961 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876511117/10000000000 : ℝ)^4673 ≤ (2933428039369/25000000000000 : ℝ)^3649 := by
    have hnat : (1876511117 : ℕ)^4673*25000000000000^3649 ≤ 2933428039369^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876511117 10000000000 2933428039369 25000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070131377/2000000000 : ℝ), (5208443093/10000000000 : ℝ), (-1876511117/10000000000 : ℝ)] ![(22447159700337/50000000000000 : ℝ), (21685984215961/50000000000000 : ℝ), (2933428039369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070131377/2000000000 : ℝ)|^4673 ≤ (22447159700337/50000000000000 : ℝ)^3649
        have hw : |(1070131377/2000000000 : ℝ)|=(1070131377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5208443093/10000000000 : ℝ)|^4673 ≤ (21685984215961/50000000000000 : ℝ)^3649
        have hw : |(5208443093/10000000000 : ℝ)|=(5208443093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876511117/10000000000 : ℝ)|^4673 ≤ (2933428039369/25000000000000 : ℝ)^3649
        have hw : |(-1876511117/10000000000 : ℝ)|=(1876511117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_3 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4234301479/10000000000 : ℝ)*x 0 + (1984088779/5000000000 : ℝ)*x 1 + (4514485389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234301479/10000000000 : ℝ)^4673 ≤ (6653918417457/20000000000000 : ℝ)^3649 := by
    have hnat : (4234301479 : ℕ)^4673*20000000000000^3649 ≤ 6653918417457^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234301479 10000000000 6653918417457 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984088779/5000000000 : ℝ)^4673 ≤ (30615812668863/100000000000000 : ℝ)^3649 := by
    have hnat : (1984088779 : ℕ)^4673*100000000000000^3649 ≤ 30615812668863^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984088779 5000000000 30615812668863 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4514485389/10000000000 : ℝ)^4673 ≤ (36114595222923/100000000000000 : ℝ)^3649 := by
    have hnat : (4514485389 : ℕ)^4673*100000000000000^3649 ≤ 36114595222923^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514485389 10000000000 36114595222923 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234301479/10000000000 : ℝ), (1984088779/5000000000 : ℝ), (4514485389/10000000000 : ℝ)] ![(6653918417457/20000000000000 : ℝ), (30615812668863/100000000000000 : ℝ), (36114595222923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234301479/10000000000 : ℝ)|^4673 ≤ (6653918417457/20000000000000 : ℝ)^3649
        have hw : |(4234301479/10000000000 : ℝ)|=(4234301479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1984088779/5000000000 : ℝ)|^4673 ≤ (30615812668863/100000000000000 : ℝ)^3649
        have hw : |(1984088779/5000000000 : ℝ)|=(1984088779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4514485389/10000000000 : ℝ)|^4673 ≤ (36114595222923/100000000000000 : ℝ)^3649
        have hw : |(4514485389/10000000000 : ℝ)|=(4514485389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_4 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-351858747/2000000000 : ℝ)*x 0 + (5209789303/10000000000 : ℝ)*x 1 + (27178551/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351858747/2000000000 : ℝ)^4673 ≤ (5401713747341/50000000000000 : ℝ)^3649 := by
    have hnat : (351858747 : ℕ)^4673*50000000000000^3649 ≤ 5401713747341^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351858747 2000000000 5401713747341 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5209789303/10000000000 : ℝ)^4673 ≤ (43386325034833/100000000000000 : ℝ)^3649 := by
    have hnat : (5209789303 : ℕ)^4673*100000000000000^3649 ≤ 43386325034833^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209789303 10000000000 43386325034833 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27178551/50000000 : ℝ)^4673 ≤ (2290512372559/5000000000000 : ℝ)^3649 := by
    have hnat : (27178551 : ℕ)^4673*5000000000000^3649 ≤ 2290512372559^3649*50000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27178551 50000000 2290512372559 5000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351858747/2000000000 : ℝ), (5209789303/10000000000 : ℝ), (27178551/50000000 : ℝ)] ![(5401713747341/50000000000000 : ℝ), (43386325034833/100000000000000 : ℝ), (2290512372559/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351858747/2000000000 : ℝ)|^4673 ≤ (5401713747341/50000000000000 : ℝ)^3649
        have hw : |(-351858747/2000000000 : ℝ)|=(351858747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5209789303/10000000000 : ℝ)|^4673 ≤ (43386325034833/100000000000000 : ℝ)^3649
        have hw : |(5209789303/10000000000 : ℝ)|=(5209789303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27178551/50000000 : ℝ)|^4673 ≤ (2290512372559/5000000000000 : ℝ)^3649
        have hw : |(27178551/50000000 : ℝ)|=(27178551/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_5 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290040417/10000000000 : ℝ)*x 0 + (-412310907/2500000000 : ℝ)*x 1 + (5435711617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290040417/10000000000 : ℝ)^4673 ≤ (1769761356859/4000000000000 : ℝ)^3649 := by
    have hnat : (5290040417 : ℕ)^4673*4000000000000^3649 ≤ 1769761356859^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290040417 10000000000 1769761356859 4000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412310907/2500000000 : ℝ)^4673 ≤ (1989140663739/20000000000000 : ℝ)^3649 := by
    have hnat : (412310907 : ℕ)^4673*20000000000000^3649 ≤ 1989140663739^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412310907 2500000000 1989140663739 20000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435711617/10000000000 : ℝ)^4673 ≤ (45810262744371/100000000000000 : ℝ)^3649 := by
    have hnat : (5435711617 : ℕ)^4673*100000000000000^3649 ≤ 45810262744371^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435711617 10000000000 45810262744371 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290040417/10000000000 : ℝ), (-412310907/2500000000 : ℝ), (5435711617/10000000000 : ℝ)] ![(1769761356859/4000000000000 : ℝ), (1989140663739/20000000000000 : ℝ), (45810262744371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290040417/10000000000 : ℝ)|^4673 ≤ (1769761356859/4000000000000 : ℝ)^3649
        have hw : |(5290040417/10000000000 : ℝ)|=(5290040417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412310907/2500000000 : ℝ)|^4673 ≤ (1989140663739/20000000000000 : ℝ)^3649
        have hw : |(-412310907/2500000000 : ℝ)|=(412310907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435711617/10000000000 : ℝ)|^4673 ≤ (45810262744371/100000000000000 : ℝ)^3649
        have hw : |(5435711617/10000000000 : ℝ)|=(5435711617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_6 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058008139/2000000000 : ℝ)*x 0 + (1358928159/2500000000 : ℝ)*x 1 + (-824620909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058008139/2000000000 : ℝ)^4673 ≤ (5530504612381/12500000000000 : ℝ)^3649 := by
    have hnat : (1058008139 : ℕ)^4673*12500000000000^3649 ≤ 5530504612381^3649*2000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058008139 2000000000 5530504612381 12500000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358928159/2500000000 : ℝ)^4673 ≤ (45810273742087/100000000000000 : ℝ)^3649 := by
    have hnat : (1358928159 : ℕ)^4673*100000000000000^3649 ≤ 45810273742087^3649*2500000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358928159 2500000000 45810273742087 100000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824620909/5000000000 : ℝ)^4673 ≤ (19891378681/200000000000 : ℝ)^3649 := by
    have hnat : (824620909 : ℕ)^4673*200000000000^3649 ≤ 19891378681^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824620909 5000000000 19891378681 200000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058008139/2000000000 : ℝ), (1358928159/2500000000 : ℝ), (-824620909/5000000000 : ℝ)] ![(5530504612381/12500000000000 : ℝ), (45810273742087/100000000000000 : ℝ), (19891378681/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058008139/2000000000 : ℝ)|^4673 ≤ (5530504612381/12500000000000 : ℝ)^3649
        have hw : |(1058008139/2000000000 : ℝ)|=(1058008139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358928159/2500000000 : ℝ)|^4673 ≤ (45810273742087/100000000000000 : ℝ)^3649
        have hw : |(1358928159/2500000000 : ℝ)|=(1358928159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-824620909/5000000000 : ℝ)|^4673 ≤ (19891378681/200000000000 : ℝ)^3649
        have hw : |(-824620909/5000000000 : ℝ)|=(824620909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1588_s2_7 (p : ℝ) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4234389993/10000000000 : ℝ)*x 0 + (2255634391/5000000000 : ℝ)*x 1 + (3971421881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234389993/10000000000 : ℝ)^4673 ≤ (16635241362271/50000000000000 : ℝ)^3649 := by
    have hnat : (4234389993 : ℕ)^4673*50000000000000^3649 ≤ 16635241362271^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234389993 10000000000 16635241362271 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255634391/5000000000 : ℝ)^4673 ≤ (28865316447/80000000000 : ℝ)^3649 := by
    have hnat : (2255634391 : ℕ)^4673*80000000000^3649 ≤ 28865316447^3649*5000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255634391 5000000000 28865316447 80000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3971421881/10000000000 : ℝ)^4673 ≤ (15323935854189/50000000000000 : ℝ)^3649 := by
    have hnat : (3971421881 : ℕ)^4673*50000000000000^3649 ≤ 15323935854189^3649*10000000000^4673 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3971421881 10000000000 15323935854189 50000000000000 4673 3649 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4673/1024 : ℝ)) 4673 3649 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234389993/10000000000 : ℝ), (2255634391/5000000000 : ℝ), (3971421881/10000000000 : ℝ)] ![(16635241362271/50000000000000 : ℝ), (28865316447/80000000000 : ℝ), (15323935854189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234389993/10000000000 : ℝ)|^4673 ≤ (16635241362271/50000000000000 : ℝ)^3649
        have hw : |(4234389993/10000000000 : ℝ)|=(4234389993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2255634391/5000000000 : ℝ)|^4673 ≤ (28865316447/80000000000 : ℝ)^3649
        have hw : |(2255634391/5000000000 : ℝ)|=(2255634391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3971421881/10000000000 : ℝ)|^4673 ≤ (15323935854189/50000000000000 : ℝ)^3649
        have hw : |(3971421881/10000000000 : ℝ)|=(3971421881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1588_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10917/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7883/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4633/50000 : ℝ) ^ (4671/1024 : ℝ) ≤ (1938451744116063/100000000000000000000 : ℝ) := by
    have hpowers : (4633/50000 : ℝ)^4671 ≤ (1938451744116063/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4633 : ℕ)^4671*100000000000000000000^1024 ≤ 1938451744116063^1024*50000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4633 50000 1938451744116063 100000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4633/50000 : ℝ)) (X := (1938451744116063/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/20000 : ℝ) ^ (4671/1024 : ℝ) ≤ (9031616387917379/25000000000000000000 : ℝ) := by
    have hpowers : (3519/20000 : ℝ)^4671 ≤ (9031616387917379/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3519 : ℕ)^4671*25000000000000000000^1024 ≤ 9031616387917379^1024*20000^4671 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 20000 9031616387917379 25000000000000000000 4671 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/20000 : ℝ)) (X := (9031616387917379/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001938451744116063/50000000000000000000 : ℝ) ≤ (2000016998026497/2000000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (50001938451744116063/50000000000000000000 : ℝ)^1024 ≤ (2000016998026497/2000000000000000 : ℝ)^4671 := by
      have hnat : (50001938451744116063 : ℕ)^1024*2000000000000000^4671 ≤ 2000016998026497^4671*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001938451744116063 50000000000000000000 2000016998026497 2000000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016998026497/2000000000000000 : ℝ)) (X := (50001938451744116063/50000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038064917295785579/100000000000000000000 : ℝ) ≤ (500041717709689/500000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (100038064917295785579/100000000000000000000 : ℝ)^1024 ≤ (500041717709689/500000000000000 : ℝ)^4671 := by
      have hnat : (100038064917295785579 : ℕ)^1024*500000000000000^4671 ≤ 500041717709689^4671*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038064917295785579 100000000000000000000 500041717709689 500000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500041717709689/500000000000000 : ℝ)) (X := (100038064917295785579/100000000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509031616387917379/12500000000000000000 : ℝ) ≤ (400063348730203/400000000000000 : ℝ) ^ (4671/1024 : ℝ) := by
    have hpowers : (12509031616387917379/12500000000000000000 : ℝ)^1024 ≤ (400063348730203/400000000000000 : ℝ)^4671 := by
      have hnat : (12509031616387917379 : ℕ)^1024*400000000000000^4671 ≤ 400063348730203^4671*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509031616387917379 12500000000000000000 400063348730203 400000000000000 1024 4671 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400063348730203/400000000000000 : ℝ)) (X := (12509031616387917379/12500000000000000000 : ℝ)) (by norm_num) 4671 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1938451744116063/100000000000000000000 : ℝ) ≤ ((666214565344236389/666320000000000000 : ℝ)+2*(149872812259/166580000000000 : ℝ)*(4633/50000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (666214565344236389/666320000000000000 : ℝ)+2*(149872812259/166580000000000 : ℝ)*(4633/50000 : ℝ)=(2000016998026497/2000000000000000 : ℝ) by norm_num, show 1+2*(1938451744116063/100000000000000000000 : ℝ)=(50001938451744116063/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9031616387917379/25000000000000000000 : ℝ)+(1938451744116063/100000000000000000000 : ℝ) ≤ ((666214565344236389/666320000000000000 : ℝ)+(149872812259/166580000000000 : ℝ)*((3519/20000 : ℝ)+(4633/50000 : ℝ)))^(4671/1024 : ℝ) := by
    rw [show (666214565344236389/666320000000000000 : ℝ)+(149872812259/166580000000000 : ℝ)*((3519/20000 : ℝ)+(4633/50000 : ℝ))=(500041717709689/500000000000000 : ℝ) by norm_num, show 1+(9031616387917379/25000000000000000000 : ℝ)+(1938451744116063/100000000000000000000 : ℝ)=(100038064917295785579/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9031616387917379/25000000000000000000 : ℝ) ≤ ((666214565344236389/666320000000000000 : ℝ)+2*(149872812259/166580000000000 : ℝ)*(3519/20000 : ℝ))^(4671/1024 : ℝ) := by
    rw [show (666214565344236389/666320000000000000 : ℝ)+2*(149872812259/166580000000000 : ℝ)*(3519/20000 : ℝ)=(400063348730203/400000000000000 : ℝ) by norm_num, show 1+2*(9031616387917379/25000000000000000000 : ℝ)=(12509031616387917379/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (666214565344236389/666320000000000000 : ℝ)*(X 1 0+X 2 0)+(149872812259/166580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (4633/50000 : ℝ)) (hi := (3519/20000 : ℝ)) (c := (666214565344236389/666320000000000000 : ℝ)) (alpha := (149872812259/166580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (666214565344236389/666320000000000000 : ℝ)*(X 0 1+X 2 1)+(149872812259/166580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (4633/50000 : ℝ)) (hi := (3519/20000 : ℝ)) (c := (666214565344236389/666320000000000000 : ℝ)) (alpha := (149872812259/166580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (666214565344236389/666320000000000000 : ℝ)*(X 0 2+X 1 2)+(149872812259/166580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4671/1024 : ℝ)) (lo := (4633/50000 : ℝ)) (hi := (3519/20000 : ℝ)) (c := (666214565344236389/666320000000000000 : ℝ)) (alpha := (149872812259/166580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-351851393/2000000000 : ℝ)*X 0 0+(2718533859/5000000000 : ℝ)*X 0 1+(5208442533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350656973/10000000000 : ℝ)*X 1 0+(-938255793/5000000000 : ℝ)*X 1 1+(5208442651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070131377/2000000000 : ℝ)*X 2 0+(5208443093/10000000000 : ℝ)*X 2 1+(-1876511117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4234301479/10000000000 : ℝ)*X 0 0+(1984088779/5000000000 : ℝ)*X 0 1+(4514485389/10000000000 : ℝ)*X 0 2+(4234301479/10000000000 : ℝ)*X 1 0+(1984088779/5000000000 : ℝ)*X 1 1+(4514485389/10000000000 : ℝ)*X 1 2+(4234301479/10000000000 : ℝ)*X 2 0+(1984088779/5000000000 : ℝ)*X 2 1+(4514485389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-351858747/2000000000 : ℝ)*X 0 0+(5209789303/10000000000 : ℝ)*X 0 1+(27178551/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290040417/10000000000 : ℝ)*X 1 0+(-412310907/2500000000 : ℝ)*X 1 1+(5435711617/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058008139/2000000000 : ℝ)*X 2 0+(1358928159/2500000000 : ℝ)*X 2 1+(-824620909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4234389993/10000000000 : ℝ)*X 0 0+(2255634391/5000000000 : ℝ)*X 0 1+(3971421881/10000000000 : ℝ)*X 0 2+(4234389993/10000000000 : ℝ)*X 1 0+(2255634391/5000000000 : ℝ)*X 1 1+(3971421881/10000000000 : ℝ)*X 1 2+(4234389993/10000000000 : ℝ)*X 2 0+(2255634391/5000000000 : ℝ)*X 2 1+(3971421881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1588_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9734189700458044422873/2082250000000000000000000000 : ℝ) := by norm_num
    linear_combination (156071753/25000000000000 : ℝ)*(base19) + (573442009/100000000000000 : ℝ)*(base23) + (328427/3125000000000 : ℝ)*(upper4) + (123161417/50000000000000 : ℝ)*(upper5) + (1551121268741901/50000000000000 : ℝ)*(major0) + (1551121268741901/50000000000000 : ℝ)*(major1) + (1551121268741901/50000000000000 : ℝ)*(major2) + (1093495789041773/25000000000000 : ℝ)*(sp0) + (546749745622143/12500000000000 : ℝ)*(sp1) + (1093500402862659/25000000000000 : ℝ)*(sp2) + (457619365189387/25000000000000 : ℝ)*(sp3) + (1189295347/6250000000000 : ℝ)*(sp4) + (3595628489/100000000000000 : ℝ)*(sp5) + (2636744671/50000000000000 : ℝ)*(sp7) + (183048273424689/10000000000000 : ℝ)*(f.failure) + (1093500546223161/25000000000000 : ℝ)*(f.sum) + (301198772061/520562500000000000000000000 : ℝ)*base65 + (11794256580031489/33316000000000000000000000000000 : ℝ)*base67 + (150580510278888511/33316000000000000000000000000000 : ℝ)*base70 + (108973777504803489/33316000000000000000000000000000 : ℝ)*base71 + (689443501469/832900000000000000000000000 : ℝ)*base74 + (186295189185475489/33316000000000000000000000000000 : ℝ)*base75 + (14134300822056511/33316000000000000000000000000000 : ℝ)*base78 + (178944868672144511/33316000000000000000000000000000 : ℝ)*base80 + (11839678879/104112500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (116577/125000000000000000000 : ℝ)*base89 + (116577/125000000000000000000 : ℝ)*base91 + (116577/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45339318072895004493088377/16658000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49998383/25000000000000 : ℝ)*(base8) + (850830207/100000000000000 : ℝ)*(base15) + (66661423/100000000000000 : ℝ)*(upper2) + (5444411/25000000000000 : ℝ)*(lower5) + (3139349995301369/100000000000000 : ℝ)*(major0) + (3139349995301369/100000000000000 : ℝ)*(major1) + (3139349995301369/100000000000000 : ℝ)*(major2) + (12031283259/100000000000000 : ℝ)*(sp1) + (46844566171/100000000000000 : ℝ)*(sp2) + (30055957/2000000000000 : ℝ)*(sp3) + (221316082801271/5000000000000 : ℝ)*(sp4) + (2213154486952743/50000000000000 : ℝ)*(sp5) + (4426275011452781/100000000000000 : ℝ)*(sp6) + (926188270530057/50000000000000 : ℝ)*(sp7) + (463094510964491/25000000000000 : ℝ)*(f.failure) + (4426321856018953/100000000000000 : ℝ)*(f.sum) + (22853817382937/8329000000000000000000000000 : ℝ)*base66 + (461840455610144541/66632000000000000000000000000000 : ℝ)*base67 + (521312289100512541/66632000000000000000000000000000 : ℝ)*base69 + (305280987901671459/66632000000000000000000000000000 : ℝ)*base72 + (41292672639743/8329000000000000000000000000 : ℝ)*base74 + (148517811684840541/66632000000000000000000000000000 : ℝ)*base75 + (555896469436976541/66632000000000000000000000000000 : ℝ)*base77 + (81147495009256541/66632000000000000000000000000000 : ℝ)*base79 + (183750074531/104112500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1162163/312500000000000000000 : ℝ)*base89 + (1162163/312500000000000000000 : ℝ)*base91 + (1162163/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1588_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1588_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1588_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1588_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1588_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1588_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4671/1024 : ℝ) ≤ p) (hpb : p ≤ (4673/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21184593/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7883/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1588_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:06:21.293639+00:00
-- url     : https://prove2.me/submissions/98222474-4cae-4d45-8d54-16433d385084

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
theorem support_rectangle_w1065_s3_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099753813/5000000000 : ℝ)*x 0 + (271882487/500000000 : ℝ)*x 1 + (5224267231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099753813/5000000000 : ℝ)^4129 ≤ (3337110319501/25000000000000 : ℝ)^3105 := by
    have hnat : (1099753813 : ℕ)^4129*25000000000000^3105 ≤ 3337110319501^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099753813 5000000000 3337110319501 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271882487/500000000 : ℝ)^4129 ≤ (44478724462199/100000000000000 : ℝ)^3105 := by
    have hnat : (271882487 : ℕ)^4129*100000000000000^3105 ≤ 44478724462199^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271882487 500000000 44478724462199 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224267231/10000000000 : ℝ)^4129 ≤ (1317901070177/3125000000000 : ℝ)^3105 := by
    have hnat : (5224267231 : ℕ)^4129*3125000000000^3105 ≤ 1317901070177^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224267231 10000000000 1317901070177 3125000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099753813/5000000000 : ℝ), (271882487/500000000 : ℝ), (5224267231/10000000000 : ℝ)] ![(3337110319501/25000000000000 : ℝ), (44478724462199/100000000000000 : ℝ), (1317901070177/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099753813/5000000000 : ℝ)|^4129 ≤ (3337110319501/25000000000000 : ℝ)^3105
        have hw : |(-1099753813/5000000000 : ℝ)|=(1099753813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271882487/500000000 : ℝ)|^4129 ≤ (44478724462199/100000000000000 : ℝ)^3105
        have hw : |(271882487/500000000 : ℝ)|=(271882487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224267231/10000000000 : ℝ)|^4129 ≤ (1317901070177/3125000000000 : ℝ)^3105
        have hw : |(5224267231/10000000000 : ℝ)|=(5224267231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355716449/10000000000 : ℝ)*x 0 + (-230877909/1000000000 : ℝ)*x 1 + (5224267369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355716449/10000000000 : ℝ)^4129 ≤ (43589726603977/100000000000000 : ℝ)^3105 := by
    have hnat : (5355716449 : ℕ)^4129*100000000000000^3105 ≤ 43589726603977^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355716449 10000000000 43589726603977 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230877909/1000000000 : ℝ)^4129 ≤ (14237437657799/100000000000000 : ℝ)^3105 := by
    have hnat : (230877909 : ℕ)^4129*100000000000000^3105 ≤ 14237437657799^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230877909 1000000000 14237437657799 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224267369/10000000000 : ℝ)^4129 ≤ (2635802232941/6250000000000 : ℝ)^3105 := by
    have hnat : (5224267369 : ℕ)^4129*6250000000000^3105 ≤ 2635802232941^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224267369 10000000000 2635802232941 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355716449/10000000000 : ℝ), (-230877909/1000000000 : ℝ), (5224267369/10000000000 : ℝ)] ![(43589726603977/100000000000000 : ℝ), (14237437657799/100000000000000 : ℝ), (2635802232941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355716449/10000000000 : ℝ)|^4129 ≤ (43589726603977/100000000000000 : ℝ)^3105
        have hw : |(5355716449/10000000000 : ℝ)|=(5355716449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-230877909/1000000000 : ℝ)|^4129 ≤ (14237437657799/100000000000000 : ℝ)^3105
        have hw : |(-230877909/1000000000 : ℝ)|=(230877909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224267369/10000000000 : ℝ)|^4129 ≤ (2635802232941/6250000000000 : ℝ)^3105
        have hw : |(5224267369/10000000000 : ℝ)|=(5224267369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267785823/500000000 : ℝ)*x 0 + (5224267737/10000000000 : ℝ)*x 1 + (-1154389297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267785823/500000000 : ℝ)^4129 ≤ (43589726723031/100000000000000 : ℝ)^3105 := by
    have hnat : (267785823 : ℕ)^4129*100000000000000^3105 ≤ 43589726723031^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267785823 500000000 43589726723031 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224267737/10000000000 : ℝ)^4129 ≤ (5271604959679/12500000000000 : ℝ)^3105 := by
    have hnat : (5224267737 : ℕ)^4129*12500000000000^3105 ≤ 5271604959679^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224267737 10000000000 5271604959679 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154389297/5000000000 : ℝ)^4129 ≤ (14237433590423/100000000000000 : ℝ)^3105 := by
    have hnat : (1154389297 : ℕ)^4129*100000000000000^3105 ≤ 14237433590423^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154389297 5000000000 14237433590423 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267785823/500000000 : ℝ), (5224267737/10000000000 : ℝ), (-1154389297/5000000000 : ℝ)] ![(43589726723031/100000000000000 : ℝ), (5271604959679/12500000000000 : ℝ), (14237433590423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267785823/500000000 : ℝ)|^4129 ≤ (43589726723031/100000000000000 : ℝ)^3105
        have hw : |(267785823/500000000 : ℝ)|=(267785823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224267737/10000000000 : ℝ)|^4129 ≤ (5271604959679/12500000000000 : ℝ)^3105
        have hw : |(5224267737/10000000000 : ℝ)|=(5224267737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154389297/5000000000 : ℝ)|^4129 ≤ (14237433590423/100000000000000 : ℝ)^3105
        have hw : |(-1154389297/5000000000 : ℝ)|=(1154389297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (437282581/1000000000 : ℝ)*x 0 + (2084411883/5000000000 : ℝ)*x 1 + (143341849/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437282581/1000000000 : ℝ)^4129 ≤ (8322022924559/25000000000000 : ℝ)^3105 := by
    have hnat : (437282581 : ℕ)^4129*25000000000000^3105 ≤ 8322022924559^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437282581 1000000000 8322022924559 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084411883/5000000000 : ℝ)^4129 ≤ (7809757662219/25000000000000 : ℝ)^3105 := by
    have hnat : (2084411883 : ℕ)^4129*25000000000000^3105 ≤ 7809757662219^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084411883 5000000000 7809757662219 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143341849/312500000 : ℝ)^4129 ≤ (35472877639261/100000000000000 : ℝ)^3105 := by
    have hnat : (143341849 : ℕ)^4129*100000000000000^3105 ≤ 35472877639261^3105*312500000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143341849 312500000 35472877639261 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437282581/1000000000 : ℝ), (2084411883/5000000000 : ℝ), (143341849/312500000 : ℝ)] ![(8322022924559/25000000000000 : ℝ), (7809757662219/25000000000000 : ℝ), (35472877639261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437282581/1000000000 : ℝ)|^4129 ≤ (8322022924559/25000000000000 : ℝ)^3105
        have hw : |(437282581/1000000000 : ℝ)|=(437282581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084411883/5000000000 : ℝ)|^4129 ≤ (7809757662219/25000000000000 : ℝ)^3105
        have hw : |(2084411883/5000000000 : ℝ)|=(2084411883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143341849/312500000 : ℝ)|^4129 ≤ (35472877639261/100000000000000 : ℝ)^3105
        have hw : |(143341849/312500000 : ℝ)|=(143341849/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-439906069/2000000000 : ℝ)*x 0 + (104502859/200000000 : ℝ)*x 1 + (5436768603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439906069/2000000000 : ℝ)^4129 ≤ (6674312313453/50000000000000 : ℝ)^3105 := by
    have hnat : (439906069 : ℕ)^4129*50000000000000^3105 ≤ 6674312313453^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439906069 2000000000 6674312313453 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104502859/200000000 : ℝ)^4129 ≤ (21091117551473/50000000000000 : ℝ)^3105 := by
    have hnat : (104502859 : ℕ)^4129*50000000000000^3105 ≤ 21091117551473^3105*200000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104502859 200000000 21091117551473 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436768603/10000000000 : ℝ)^4129 ≤ (11117285063683/25000000000000 : ℝ)^3105 := by
    have hnat : (5436768603 : ℕ)^4129*25000000000000^3105 ≤ 11117285063683^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436768603 10000000000 11117285063683 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439906069/2000000000 : ℝ), (104502859/200000000 : ℝ), (5436768603/10000000000 : ℝ)] ![(6674312313453/50000000000000 : ℝ), (21091117551473/50000000000000 : ℝ), (11117285063683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439906069/2000000000 : ℝ)|^4129 ≤ (6674312313453/50000000000000 : ℝ)^3105
        have hw : |(-439906069/2000000000 : ℝ)|=(439906069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104502859/200000000 : ℝ)|^4129 ≤ (21091117551473/50000000000000 : ℝ)^3105
        have hw : |(104502859/200000000 : ℝ)|=(104502859/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436768603/10000000000 : ℝ)|^4129 ≤ (11117285063683/25000000000000 : ℝ)^3105
        have hw : |(5436768603/10000000000 : ℝ)|=(5436768603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650985213/5000000000 : ℝ)*x 0 + (-1048138537/5000000000 : ℝ)*x 1 + (271838457/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650985213/5000000000 : ℝ)^4129 ≤ (4300899520407/10000000000000 : ℝ)^3105 := by
    have hnat : (2650985213 : ℕ)^4129*10000000000000^3105 ≤ 4300899520407^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650985213 5000000000 4300899520407 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048138537/5000000000 : ℝ)^4129 ≤ (12521858689259/100000000000000 : ℝ)^3105 := by
    have hnat : (1048138537 : ℕ)^4129*100000000000000^3105 ≤ 12521858689259^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048138537 5000000000 12521858689259 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271838457/500000000 : ℝ)^4129 ≤ (22234573047787/50000000000000 : ℝ)^3105 := by
    have hnat : (271838457 : ℕ)^4129*50000000000000^3105 ≤ 22234573047787^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271838457 500000000 22234573047787 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650985213/5000000000 : ℝ), (-1048138537/5000000000 : ℝ), (271838457/500000000 : ℝ)] ![(4300899520407/10000000000000 : ℝ), (12521858689259/100000000000000 : ℝ), (22234573047787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650985213/5000000000 : ℝ)|^4129 ≤ (4300899520407/10000000000000 : ℝ)^3105
        have hw : |(2650985213/5000000000 : ℝ)|=(2650985213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048138537/5000000000 : ℝ)|^4129 ≤ (12521858689259/100000000000000 : ℝ)^3105
        have hw : |(-1048138537/5000000000 : ℝ)|=(1048138537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271838457/500000000 : ℝ)|^4129 ≤ (22234573047787/50000000000000 : ℝ)^3105
        have hw : |(271838457/500000000 : ℝ)|=(271838457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060394003/2000000000 : ℝ)*x 0 + (5436769073/10000000000 : ℝ)*x 1 + (-2096277723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060394003/2000000000 : ℝ)^4129 ≤ (43008990770567/100000000000000 : ℝ)^3105 := by
    have hnat : (1060394003 : ℕ)^4129*100000000000000^3105 ≤ 43008990770567^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060394003 2000000000 43008990770567 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436769073/10000000000 : ℝ)^4129 ≤ (11117286341707/25000000000000 : ℝ)^3105 := by
    have hnat : (5436769073 : ℕ)^4129*25000000000000^3105 ≤ 11117286341707^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436769073 10000000000 11117286341707 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096277723/10000000000 : ℝ)^4129 ≤ (1252186384449/10000000000000 : ℝ)^3105 := by
    have hnat : (2096277723 : ℕ)^4129*10000000000000^3105 ≤ 1252186384449^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096277723 10000000000 1252186384449 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060394003/2000000000 : ℝ), (5436769073/10000000000 : ℝ), (-2096277723/10000000000 : ℝ)] ![(43008990770567/100000000000000 : ℝ), (11117286341707/25000000000000 : ℝ), (1252186384449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060394003/2000000000 : ℝ)|^4129 ≤ (43008990770567/100000000000000 : ℝ)^3105
        have hw : |(1060394003/2000000000 : ℝ)|=(1060394003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436769073/10000000000 : ℝ)|^4129 ≤ (11117286341707/25000000000000 : ℝ)^3105
        have hw : |(5436769073/10000000000 : ℝ)|=(5436769073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2096277723/10000000000 : ℝ)|^4129 ≤ (1252186384449/10000000000000 : ℝ)^3105
        have hw : |(-2096277723/10000000000 : ℝ)|=(2096277723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s3_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2186434663/5000000000 : ℝ)*x 0 + (1146306191/2500000000 : ℝ)*x 1 + (1042637159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186434663/5000000000 : ℝ)^4129 ≤ (33288532212201/100000000000000 : ℝ)^3105 := by
    have hnat : (2186434663 : ℕ)^4129*100000000000000^3105 ≤ 33288532212201^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186434663 5000000000 33288532212201 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1146306191/2500000000 : ℝ)^4129 ≤ (35455248012377/100000000000000 : ℝ)^3105 := by
    have hnat : (1146306191 : ℕ)^4129*100000000000000^3105 ≤ 35455248012377^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146306191 2500000000 35455248012377 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042637159/2500000000 : ℝ)^4129 ≤ (31256219754759/100000000000000 : ℝ)^3105 := by
    have hnat : (1042637159 : ℕ)^4129*100000000000000^3105 ≤ 31256219754759^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042637159 2500000000 31256219754759 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186434663/5000000000 : ℝ), (1146306191/2500000000 : ℝ), (1042637159/2500000000 : ℝ)] ![(33288532212201/100000000000000 : ℝ), (35455248012377/100000000000000 : ℝ), (31256219754759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186434663/5000000000 : ℝ)|^4129 ≤ (33288532212201/100000000000000 : ℝ)^3105
        have hw : |(2186434663/5000000000 : ℝ)|=(2186434663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1146306191/2500000000 : ℝ)|^4129 ≤ (35455248012377/100000000000000 : ℝ)^3105
        have hw : |(1146306191/2500000000 : ℝ)|=(1146306191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042637159/2500000000 : ℝ)|^4129 ≤ (31256219754759/100000000000000 : ℝ)^3105
        have hw : |(1042637159/2500000000 : ℝ)|=(1042637159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14907/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2093/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8707/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2093/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8707/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2093/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8707/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2093/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8707/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2093/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8707/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2093/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8707/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8707/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (5318968612566817/100000000000000000000 : ℝ) := by
    have hpowers : (8707/100000 : ℝ)^8257 ≤ (5318968612566817/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8707 : ℕ)^8257*100000000000000000000^2048 ≤ 5318968612566817^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8707 100000 5318968612566817 100000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8707/100000 : ℝ)) (X := (5318968612566817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2093/12500 : ℝ) ^ (8257/2048 : ℝ) ≤ (9283537580637149/12500000000000000000 : ℝ) := by
    have hpowers : (2093/12500 : ℝ)^8257 ≤ (9283537580637149/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2093 : ℕ)^8257*12500000000000000000^2048 ≤ 9283537580637149^2048*12500^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2093 12500 9283537580637149 12500000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2093/12500 : ℝ)) (X := (9283537580637149/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005318968612566817/50000000000000000000 : ℝ) ≤ (625016490268937/625000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (50005318968612566817/50000000000000000000 : ℝ)^2048 ≤ (625016490268937/625000000000000 : ℝ)^8257 := by
      have hnat : (50005318968612566817 : ℕ)^2048*625000000000000^8257 ≤ 625016490268937^8257*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005318968612566817 50000000000000000000 625016490268937 625000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625016490268937/625000000000000 : ℝ)) (X := (50005318968612566817/50000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100079587269257664009/100000000000000000000 : ℝ) ≤ (1250246678539879/1250000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (100079587269257664009/100000000000000000000 : ℝ)^2048 ≤ (1250246678539879/1250000000000000 : ℝ)^8257 := by
      have hnat : (100079587269257664009 : ℕ)^2048*1250000000000000^8257 ≤ 1250246678539879^8257*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100079587269257664009 100000000000000000000 1250246678539879 1250000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250246678539879/1250000000000000 : ℝ)) (X := (100079587269257664009/100000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6259283537580637149/6250000000000000000 : ℝ) ≤ (312615094135471/312500000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (6259283537580637149/6250000000000000000 : ℝ)^2048 ≤ (312615094135471/312500000000000 : ℝ)^8257 := by
      have hnat : (6259283537580637149 : ℕ)^2048*312500000000000^8257 ≤ 312615094135471^8257*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259283537580637149 6250000000000000000 312615094135471 312500000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312615094135471/312500000000000 : ℝ)) (X := (6259283537580637149/6250000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5318968612566817/100000000000000000000 : ℝ) ≤ ((278966492432666063/279062500000000000 : ℝ)+2*(4748844489/2232500000000 : ℝ)*(8707/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (278966492432666063/279062500000000000 : ℝ)+2*(4748844489/2232500000000 : ℝ)*(8707/100000 : ℝ)=(625016490268937/625000000000000 : ℝ) by norm_num, show 1+2*(5318968612566817/100000000000000000000 : ℝ)=(50005318968612566817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9283537580637149/12500000000000000000 : ℝ)+(5318968612566817/100000000000000000000 : ℝ) ≤ ((278966492432666063/279062500000000000 : ℝ)+(4748844489/2232500000000 : ℝ)*((2093/12500 : ℝ)+(8707/100000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (278966492432666063/279062500000000000 : ℝ)+(4748844489/2232500000000 : ℝ)*((2093/12500 : ℝ)+(8707/100000 : ℝ))=(1250246678539879/1250000000000000 : ℝ) by norm_num, show 1+(9283537580637149/12500000000000000000 : ℝ)+(5318968612566817/100000000000000000000 : ℝ)=(100079587269257664009/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9283537580637149/12500000000000000000 : ℝ) ≤ ((278966492432666063/279062500000000000 : ℝ)+2*(4748844489/2232500000000 : ℝ)*(2093/12500 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (278966492432666063/279062500000000000 : ℝ)+2*(4748844489/2232500000000 : ℝ)*(2093/12500 : ℝ)=(312615094135471/312500000000000 : ℝ) by norm_num, show 1+2*(9283537580637149/12500000000000000000 : ℝ)=(6259283537580637149/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (278966492432666063/279062500000000000 : ℝ)*(X 1 0+X 2 0)+(4748844489/2232500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (8707/100000 : ℝ)) (hi := (2093/12500 : ℝ)) (c := (278966492432666063/279062500000000000 : ℝ)) (alpha := (4748844489/2232500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (278966492432666063/279062500000000000 : ℝ)*(X 0 1+X 2 1)+(4748844489/2232500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (8707/100000 : ℝ)) (hi := (2093/12500 : ℝ)) (c := (278966492432666063/279062500000000000 : ℝ)) (alpha := (4748844489/2232500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (278966492432666063/279062500000000000 : ℝ)*(X 0 2+X 1 2)+(4748844489/2232500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (8707/100000 : ℝ)) (hi := (2093/12500 : ℝ)) (c := (278966492432666063/279062500000000000 : ℝ)) (alpha := (4748844489/2232500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1099753813/5000000000 : ℝ)*X 0 0+(271882487/500000000 : ℝ)*X 0 1+(5224267231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355716449/10000000000 : ℝ)*X 1 0+(-230877909/1000000000 : ℝ)*X 1 1+(5224267369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267785823/500000000 : ℝ)*X 2 0+(5224267737/10000000000 : ℝ)*X 2 1+(-1154389297/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((437282581/1000000000 : ℝ)*X 0 0+(2084411883/5000000000 : ℝ)*X 0 1+(143341849/312500000 : ℝ)*X 0 2+(437282581/1000000000 : ℝ)*X 1 0+(2084411883/5000000000 : ℝ)*X 1 1+(143341849/312500000 : ℝ)*X 1 2+(437282581/1000000000 : ℝ)*X 2 0+(2084411883/5000000000 : ℝ)*X 2 1+(143341849/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-439906069/2000000000 : ℝ)*X 0 0+(104502859/200000000 : ℝ)*X 0 1+(5436768603/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650985213/5000000000 : ℝ)*X 1 0+(-1048138537/5000000000 : ℝ)*X 1 1+(271838457/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060394003/2000000000 : ℝ)*X 2 0+(5436769073/10000000000 : ℝ)*X 2 1+(-2096277723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2186434663/5000000000 : ℝ)*X 0 0+(1146306191/2500000000 : ℝ)*X 0 1+(1042637159/2500000000 : ℝ)*X 0 2+(2186434663/5000000000 : ℝ)*X 1 0+(1146306191/2500000000 : ℝ)*X 1 1+(1042637159/2500000000 : ℝ)*X 1 2+(2186434663/5000000000 : ℝ)*X 2 0+(1146306191/2500000000 : ℝ)*X 2 1+(1042637159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36449997205023175627630551/13953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (966170713/100000000000000 : ℝ)*(base19) + (328877433/50000000000000 : ℝ)*(base23) + (186006963/100000000000000 : ℝ)*(lower2) + (11811769/12500000000000 : ℝ)*(upper5) + (1769542235851911/50000000000000 : ℝ)*(major0) + (1769542235851911/50000000000000 : ℝ)*(major1) + (1769542235851911/50000000000000 : ℝ)*(major2) + (4686441021456203/100000000000000 : ℝ)*(sp0) + (4686464812334377/100000000000000 : ℝ)*(sp1) + (2343234018442639/50000000000000 : ℝ)*(sp2) + (2391692089602163/100000000000000 : ℝ)*(sp3) + (13836591971/50000000000000 : ℝ)*(sp4) + (583227011/20000000000000 : ℝ)*(sp5) + (8072088061/100000000000000 : ℝ)*(sp7) + (149481260105639/6250000000000 : ℝ)*(f.failure) + (292904293415009/6250000000000 : ℝ)*(f.sum) + (6229556643/4465000000000000000000000 : ℝ)*base66 + (85944361503802643/13953125000000000000000000000000 : ℝ)*base67 + (109357539012206009/6976562500000000000000000000000 : ℝ)*base69 + (46414416431268509/6976562500000000000000000000000 : ℝ)*base71 + (845590661451/446500000000000000000000000 : ℝ)*base74 + (91548891086798317/3488281250000000000000000000000 : ℝ)*base75 + (97052092502208893/13953125000000000000000000000000 : ℝ)*base77 + (245472814925083893/13953125000000000000000000000000 : ℝ)*base79 + (218777919/1116250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1190837/125000000000000000000 : ℝ)*base90 + (1190837/125000000000000000000 : ℝ)*base92 + (1190837/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9570070894681723449662259/2790625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47206731/4000000000000 : ℝ)*(base19) + (32077239/4000000000000 : ℝ)*(base23) + (48050521/100000000000000 : ℝ)*(upper2) + (20207141/10000000000000 : ℝ)*(upper3) + (356842008576249/10000000000000 : ℝ)*(major0) + (356842008576249/10000000000000 : ℝ)*(major1) + (356842008576249/10000000000000 : ℝ)*(major2) + (5554928147/20000000000000 : ℝ)*(sp1) + (17656468689/100000000000000 : ℝ)*(sp2) + (1877510551/100000000000000 : ℝ)*(sp3) + (4725314996329487/100000000000000 : ℝ)*(sp4) + (2362643020760239/50000000000000 : ℝ)*(sp5) + (147665516810307/3125000000000 : ℝ)*(sp6) + (1205761591686387/50000000000000 : ℝ)*(sp7) + (1205762530441663/50000000000000 : ℝ)*(f.failure) + (4725314996329487/100000000000000 : ℝ)*(f.sum) + (1250207864113/893000000000000000000000000 : ℝ)*base65 + (49931270899525187/2790625000000000000000000000000 : ℝ)*base67 + (18765428395367281/1395312500000000000000000000000 : ℝ)*base69 + (12936523285817281/1395312500000000000000000000000 : ℝ)*base71 + (62150557351/22325000000000000000000000 : ℝ)*base73 + (2646377166309789/348828125000000000000000000000 : ℝ)*base75 + (30785063794443937/2790625000000000000000000000000 : ℝ)*base77 + (2027913277666453/697656250000000000000000000000 : ℝ)*base79 + (930490992511/446500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1494371/1000000000000000000000 : ℝ)*base89 + (1494371/1000000000000000000000 : ℝ)*base91 + (1494371/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1065_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14907/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_s4_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-440639097/2000000000 : ℝ)*x 0 + (2702932677/5000000000 : ℝ)*x 1 + (5253642473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440639097/2000000000 : ℝ)^4129 ≤ (13378211541601/100000000000000 : ℝ)^3105 := by
    have hnat : (440639097 : ℕ)^4129*100000000000000^3105 ≤ 13378211541601^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440639097 2000000000 13378211541601 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702932677/5000000000 : ℝ)^4129 ≤ (22066663615097/50000000000000 : ℝ)^3105 := by
    have hnat : (2702932677 : ℕ)^4129*50000000000000^3105 ≤ 22066663615097^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702932677 5000000000 22066663615097 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253642473/10000000000 : ℝ)^4129 ≤ (42488461222401/100000000000000 : ℝ)^3105 := by
    have hnat : (5253642473 : ℕ)^4129*100000000000000^3105 ≤ 42488461222401^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253642473 10000000000 42488461222401 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440639097/2000000000 : ℝ), (2702932677/5000000000 : ℝ), (5253642473/10000000000 : ℝ)] ![(13378211541601/100000000000000 : ℝ), (22066663615097/50000000000000 : ℝ), (42488461222401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440639097/2000000000 : ℝ)|^4129 ≤ (13378211541601/100000000000000 : ℝ)^3105
        have hw : |(-440639097/2000000000 : ℝ)|=(440639097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702932677/5000000000 : ℝ)|^4129 ≤ (22066663615097/50000000000000 : ℝ)^3105
        have hw : |(2702932677/5000000000 : ℝ)|=(2702932677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253642473/10000000000 : ℝ)|^4129 ≤ (42488461222401/100000000000000 : ℝ)^3105
        have hw : |(5253642473/10000000000 : ℝ)|=(5253642473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347843779/10000000000 : ℝ)*x 0 + (-2280621149/10000000000 : ℝ)*x 1 + (1050728489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347843779/10000000000 : ℝ)^4129 ≤ (43504540926919/100000000000000 : ℝ)^3105 := by
    have hnat : (5347843779 : ℕ)^4129*100000000000000^3105 ≤ 43504540926919^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347843779 10000000000 43504540926919 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280621149/10000000000 : ℝ)^4129 ≤ (14006998141033/100000000000000 : ℝ)^3105 := by
    have hnat : (2280621149 : ℕ)^4129*100000000000000^3105 ≤ 14006998141033^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280621149 10000000000 14006998141033 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050728489/2000000000 : ℝ)^4129 ≤ (42488460921273/100000000000000 : ℝ)^3105 := by
    have hnat : (1050728489 : ℕ)^4129*100000000000000^3105 ≤ 42488460921273^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050728489 2000000000 42488460921273 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347843779/10000000000 : ℝ), (-2280621149/10000000000 : ℝ), (1050728489/2000000000 : ℝ)] ![(43504540926919/100000000000000 : ℝ), (14006998141033/100000000000000 : ℝ), (42488460921273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347843779/10000000000 : ℝ)|^4129 ≤ (43504540926919/100000000000000 : ℝ)^3105
        have hw : |(5347843779/10000000000 : ℝ)|=(5347843779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2280621149/10000000000 : ℝ)|^4129 ≤ (14006998141033/100000000000000 : ℝ)^3105
        have hw : |(-2280621149/10000000000 : ℝ)|=(2280621149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050728489/2000000000 : ℝ)|^4129 ≤ (42488460921273/100000000000000 : ℝ)^3105
        have hw : |(1050728489/2000000000 : ℝ)|=(1050728489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347843871/10000000000 : ℝ)*x 0 + (1313410601/2500000000 : ℝ)*x 1 + (-57015527/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347843871/10000000000 : ℝ)^4129 ≤ (43504541922157/100000000000000 : ℝ)^3105 := by
    have hnat : (5347843871 : ℕ)^4129*100000000000000^3105 ≤ 43504541922157^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347843871 10000000000 43504541922157 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313410601/2500000000 : ℝ)^4129 ≤ (8497692096067/20000000000000 : ℝ)^3105 := by
    have hnat : (1313410601 : ℕ)^4129*20000000000000^3105 ≤ 8497692096067^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313410601 2500000000 8497692096067 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57015527/250000000 : ℝ)^4129 ≤ (7003498788747/50000000000000 : ℝ)^3105 := by
    have hnat : (57015527 : ℕ)^4129*50000000000000^3105 ≤ 7003498788747^3105*250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57015527 250000000 7003498788747 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347843871/10000000000 : ℝ), (1313410601/2500000000 : ℝ), (-57015527/250000000 : ℝ)] ![(43504541922157/100000000000000 : ℝ), (8497692096067/20000000000000 : ℝ), (7003498788747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347843871/10000000000 : ℝ)|^4129 ≤ (43504541922157/100000000000000 : ℝ)^3105
        have hw : |(5347843871/10000000000 : ℝ)|=(5347843871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313410601/2500000000 : ℝ)|^4129 ≤ (8497692096067/20000000000000 : ℝ)^3105
        have hw : |(1313410601/2500000000 : ℝ)|=(1313410601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57015527/250000000 : ℝ)|^4129 ≤ (7003498788747/50000000000000 : ℝ)^3105
        have hw : |(-57015527/250000000 : ℝ)|=(57015527/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187509537/5000000000 : ℝ)*x 0 + (4228455549/10000000000 : ℝ)*x 1 + (4526732039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187509537/5000000000 : ℝ)^4129 ≤ (16655147992391/50000000000000 : ℝ)^3105 := by
    have hnat : (2187509537 : ℕ)^4129*50000000000000^3105 ≤ 16655147992391^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187509537 5000000000 16655147992391 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228455549/10000000000 : ℝ)^4129 ≤ (1591732239763/5000000000000 : ℝ)^3105 := by
    have hnat : (4228455549 : ℕ)^4129*5000000000000^3105 ≤ 1591732239763^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228455549 10000000000 1591732239763 5000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526732039/10000000000 : ℝ)^4129 ≤ (34855059204621/100000000000000 : ℝ)^3105 := by
    have hnat : (4526732039 : ℕ)^4129*100000000000000^3105 ≤ 34855059204621^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526732039 10000000000 34855059204621 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187509537/5000000000 : ℝ), (4228455549/10000000000 : ℝ), (4526732039/10000000000 : ℝ)] ![(16655147992391/50000000000000 : ℝ), (1591732239763/5000000000000 : ℝ), (34855059204621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187509537/5000000000 : ℝ)|^4129 ≤ (16655147992391/50000000000000 : ℝ)^3105
        have hw : |(2187509537/5000000000 : ℝ)|=(2187509537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228455549/10000000000 : ℝ)|^4129 ≤ (1591732239763/5000000000000 : ℝ)^3105
        have hw : |(4228455549/10000000000 : ℝ)|=(4228455549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526732039/10000000000 : ℝ)|^4129 ≤ (34855059204621/100000000000000 : ℝ)^3105
        have hw : |(4526732039/10000000000 : ℝ)|=(4526732039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-68850121/312500000 : ℝ)*x 0 + (5254088661/10000000000 : ℝ)*x 1 + (5405417099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68850121/312500000 : ℝ)^4129 ≤ (267565585289/2000000000000 : ℝ)^3105 := by
    have hnat : (68850121 : ℕ)^4129*2000000000000^3105 ≤ 267565585289^3105*312500000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68850121 312500000 267565585289 2000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254088661/10000000000 : ℝ)^4129 ≤ (42493259857593/100000000000000 : ℝ)^3105 := by
    have hnat : (5254088661 : ℕ)^4129*100000000000000^3105 ≤ 42493259857593^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254088661 10000000000 42493259857593 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405417099/10000000000 : ℝ)^4129 ≤ (44128460873613/100000000000000 : ℝ)^3105 := by
    have hnat : (5405417099 : ℕ)^4129*100000000000000^3105 ≤ 44128460873613^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405417099 10000000000 44128460873613 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-68850121/312500000 : ℝ), (5254088661/10000000000 : ℝ), (5405417099/10000000000 : ℝ)] ![(267565585289/2000000000000 : ℝ), (42493259857593/100000000000000 : ℝ), (44128460873613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-68850121/312500000 : ℝ)|^4129 ≤ (267565585289/2000000000000 : ℝ)^3105
        have hw : |(-68850121/312500000 : ℝ)|=(68850121/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254088661/10000000000 : ℝ)|^4129 ≤ (42493259857593/100000000000000 : ℝ)^3105
        have hw : |(5254088661/10000000000 : ℝ)|=(5254088661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405417099/10000000000 : ℝ)|^4129 ≤ (44128460873613/100000000000000 : ℝ)^3105
        have hw : |(5405417099/10000000000 : ℝ)|=(5405417099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061901379/2000000000 : ℝ)*x 0 + (-1064423059/5000000000 : ℝ)*x 1 + (337838579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061901379/2000000000 : ℝ)^4129 ≤ (8618062200889/20000000000000 : ℝ)^3105 := by
    have hnat : (1061901379 : ℕ)^4129*20000000000000^3105 ≤ 8618062200889^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061901379 2000000000 8618062200889 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064423059/5000000000 : ℝ)^4129 ≤ (6390613161063/50000000000000 : ℝ)^3105 := by
    have hnat : (1064423059 : ℕ)^4129*50000000000000^3105 ≤ 6390613161063^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064423059 5000000000 6390613161063 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337838579/625000000 : ℝ)^4129 ≤ (22064231332433/50000000000000 : ℝ)^3105 := by
    have hnat : (337838579 : ℕ)^4129*50000000000000^3105 ≤ 22064231332433^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337838579 625000000 22064231332433 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061901379/2000000000 : ℝ), (-1064423059/5000000000 : ℝ), (337838579/625000000 : ℝ)] ![(8618062200889/20000000000000 : ℝ), (6390613161063/50000000000000 : ℝ), (22064231332433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061901379/2000000000 : ℝ)|^4129 ≤ (8618062200889/20000000000000 : ℝ)^3105
        have hw : |(1061901379/2000000000 : ℝ)|=(1061901379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064423059/5000000000 : ℝ)|^4129 ≤ (6390613161063/50000000000000 : ℝ)^3105
        have hw : |(-1064423059/5000000000 : ℝ)|=(1064423059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337838579/625000000 : ℝ)|^4129 ≤ (22064231332433/50000000000000 : ℝ)^3105
        have hw : |(337838579/625000000 : ℝ)|=(337838579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309507/10000000 : ℝ)*x 0 + (5405417107/10000000000 : ℝ)*x 1 + (-532211547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309507/10000000 : ℝ)^4129 ≤ (43090312137623/100000000000000 : ℝ)^3105 := by
    have hnat : (5309507 : ℕ)^4129*100000000000000^3105 ≤ 43090312137623^3105*10000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309507 10000000 43090312137623 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405417107/10000000000 : ℝ)^4129 ≤ (22064230480231/50000000000000 : ℝ)^3105 := by
    have hnat : (5405417107 : ℕ)^4129*50000000000000^3105 ≤ 22064230480231^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405417107 10000000000 22064230480231 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532211547/2500000000 : ℝ)^4129 ≤ (2556245376199/20000000000000 : ℝ)^3105 := by
    have hnat : (532211547 : ℕ)^4129*20000000000000^3105 ≤ 2556245376199^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532211547 2500000000 2556245376199 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309507/10000000 : ℝ), (5405417107/10000000000 : ℝ), (-532211547/2500000000 : ℝ)] ![(43090312137623/100000000000000 : ℝ), (22064230480231/50000000000000 : ℝ), (2556245376199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309507/10000000 : ℝ)|^4129 ≤ (43090312137623/100000000000000 : ℝ)^3105
        have hw : |(5309507/10000000 : ℝ)|=(5309507/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405417107/10000000000 : ℝ)|^4129 ≤ (22064230480231/50000000000000 : ℝ)^3105
        have hw : |(5405417107/10000000000 : ℝ)|=(5405417107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532211547/2500000000 : ℝ)|^4129 ≤ (2556245376199/20000000000000 : ℝ)^3105
        have hw : |(-532211547/2500000000 : ℝ)|=(532211547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s4_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875007029/2000000000 : ℝ)*x 0 + (2262928677/5000000000 : ℝ)*x 1 + (264333363/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875007029/2000000000 : ℝ)^4129 ≤ (6662091739761/20000000000000 : ℝ)^3105 := by
    have hnat : (875007029 : ℕ)^4129*20000000000000^3105 ≤ 6662091739761^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875007029 2000000000 6662091739761 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262928677/5000000000 : ℝ)^4129 ≤ (8711525862651/25000000000000 : ℝ)^3105 := by
    have hnat : (2262928677 : ℕ)^4129*25000000000000^3105 ≤ 8711525862651^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262928677 5000000000 8711525862651 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264333363/625000000 : ℝ)^4129 ≤ (15921718917131/50000000000000 : ℝ)^3105 := by
    have hnat : (264333363 : ℕ)^4129*50000000000000^3105 ≤ 15921718917131^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264333363 625000000 15921718917131 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875007029/2000000000 : ℝ), (2262928677/5000000000 : ℝ), (264333363/625000000 : ℝ)] ![(6662091739761/20000000000000 : ℝ), (8711525862651/25000000000000 : ℝ), (15921718917131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875007029/2000000000 : ℝ)|^4129 ≤ (6662091739761/20000000000000 : ℝ)^3105
        have hw : |(875007029/2000000000 : ℝ)|=(875007029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262928677/5000000000 : ℝ)|^4129 ≤ (8711525862651/25000000000000 : ℝ)^3105
        have hw : |(2262928677/5000000000 : ℝ)|=(2262928677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264333363/625000000 : ℝ)|^4129 ≤ (15921718917131/50000000000000 : ℝ)^3105
        have hw : |(264333363/625000000 : ℝ)|=(264333363/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (551/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14243/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10393/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (1357271622798829/12500000000000000000 : ℝ) := by
    have hpowers : (10393/100000 : ℝ)^8257 ≤ (1357271622798829/12500000000000000000 : ℝ)^2048 := by
      have hnat : (10393 : ℕ)^8257*12500000000000000000^2048 ≤ 1357271622798829^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10393 100000 1357271622798829 12500000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10393/100000 : ℝ)) (X := (1357271622798829/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14907/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (11621597814472703/25000000000000000000 : ℝ) := by
    have hpowers : (14907/100000 : ℝ)^8257 ≤ (11621597814472703/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14907 : ℕ)^8257*25000000000000000000^2048 ≤ 11621597814472703^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14907 100000 11621597814472703 25000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14907/100000 : ℝ)) (X := (11621597814472703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251357271622798829/6250000000000000000 : ℝ) ≤ (10000538590839371/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (6251357271622798829/6250000000000000000 : ℝ)^2048 ≤ (10000538590839371/10000000000000000 : ℝ)^8257 := by
      have hnat : (6251357271622798829 : ℕ)^2048*10000000000000000^8257 ≤ 10000538590839371^8257*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251357271622798829 6250000000000000000 10000538590839371 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538590839371/10000000000000000 : ℝ)) (X := (6251357271622798829/6250000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25014336141060070361/25000000000000000000 : ℝ) ≤ (10001422021979727/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (25014336141060070361/25000000000000000000 : ℝ)^2048 ≤ (10001422021979727/10000000000000000 : ℝ)^8257 := by
      have hnat : (25014336141060070361 : ℕ)^2048*10000000000000000^8257 ≤ 10001422021979727^8257*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014336141060070361 25000000000000000000 10001422021979727 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001422021979727/10000000000000000 : ℝ)) (X := (25014336141060070361/25000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511621597814472703/12500000000000000000 : ℝ) ≤ (10002305453120083/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (12511621597814472703/12500000000000000000 : ℝ)^2048 ≤ (10002305453120083/10000000000000000 : ℝ)^8257 := by
      have hnat : (12511621597814472703 : ℕ)^2048*10000000000000000^8257 ≤ 10002305453120083^8257*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511621597814472703 12500000000000000000 10002305453120083 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002305453120083/10000000000000000 : ℝ)) (X := (12511621597814472703/12500000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1357271622798829/12500000000000000000 : ℝ) ≤ ((22562034099682740439/22570000000000000000 : ℝ)+2*(220857785089/112850000000000 : ℝ)*(10393/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (22562034099682740439/22570000000000000000 : ℝ)+2*(220857785089/112850000000000 : ℝ)*(10393/100000 : ℝ)=(10000538590839371/10000000000000000 : ℝ) by norm_num, show 1+2*(1357271622798829/12500000000000000000 : ℝ)=(6251357271622798829/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11621597814472703/25000000000000000000 : ℝ)+(1357271622798829/12500000000000000000 : ℝ) ≤ ((22562034099682740439/22570000000000000000 : ℝ)+(220857785089/112850000000000 : ℝ)*((14907/100000 : ℝ)+(10393/100000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (22562034099682740439/22570000000000000000 : ℝ)+(220857785089/112850000000000 : ℝ)*((14907/100000 : ℝ)+(10393/100000 : ℝ))=(10001422021979727/10000000000000000 : ℝ) by norm_num, show 1+(11621597814472703/25000000000000000000 : ℝ)+(1357271622798829/12500000000000000000 : ℝ)=(25014336141060070361/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11621597814472703/25000000000000000000 : ℝ) ≤ ((22562034099682740439/22570000000000000000 : ℝ)+2*(220857785089/112850000000000 : ℝ)*(14907/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (22562034099682740439/22570000000000000000 : ℝ)+2*(220857785089/112850000000000 : ℝ)*(14907/100000 : ℝ)=(10002305453120083/10000000000000000 : ℝ) by norm_num, show 1+2*(11621597814472703/25000000000000000000 : ℝ)=(12511621597814472703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22562034099682740439/22570000000000000000 : ℝ)*(X 1 0+X 2 0)+(220857785089/112850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (10393/100000 : ℝ)) (hi := (14907/100000 : ℝ)) (c := (22562034099682740439/22570000000000000000 : ℝ)) (alpha := (220857785089/112850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22562034099682740439/22570000000000000000 : ℝ)*(X 0 1+X 2 1)+(220857785089/112850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (10393/100000 : ℝ)) (hi := (14907/100000 : ℝ)) (c := (22562034099682740439/22570000000000000000 : ℝ)) (alpha := (220857785089/112850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22562034099682740439/22570000000000000000 : ℝ)*(X 0 2+X 1 2)+(220857785089/112850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (10393/100000 : ℝ)) (hi := (14907/100000 : ℝ)) (c := (22562034099682740439/22570000000000000000 : ℝ)) (alpha := (220857785089/112850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-440639097/2000000000 : ℝ)*X 0 0+(2702932677/5000000000 : ℝ)*X 0 1+(5253642473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347843779/10000000000 : ℝ)*X 1 0+(-2280621149/10000000000 : ℝ)*X 1 1+(1050728489/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347843871/10000000000 : ℝ)*X 2 0+(1313410601/2500000000 : ℝ)*X 2 1+(-57015527/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187509537/5000000000 : ℝ)*X 0 0+(4228455549/10000000000 : ℝ)*X 0 1+(4526732039/10000000000 : ℝ)*X 0 2+(2187509537/5000000000 : ℝ)*X 1 0+(4228455549/10000000000 : ℝ)*X 1 1+(4526732039/10000000000 : ℝ)*X 1 2+(2187509537/5000000000 : ℝ)*X 2 0+(4228455549/10000000000 : ℝ)*X 2 1+(4526732039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-68850121/312500000 : ℝ)*X 0 0+(5254088661/10000000000 : ℝ)*X 0 1+(5405417099/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061901379/2000000000 : ℝ)*X 1 0+(-1064423059/5000000000 : ℝ)*X 1 1+(337838579/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309507/10000000 : ℝ)*X 2 0+(5405417107/10000000000 : ℝ)*X 2 1+(-532211547/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875007029/2000000000 : ℝ)*X 0 0+(2262928677/5000000000 : ℝ)*X 0 1+(264333363/625000000 : ℝ)*X 0 2+(875007029/2000000000 : ℝ)*X 1 0+(2262928677/5000000000 : ℝ)*X 1 1+(264333363/625000000 : ℝ)*X 1 2+(875007029/2000000000 : ℝ)*X 2 0+(2262928677/5000000000 : ℝ)*X 2 1+(264333363/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3794707000530985668330875121/564250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (274025857/25000000000000 : ℝ)*(base19) + (232163731/25000000000000 : ℝ)*(base23) + (149986949/100000000000000 : ℝ)*(lower2) + (149454849/100000000000000 : ℝ)*(upper3) + (51111441/100000000000000 : ℝ)*(upper5) + (2480494726355987/50000000000000 : ℝ)*(major0) + (2480494726355987/50000000000000 : ℝ)*(major1) + (2480494726355987/50000000000000 : ℝ)*(major2) + (1642334296918471/25000000000000 : ℝ)*(sp0) + (1313871862052353/20000000000000 : ℝ)*(sp1) + (6569359477710269/100000000000000 : ℝ)*(sp2) + (838151094370443/25000000000000 : ℝ)*(sp3) + (23218691309/100000000000000 : ℝ)*(sp4) + (13897402879/100000000000000 : ℝ)*(sp7) + (838154568721163/25000000000000 : ℝ)*(f.failure) + (6569360406365193/100000000000000 : ℝ)*(f.sum) + (1133531161203/11285000000000000000000000000 : ℝ)*base66 + (16774051723501758293/1128500000000000000000000000000000 : ℝ)*base67 + (5248052779907758293/1128500000000000000000000000000000 : ℝ)*base69 + (27566039031940258293/1128500000000000000000000000000000 : ℝ)*base71 + (24875677185193/11285000000000000000000000000 : ℝ)*base74 + (12286634051799241707/1128500000000000000000000000000000 : ℝ)*base76 + (2323072392666258293/1128500000000000000000000000000000 : ℝ)*base77 + (2187326324591741707/1128500000000000000000000000000000 : ℝ)*base80 + (1900790563583/705312500000000000000000000 : ℝ)*base82 + (895871/500000000000000000000 : ℝ)*base89 + (895871/500000000000000000000 : ℝ)*base91 + (895871/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1902999559504760957828279703/564250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (268202393/20000000000000 : ℝ)*(base19) + (1444768159/100000000000000 : ℝ)*(base23) + (24487559/25000000000000 : ℝ)*(upper3) + (3507981/100000000000000 : ℝ)*(lower4) + (42221927/25000000000000 : ℝ)*(upper5) + (2495139940233941/50000000000000 : ℝ)*(major0) + (2495139940233941/50000000000000 : ℝ)*(major1) + (2495139940233941/50000000000000 : ℝ)*(major2) + (41325908753/100000000000000 : ℝ)*(sp1) + (917045177/2500000000000 : ℝ)*(sp2) + (6608147011173251/100000000000000 : ℝ)*(sp4) + (6608104344252533/100000000000000 : ℝ)*(sp5) + (1652027221149503/25000000000000 : ℝ)*(sp6) + (843103159335479/25000000000000 : ℝ)*(sp7) + (843103159335479/25000000000000 : ℝ)*(f.failure) + (6608147011173251/100000000000000 : ℝ)*(f.sum) + (7097110969977/1410625000000000000000000000 : ℝ)*base65 + (8069903792803340099/1128500000000000000000000000000000 : ℝ)*base67 + (8651484486753659901/1128500000000000000000000000000000 : ℝ)*base70 + (9652519790993840099/1128500000000000000000000000000000 : ℝ)*base71 + (19528418010691/11285000000000000000000000000 : ℝ)*base73 + (7528550190071659901/1128500000000000000000000000000000 : ℝ)*base76 + (6216149202540840099/1128500000000000000000000000000000 : ℝ)*base77 + (2051833696752840099/1128500000000000000000000000000000 : ℝ)*base79 + (9457733865369/2821250000000000000000000000 : ℝ)*base81 + (935557/500000000000000000000 : ℝ)*base90 + (935557/500000000000000000000 : ℝ)*base92 + (935557/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1065_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_s5_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88161129/400000000 : ℝ)*x 0 + (1349256117/2500000000 : ℝ)*x 1 + (5261937189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88161129/400000000 : ℝ)^4129 ≤ (13384936115877/100000000000000 : ℝ)^3105 := by
    have hnat : (88161129 : ℕ)^4129*100000000000000^3105 ≤ 13384936115877^3105*400000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88161129 400000000 13384936115877 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349256117/2500000000 : ℝ)^4129 ≤ (2752335823371/6250000000000 : ℝ)^3105 := by
    have hnat : (1349256117 : ℕ)^4129*6250000000000^3105 ≤ 2752335823371^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349256117 2500000000 2752335823371 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261937189/10000000000 : ℝ)^4129 ≤ (42577690689577/100000000000000 : ℝ)^3105 := by
    have hnat : (5261937189 : ℕ)^4129*100000000000000^3105 ≤ 42577690689577^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261937189 10000000000 42577690689577 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88161129/400000000 : ℝ), (1349256117/2500000000 : ℝ), (5261937189/10000000000 : ℝ)] ![(13384936115877/100000000000000 : ℝ), (2752335823371/6250000000000 : ℝ), (42577690689577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88161129/400000000 : ℝ)|^4129 ≤ (13384936115877/100000000000000 : ℝ)^3105
        have hw : |(-88161129/400000000 : ℝ)|=(88161129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349256117/2500000000 : ℝ)|^4129 ≤ (2752335823371/6250000000000 : ℝ)^3105
        have hw : |(1349256117/2500000000 : ℝ)|=(1349256117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261937189/10000000000 : ℝ)|^4129 ≤ (42577690689577/100000000000000 : ℝ)^3105
        have hw : |(5261937189/10000000000 : ℝ)|=(5261937189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672821147/5000000000 : ℝ)*x 0 + (-1136303433/5000000000 : ℝ)*x 1 + (526193723/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672821147/5000000000 : ℝ)^4129 ≤ (21740363653897/50000000000000 : ℝ)^3105 := by
    have hnat : (2672821147 : ℕ)^4129*50000000000000^3105 ≤ 21740363653897^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672821147 5000000000 21740363653897 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136303433/5000000000 : ℝ)^4129 ≤ (13941581543603/100000000000000 : ℝ)^3105 := by
    have hnat : (1136303433 : ℕ)^4129*100000000000000^3105 ≤ 13941581543603^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136303433 5000000000 13941581543603 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526193723/1000000000 : ℝ)^4129 ≤ (5322211391343/12500000000000 : ℝ)^3105 := by
    have hnat : (526193723 : ℕ)^4129*12500000000000^3105 ≤ 5322211391343^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526193723 1000000000 5322211391343 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672821147/5000000000 : ℝ), (-1136303433/5000000000 : ℝ), (526193723/1000000000 : ℝ)] ![(21740363653897/50000000000000 : ℝ), (13941581543603/100000000000000 : ℝ), (5322211391343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672821147/5000000000 : ℝ)|^4129 ≤ (21740363653897/50000000000000 : ℝ)^3105
        have hw : |(2672821147/5000000000 : ℝ)|=(2672821147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136303433/5000000000 : ℝ)|^4129 ≤ (13941581543603/100000000000000 : ℝ)^3105
        have hw : |(-1136303433/5000000000 : ℝ)|=(1136303433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526193723/1000000000 : ℝ)|^4129 ≤ (5322211391343/12500000000000 : ℝ)^3105
        have hw : |(526193723/1000000000 : ℝ)|=(526193723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267282109/500000000 : ℝ)*x 0 + (82217769/156250000 : ℝ)*x 1 + (-568151759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267282109/500000000 : ℝ)^4129 ≤ (10870181518683/25000000000000 : ℝ)^3105 := by
    have hnat : (267282109 : ℕ)^4129*25000000000000^3105 ≤ 10870181518683^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267282109 500000000 10870181518683 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82217769/156250000 : ℝ)^4129 ≤ (21288845490051/50000000000000 : ℝ)^3105 := by
    have hnat : (82217769 : ℕ)^4129*50000000000000^3105 ≤ 21288845490051^3105*156250000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82217769 156250000 21288845490051 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568151759/2500000000 : ℝ)^4129 ≤ (6970791465211/50000000000000 : ℝ)^3105 := by
    have hnat : (568151759 : ℕ)^4129*50000000000000^3105 ≤ 6970791465211^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568151759 2500000000 6970791465211 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267282109/500000000 : ℝ), (82217769/156250000 : ℝ), (-568151759/2500000000 : ℝ)] ![(10870181518683/25000000000000 : ℝ), (21288845490051/50000000000000 : ℝ), (6970791465211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267282109/500000000 : ℝ)|^4129 ≤ (10870181518683/25000000000000 : ℝ)^3105
        have hw : |(267282109/500000000 : ℝ)|=(267282109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82217769/156250000 : ℝ)|^4129 ≤ (21288845490051/50000000000000 : ℝ)^3105
        have hw : |(82217769/156250000 : ℝ)|=(82217769/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-568151759/2500000000 : ℝ)|^4129 ≤ (6970791465211/50000000000000 : ℝ)^3105
        have hw : |(-568151759/2500000000 : ℝ)|=(568151759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1093875527/2500000000 : ℝ)*x 0 + (1061295053/2500000000 : ℝ)*x 1 + (281867531/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093875527/2500000000 : ℝ)^4129 ≤ (33315186644277/100000000000000 : ℝ)^3105 := by
    have hnat : (1093875527 : ℕ)^4129*100000000000000^3105 ≤ 33315186644277^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093875527 2500000000 33315186644277 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061295053/2500000000 : ℝ)^4129 ≤ (16001096889841/50000000000000 : ℝ)^3105 := by
    have hnat : (1061295053 : ℕ)^4129*50000000000000^3105 ≤ 16001096889841^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061295053 2500000000 16001096889841 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281867531/625000000 : ℝ)^4129 ≤ (17341309785267/50000000000000 : ℝ)^3105 := by
    have hnat : (281867531 : ℕ)^4129*50000000000000^3105 ≤ 17341309785267^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281867531 625000000 17341309785267 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093875527/2500000000 : ℝ), (1061295053/2500000000 : ℝ), (281867531/625000000 : ℝ)] ![(33315186644277/100000000000000 : ℝ), (16001096889841/50000000000000 : ℝ), (17341309785267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093875527/2500000000 : ℝ)|^4129 ≤ (33315186644277/100000000000000 : ℝ)^3105
        have hw : |(1093875527/2500000000 : ℝ)|=(1093875527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061295053/2500000000 : ℝ)|^4129 ≤ (16001096889841/50000000000000 : ℝ)^3105
        have hw : |(1061295053/2500000000 : ℝ)|=(1061295053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281867531/625000000 : ℝ)|^4129 ≤ (17341309785267/50000000000000 : ℝ)^3105
        have hw : |(281867531/625000000 : ℝ)|=(281867531/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-34438031/156250000 : ℝ)*x 0 + (657786099/1250000000 : ℝ)*x 1 + (2698335749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34438031/156250000 : ℝ)^4129 ≤ (6692491312047/50000000000000 : ℝ)^3105 := by
    have hnat : (34438031 : ℕ)^4129*50000000000000^3105 ≤ 6692491312047^3105*156250000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34438031 156250000 6692491312047 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657786099/1250000000 : ℝ)^4129 ≤ (42581474044441/100000000000000 : ℝ)^3105 := by
    have hnat : (657786099 : ℕ)^4129*100000000000000^3105 ≤ 42581474044441^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657786099 1250000000 42581474044441 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698335749/5000000000 : ℝ)^4129 ≤ (11008385827361/25000000000000 : ℝ)^3105 := by
    have hnat : (2698335749 : ℕ)^4129*25000000000000^3105 ≤ 11008385827361^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698335749 5000000000 11008385827361 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34438031/156250000 : ℝ), (657786099/1250000000 : ℝ), (2698335749/5000000000 : ℝ)] ![(6692491312047/50000000000000 : ℝ), (42581474044441/100000000000000 : ℝ), (11008385827361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34438031/156250000 : ℝ)|^4129 ≤ (6692491312047/50000000000000 : ℝ)^3105
        have hw : |(-34438031/156250000 : ℝ)|=(34438031/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657786099/1250000000 : ℝ)|^4129 ≤ (42581474044441/100000000000000 : ℝ)^3105
        have hw : |(657786099/1250000000 : ℝ)|=(657786099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698335749/5000000000 : ℝ)|^4129 ≤ (11008385827361/25000000000000 : ℝ)^3105
        have hw : |(2698335749/5000000000 : ℝ)|=(2698335749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327904911/2500000000 : ℝ)*x 0 + (-85514907/400000000 : ℝ)*x 1 + (2698335741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327904911/2500000000 : ℝ)^4129 ≤ (21556556821817/50000000000000 : ℝ)^3105 := by
    have hnat : (1327904911 : ℕ)^4129*50000000000000^3105 ≤ 21556556821817^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327904911 2500000000 21556556821817 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85514907/400000000 : ℝ)^4129 ≤ (12853343200137/100000000000000 : ℝ)^3105 := by
    have hnat : (85514907 : ℕ)^4129*100000000000000^3105 ≤ 12853343200137^3105*400000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85514907 400000000 12853343200137 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698335741/5000000000 : ℝ)^4129 ≤ (44033543135839/100000000000000 : ℝ)^3105 := by
    have hnat : (2698335741 : ℕ)^4129*100000000000000^3105 ≤ 44033543135839^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698335741 5000000000 44033543135839 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327904911/2500000000 : ℝ), (-85514907/400000000 : ℝ), (2698335741/5000000000 : ℝ)] ![(21556556821817/50000000000000 : ℝ), (12853343200137/100000000000000 : ℝ), (44033543135839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327904911/2500000000 : ℝ)|^4129 ≤ (21556556821817/50000000000000 : ℝ)^3105
        have hw : |(1327904911/2500000000 : ℝ)|=(1327904911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85514907/400000000 : ℝ)|^4129 ≤ (12853343200137/100000000000000 : ℝ)^3105
        have hw : |(-85514907/400000000 : ℝ)|=(85514907/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698335741/5000000000 : ℝ)|^4129 ≤ (44033543135839/100000000000000 : ℝ)^3105
        have hw : |(2698335741/5000000000 : ℝ)|=(2698335741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327904913/2500000000 : ℝ)*x 0 + (5396671489/10000000000 : ℝ)*x 1 + (-427574531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327904913/2500000000 : ℝ)^4129 ≤ (43113113729983/100000000000000 : ℝ)^3105 := by
    have hnat : (1327904913 : ℕ)^4129*100000000000000^3105 ≤ 43113113729983^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327904913 2500000000 43113113729983 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396671489/10000000000 : ℝ)^4129 ≤ (44033543211791/100000000000000 : ℝ)^3105 := by
    have hnat : (5396671489 : ℕ)^4129*100000000000000^3105 ≤ 44033543211791^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396671489 10000000000 44033543211791 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427574531/2000000000 : ℝ)^4129 ≤ (12853343040237/100000000000000 : ℝ)^3105 := by
    have hnat : (427574531 : ℕ)^4129*100000000000000^3105 ≤ 12853343040237^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427574531 2000000000 12853343040237 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327904913/2500000000 : ℝ), (5396671489/10000000000 : ℝ), (-427574531/2000000000 : ℝ)] ![(43113113729983/100000000000000 : ℝ), (44033543211791/100000000000000 : ℝ), (12853343040237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327904913/2500000000 : ℝ)|^4129 ≤ (43113113729983/100000000000000 : ℝ)^3105
        have hw : |(1327904913/2500000000 : ℝ)|=(1327904913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396671489/10000000000 : ℝ)|^4129 ≤ (44033543211791/100000000000000 : ℝ)^3105
        have hw : |(5396671489/10000000000 : ℝ)|=(5396671489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427574531/2000000000 : ℝ)|^4129 ≤ (12853343040237/100000000000000 : ℝ)^3105
        have hw : |(-427574531/2000000000 : ℝ)|=(427574531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s5_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4375513337/10000000000 : ℝ)*x 0 + (1127297791/2500000000 : ℝ)*x 1 + (4245872053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375513337/10000000000 : ℝ)^4129 ≤ (33315300338631/100000000000000 : ℝ)^3105 := by
    have hnat : (4375513337 : ℕ)^4129*100000000000000^3105 ≤ 33315300338631^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375513337 10000000000 33315300338631 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127297791/2500000000 : ℝ)^4129 ≤ (17337785121987/50000000000000 : ℝ)^3105 := by
    have hnat : (1127297791 : ℕ)^4129*50000000000000^3105 ≤ 17337785121987^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127297791 2500000000 17337785121987 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245872053/10000000000 : ℝ)^4129 ≤ (3200912939287/10000000000000 : ℝ)^3105 := by
    have hnat : (4245872053 : ℕ)^4129*10000000000000^3105 ≤ 3200912939287^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245872053 10000000000 3200912939287 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375513337/10000000000 : ℝ), (1127297791/2500000000 : ℝ), (4245872053/10000000000 : ℝ)] ![(33315300338631/100000000000000 : ℝ), (17337785121987/50000000000000 : ℝ), (3200912939287/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375513337/10000000000 : ℝ)|^4129 ≤ (33315300338631/100000000000000 : ℝ)^3105
        have hw : |(4375513337/10000000000 : ℝ)|=(4375513337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127297791/2500000000 : ℝ)|^4129 ≤ (17337785121987/50000000000000 : ℝ)^3105
        have hw : |(1127297791/2500000000 : ℝ)|=(1127297791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245872053/10000000000 : ℝ)|^4129 ≤ (3200912939287/10000000000000 : ℝ)^3105
        have hw : |(4245872053/10000000000 : ℝ)|=(4245872053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11197/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (551/5000 : ℝ) ^ (8257/2048 : ℝ) ≤ (687538262765469/5000000000000000000 : ℝ) := by
    have hpowers : (551/5000 : ℝ)^8257 ≤ (687538262765469/5000000000000000000 : ℝ)^2048 := by
      have hnat : (551 : ℕ)^8257*5000000000000000000^2048 ≤ 687538262765469^2048*5000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        551 5000 687538262765469 5000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (551/5000 : ℝ)) (X := (687538262765469/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14243/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (38685005478269113/100000000000000000000 : ℝ) := by
    have hpowers : (14243/100000 : ℝ)^8257 ≤ (38685005478269113/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14243 : ℕ)^8257*100000000000000000000^2048 ≤ 38685005478269113^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14243 100000 38685005478269113 100000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14243/100000 : ℝ)) (X := (38685005478269113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500687538262765469/2500000000000000000 : ℝ) ≤ (10000682055365537/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (2500687538262765469/2500000000000000000 : ℝ)^2048 ≤ (10000682055365537/10000000000000000 : ℝ)^8257 := by
      have hnat : (2500687538262765469 : ℕ)^2048*10000000000000000^8257 ≤ 10000682055365537^8257*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500687538262765469 2500000000000000000 10000682055365537 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682055365537/10000000000000000 : ℝ)) (X := (2500687538262765469/2500000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052435770733578493/100000000000000000000 : ℝ) ≤ (10001300318436433/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (100052435770733578493/100000000000000000000 : ℝ)^2048 ≤ (10001300318436433/10000000000000000 : ℝ)^8257 := by
      have hnat : (100052435770733578493 : ℕ)^2048*10000000000000000^8257 ≤ 10001300318436433^8257*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052435770733578493 100000000000000000000 10001300318436433 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001300318436433/10000000000000000 : ℝ)) (X := (100052435770733578493/100000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038685005478269113/50000000000000000000 : ℝ) ≤ (10001918581507329/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (50038685005478269113/50000000000000000000 : ℝ)^2048 ≤ (10001918581507329/10000000000000000 : ℝ)^8257 := by
      have hnat : (50038685005478269113 : ℕ)^2048*10000000000000000^8257 ≤ 10001918581507329^8257*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038685005478269113 50000000000000000000 10001918581507329 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001918581507329/10000000000000000 : ℝ)) (X := (50038685005478269113/50000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(687538262765469/5000000000000000000 : ℝ) ≤ ((32218571746360577911/32230000000000000000 : ℝ)+2*(38641441931/20143750000000 : ℝ)*(551/5000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (32218571746360577911/32230000000000000000 : ℝ)+2*(38641441931/20143750000000 : ℝ)*(551/5000 : ℝ)=(10000682055365537/10000000000000000 : ℝ) by norm_num, show 1+2*(687538262765469/5000000000000000000 : ℝ)=(2500687538262765469/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38685005478269113/100000000000000000000 : ℝ)+(687538262765469/5000000000000000000 : ℝ) ≤ ((32218571746360577911/32230000000000000000 : ℝ)+(38641441931/20143750000000 : ℝ)*((14243/100000 : ℝ)+(551/5000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (32218571746360577911/32230000000000000000 : ℝ)+(38641441931/20143750000000 : ℝ)*((14243/100000 : ℝ)+(551/5000 : ℝ))=(10001300318436433/10000000000000000 : ℝ) by norm_num, show 1+(38685005478269113/100000000000000000000 : ℝ)+(687538262765469/5000000000000000000 : ℝ)=(100052435770733578493/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38685005478269113/100000000000000000000 : ℝ) ≤ ((32218571746360577911/32230000000000000000 : ℝ)+2*(38641441931/20143750000000 : ℝ)*(14243/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (32218571746360577911/32230000000000000000 : ℝ)+2*(38641441931/20143750000000 : ℝ)*(14243/100000 : ℝ)=(10001918581507329/10000000000000000 : ℝ) by norm_num, show 1+2*(38685005478269113/100000000000000000000 : ℝ)=(50038685005478269113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32218571746360577911/32230000000000000000 : ℝ)*(X 1 0+X 2 0)+(38641441931/20143750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (32218571746360577911/32230000000000000000 : ℝ)) (alpha := (38641441931/20143750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32218571746360577911/32230000000000000000 : ℝ)*(X 0 1+X 2 1)+(38641441931/20143750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (32218571746360577911/32230000000000000000 : ℝ)) (alpha := (38641441931/20143750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32218571746360577911/32230000000000000000 : ℝ)*(X 0 2+X 1 2)+(38641441931/20143750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (32218571746360577911/32230000000000000000 : ℝ)) (alpha := (38641441931/20143750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-88161129/400000000 : ℝ)*X 0 0+(1349256117/2500000000 : ℝ)*X 0 1+(5261937189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672821147/5000000000 : ℝ)*X 1 0+(-1136303433/5000000000 : ℝ)*X 1 1+(526193723/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267282109/500000000 : ℝ)*X 2 0+(82217769/156250000 : ℝ)*X 2 1+(-568151759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093875527/2500000000 : ℝ)*X 0 0+(1061295053/2500000000 : ℝ)*X 0 1+(281867531/625000000 : ℝ)*X 0 2+(1093875527/2500000000 : ℝ)*X 1 0+(1061295053/2500000000 : ℝ)*X 1 1+(281867531/625000000 : ℝ)*X 1 2+(1093875527/2500000000 : ℝ)*X 2 0+(1061295053/2500000000 : ℝ)*X 2 1+(281867531/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-34438031/156250000 : ℝ)*X 0 0+(657786099/1250000000 : ℝ)*X 0 1+(2698335749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327904911/2500000000 : ℝ)*X 1 0+(-85514907/400000000 : ℝ)*X 1 1+(2698335741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327904913/2500000000 : ℝ)*X 2 0+(5396671489/10000000000 : ℝ)*X 2 1+(-427574531/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375513337/10000000000 : ℝ)*X 0 0+(1127297791/2500000000 : ℝ)*X 0 1+(4245872053/10000000000 : ℝ)*X 0 2+(4375513337/10000000000 : ℝ)*X 1 0+(1127297791/2500000000 : ℝ)*X 1 1+(4245872053/10000000000 : ℝ)*X 1 2+(4375513337/10000000000 : ℝ)*X 2 0+(1127297791/2500000000 : ℝ)*X 2 1+(4245872053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1044956470402949576228047869/201437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (783747809/100000000000000 : ℝ)*(base19) + (748003173/100000000000000 : ℝ)*(base23) + (33230867/25000000000000 : ℝ)*(upper3) + (72257133/100000000000000 : ℝ)*(lower4) + (1397570349727007/25000000000000 : ℝ)*(major0) + (1397570349727007/25000000000000 : ℝ)*(major1) + (1397570349727007/25000000000000 : ℝ)*(major2) + (1850662809531671/25000000000000 : ℝ)*(sp0) + (1850667600671109/25000000000000 : ℝ)*(sp1) + (185066709711651/2500000000000 : ℝ)*(sp2) + (3777874010260559/100000000000000 : ℝ)*(sp3) + (19948305561/100000000000000 : ℝ)*(sp4) + (256245379/12500000000000 : ℝ)*(sp6) + (1742820667/10000000000000 : ℝ)*(sp7) + (3777891438467229/100000000000000 : ℝ)*(f.failure) + (1480534237286449/20000000000000 : ℝ)*(f.sum) + (293411453641/8057500000000000000000000000 : ℝ)*base66 + (10361474771662542377/805750000000000000000000000000000 : ℝ)*base67 + (6450200208070542377/805750000000000000000000000000000 : ℝ)*base69 + (10388343686642042377/805750000000000000000000000000000 : ℝ)*base71 + (310518826927/4028750000000000000000000000 : ℝ)*base73 + (16076092078671042377/805750000000000000000000000000000 : ℝ)*base75 + (367722548667957623/805750000000000000000000000000000 : ℝ)*base78 + (11768908218994542377/805750000000000000000000000000000 : ℝ)*base79 + (20915197909461/8057500000000000000000000000 : ℝ)*base82 + (3970807/2000000000000000000000 : ℝ)*base90 + (3970807/2000000000000000000000 : ℝ)*base92 + (3970807/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (348309228306769571795842863/50359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (638057927/50000000000000 : ℝ)*(base19) + (717980049/50000000000000 : ℝ)*(base23) + (138709007/100000000000000 : ℝ)*(upper3) + (64016181/100000000000000 : ℝ)*(lower4) + (70816221/50000000000000 : ℝ)*(upper5) + (175611026182787/3125000000000 : ℝ)*(major0) + (175611026182787/3125000000000 : ℝ)*(major1) + (175611026182787/3125000000000 : ℝ)*(major2) + (8105265437/25000000000000 : ℝ)*(sp1) + (36810580363/100000000000000 : ℝ)*(sp2) + (7441432476795379/100000000000000 : ℝ)*(sp4) + (465087423726111/6250000000000 : ℝ)*(sp5) + (7441394230254917/100000000000000 : ℝ)*(sp6) + (1898836484176951/50000000000000 : ℝ)*(sp7) + (1898836484176951/50000000000000 : ℝ)*(f.failure) + (7441432476795379/100000000000000 : ℝ)*(f.sum) + (37041732785747/8057500000000000000000000000 : ℝ)*base65 + (617695078500682043/100718750000000000000000000000000 : ℝ)*base68 + (378165188463057043/100718750000000000000000000000000 : ℝ)*base70 + (476914290846994543/100718750000000000000000000000000 : ℝ)*base72 + (251913794529/1007187500000000000000000000 : ℝ)*base73 + (811470780512744543/100718750000000000000000000000000 : ℝ)*base76 + (127599363492744543/100718750000000000000000000000000 : ℝ)*base78 + (961685732832525793/100718750000000000000000000000000 : ℝ)*base80 + (32544779809019/16115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2767867/1000000000000000000000 : ℝ)*base89 + (2767867/1000000000000000000000 : ℝ)*base91 + (2767867/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1065_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1065_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1065_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1065_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2093/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8707/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

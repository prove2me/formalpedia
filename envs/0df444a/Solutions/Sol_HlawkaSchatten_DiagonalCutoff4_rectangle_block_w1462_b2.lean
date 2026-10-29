-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1462_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:35.408131+00:00
-- url     : https://prove2.me/submissions/8a1c5510-616a-4e66-ae4a-4793d977e819

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
theorem support_rectangle_w1462_s6_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1944666803/10000000000 : ℝ)*x 0 + (1081303973/2000000000 : ℝ)*x 1 + (209903803/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1944666803/10000000000 : ℝ)^2211 ≤ (11872332299581/100000000000000 : ℝ)^1699 := by
    have hnat : (1944666803 : ℕ)^2211*100000000000000^1699 ≤ 11872332299581^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944666803 10000000000 11872332299581 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081303973/2000000000 : ℝ)^2211 ≤ (8983831142097/20000000000000 : ℝ)^1699 := by
    have hnat : (1081303973 : ℕ)^2211*20000000000000^1699 ≤ 8983831142097^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081303973 2000000000 8983831142097 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209903803/400000000 : ℝ)^2211 ≤ (5401063997909/12500000000000 : ℝ)^1699 := by
    have hnat : (209903803 : ℕ)^2211*12500000000000^1699 ≤ 5401063997909^1699*400000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209903803 400000000 5401063997909 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1944666803/10000000000 : ℝ), (1081303973/2000000000 : ℝ), (209903803/400000000 : ℝ)] ![(11872332299581/100000000000000 : ℝ), (8983831142097/20000000000000 : ℝ), (5401063997909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1944666803/10000000000 : ℝ)|^2211 ≤ (11872332299581/100000000000000 : ℝ)^1699
        have hw : |(-1944666803/10000000000 : ℝ)|=(1944666803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081303973/2000000000 : ℝ)|^2211 ≤ (8983831142097/20000000000000 : ℝ)^1699
        have hw : |(1081303973/2000000000 : ℝ)|=(1081303973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209903803/400000000 : ℝ)|^2211 ≤ (5401063997909/12500000000000 : ℝ)^1699
        have hw : |(209903803/400000000 : ℝ)|=(209903803/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673306271/5000000000 : ℝ)*x 0 + (-506388889/2500000000 : ℝ)*x 1 + (1049519/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673306271/5000000000 : ℝ)^2211 ≤ (44272517330387/100000000000000 : ℝ)^1699 := by
    have hnat : (2673306271 : ℕ)^2211*100000000000000^1699 ≤ 44272517330387^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673306271 5000000000 44272517330387 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506388889/2500000000 : ℝ)^2211 ≤ (1564871434587/12500000000000 : ℝ)^1699 := by
    have hnat : (506388889 : ℕ)^2211*12500000000000^1699 ≤ 1564871434587^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506388889 2500000000 1564871434587 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049519/2000000 : ℝ)^2211 ≤ (5401063897453/12500000000000 : ℝ)^1699 := by
    have hnat : (1049519 : ℕ)^2211*12500000000000^1699 ≤ 5401063897453^1699*2000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049519 2000000 5401063897453 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673306271/5000000000 : ℝ), (-506388889/2500000000 : ℝ), (1049519/2000000 : ℝ)] ![(44272517330387/100000000000000 : ℝ), (1564871434587/12500000000000 : ℝ), (5401063897453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673306271/5000000000 : ℝ)|^2211 ≤ (44272517330387/100000000000000 : ℝ)^1699
        have hw : |(2673306271/5000000000 : ℝ)|=(2673306271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-506388889/2500000000 : ℝ)|^2211 ≤ (1564871434587/12500000000000 : ℝ)^1699
        have hw : |(-506388889/2500000000 : ℝ)|=(506388889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049519/2000000 : ℝ)|^2211 ≤ (5401063897453/12500000000000 : ℝ)^1699
        have hw : |(1049519/2000000 : ℝ)|=(1049519/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673305907/5000000000 : ℝ)*x 0 + (5247596127/10000000000 : ℝ)*x 1 + (-2025555029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673305907/5000000000 : ℝ)^2211 ≤ (44272509485581/100000000000000 : ℝ)^1699 := by
    have hnat : (2673305907 : ℕ)^2211*100000000000000^1699 ≤ 44272509485581^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673305907 5000000000 44272509485581 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247596127/10000000000 : ℝ)^2211 ≤ (5401065406971/12500000000000 : ℝ)^1699 := by
    have hnat : (5247596127 : ℕ)^2211*12500000000000^1699 ≤ 5401065406971^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247596127 10000000000 5401065406971 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025555029/10000000000 : ℝ)^2211 ≤ (6259483619009/50000000000000 : ℝ)^1699 := by
    have hnat : (2025555029 : ℕ)^2211*50000000000000^1699 ≤ 6259483619009^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025555029 10000000000 6259483619009 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673305907/5000000000 : ℝ), (5247596127/10000000000 : ℝ), (-2025555029/10000000000 : ℝ)] ![(44272509485581/100000000000000 : ℝ), (5401065406971/12500000000000 : ℝ), (6259483619009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673305907/5000000000 : ℝ)|^2211 ≤ (44272509485581/100000000000000 : ℝ)^1699
        have hw : |(2673305907/5000000000 : ℝ)|=(2673305907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247596127/10000000000 : ℝ)|^2211 ≤ (5401065406971/12500000000000 : ℝ)^1699
        have hw : |(5247596127/10000000000 : ℝ)|=(5247596127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2025555029/10000000000 : ℝ)|^2211 ≤ (6259483619009/50000000000000 : ℝ)^1699
        have hw : |(-2025555029/10000000000 : ℝ)|=(2025555029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4296188921/10000000000 : ℝ)*x 0 + (4125332621/10000000000 : ℝ)*x 1 + (2236648267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296188921/10000000000 : ℝ)^2211 ≤ (8326292854493/25000000000000 : ℝ)^1699 := by
    have hnat : (4296188921 : ℕ)^2211*25000000000000^1699 ≤ 8326292854493^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296188921 10000000000 8326292854493 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125332621/10000000000 : ℝ)^2211 ≤ (7897981340247/25000000000000 : ℝ)^1699 := by
    have hnat : (4125332621 : ℕ)^2211*25000000000000^1699 ≤ 7897981340247^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125332621 10000000000 7897981340247 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236648267/5000000000 : ℝ)^2211 ≤ (17551451604231/50000000000000 : ℝ)^1699 := by
    have hnat : (2236648267 : ℕ)^2211*50000000000000^1699 ≤ 17551451604231^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236648267 5000000000 17551451604231 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296188921/10000000000 : ℝ), (4125332621/10000000000 : ℝ), (2236648267/5000000000 : ℝ)] ![(8326292854493/25000000000000 : ℝ), (7897981340247/25000000000000 : ℝ), (17551451604231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296188921/10000000000 : ℝ)|^2211 ≤ (8326292854493/25000000000000 : ℝ)^1699
        have hw : |(4296188921/10000000000 : ℝ)|=(4296188921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4125332621/10000000000 : ℝ)|^2211 ≤ (7897981340247/25000000000000 : ℝ)^1699
        have hw : |(4125332621/10000000000 : ℝ)|=(4125332621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2236648267/5000000000 : ℝ)|^2211 ≤ (17551451604231/50000000000000 : ℝ)^1699
        have hw : |(2236648267/5000000000 : ℝ)|=(2236648267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-60771179/312500000 : ℝ)*x 0 + (2624085421/5000000000 : ℝ)*x 1 + (1351485301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60771179/312500000 : ℝ)^2211 ≤ (11872419097241/100000000000000 : ℝ)^1699 := by
    have hnat : (60771179 : ℕ)^2211*100000000000000^1699 ≤ 11872419097241^1699*312500000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60771179 312500000 11872419097241 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624085421/5000000000 : ℝ)^2211 ≤ (8642936320347/20000000000000 : ℝ)^1699 := by
    have hnat : (2624085421 : ℕ)^2211*20000000000000^1699 ≤ 8642936320347^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624085421 5000000000 8642936320347 20000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351485301/2500000000 : ℝ)^2211 ≤ (22456449641937/50000000000000 : ℝ)^1699 := by
    have hnat : (1351485301 : ℕ)^2211*50000000000000^1699 ≤ 22456449641937^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351485301 2500000000 22456449641937 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60771179/312500000 : ℝ), (2624085421/5000000000 : ℝ), (1351485301/2500000000 : ℝ)] ![(11872419097241/100000000000000 : ℝ), (8642936320347/20000000000000 : ℝ), (22456449641937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60771179/312500000 : ℝ)|^2211 ≤ (11872419097241/100000000000000 : ℝ)^1699
        have hw : |(-60771179/312500000 : ℝ)|=(60771179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624085421/5000000000 : ℝ)|^2211 ≤ (8642936320347/20000000000000 : ℝ)^1699
        have hw : |(2624085421/5000000000 : ℝ)|=(2624085421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351485301/2500000000 : ℝ)|^2211 ≤ (22456449641937/50000000000000 : ℝ)^1699
        have hw : |(1351485301/2500000000 : ℝ)|=(1351485301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305166531/10000000000 : ℝ)*x 0 + (-116700613/625000000 : ℝ)*x 1 + (5405941259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305166531/10000000000 : ℝ)^2211 ≤ (43826424622467/100000000000000 : ℝ)^1699 := by
    have hnat : (5305166531 : ℕ)^2211*100000000000000^1699 ≤ 43826424622467^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305166531 10000000000 43826424622467 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116700613/625000000 : ℝ)^2211 ≤ (5630337739523/50000000000000 : ℝ)^1699 := by
    have hnat : (116700613 : ℕ)^2211*50000000000000^1699 ≤ 5630337739523^1699*625000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116700613 625000000 5630337739523 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405941259/10000000000 : ℝ)^2211 ≤ (44912899878519/100000000000000 : ℝ)^1699 := by
    have hnat : (5405941259 : ℕ)^2211*100000000000000^1699 ≤ 44912899878519^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405941259 10000000000 44912899878519 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305166531/10000000000 : ℝ), (-116700613/625000000 : ℝ), (5405941259/10000000000 : ℝ)] ![(43826424622467/100000000000000 : ℝ), (5630337739523/50000000000000 : ℝ), (44912899878519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305166531/10000000000 : ℝ)|^2211 ≤ (43826424622467/100000000000000 : ℝ)^1699
        have hw : |(5305166531/10000000000 : ℝ)|=(5305166531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116700613/625000000 : ℝ)|^2211 ≤ (5630337739523/50000000000000 : ℝ)^1699
        have hw : |(-116700613/625000000 : ℝ)|=(116700613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405941259/10000000000 : ℝ)|^2211 ≤ (44912899878519/100000000000000 : ℝ)^1699
        have hw : |(5405941259/10000000000 : ℝ)|=(5405941259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061033273/2000000000 : ℝ)*x 0 + (2702970733/5000000000 : ℝ)*x 1 + (-1867209751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061033273/2000000000 : ℝ)^2211 ≤ (10956605709467/25000000000000 : ℝ)^1699 := by
    have hnat : (1061033273 : ℕ)^2211*25000000000000^1699 ≤ 10956605709467^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061033273 2000000000 10956605709467 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702970733/5000000000 : ℝ)^2211 ≤ (44912902116547/100000000000000 : ℝ)^1699 := by
    have hnat : (2702970733 : ℕ)^2211*100000000000000^1699 ≤ 44912902116547^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702970733 5000000000 44912902116547 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867209751/10000000000 : ℝ)^2211 ≤ (5630337515851/50000000000000 : ℝ)^1699 := by
    have hnat : (1867209751 : ℕ)^2211*50000000000000^1699 ≤ 5630337515851^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867209751 10000000000 5630337515851 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061033273/2000000000 : ℝ), (2702970733/5000000000 : ℝ), (-1867209751/10000000000 : ℝ)] ![(10956605709467/25000000000000 : ℝ), (44912902116547/100000000000000 : ℝ), (5630337515851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061033273/2000000000 : ℝ)|^2211 ≤ (10956605709467/25000000000000 : ℝ)^1699
        have hw : |(1061033273/2000000000 : ℝ)|=(1061033273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702970733/5000000000 : ℝ)|^2211 ≤ (44912902116547/100000000000000 : ℝ)^1699
        have hw : |(2702970733/5000000000 : ℝ)|=(2702970733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867209751/10000000000 : ℝ)|^2211 ≤ (5630337515851/50000000000000 : ℝ)^1699
        have hw : |(-1867209751/10000000000 : ℝ)|=(1867209751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_s6_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4296214081/10000000000 : ℝ)*x 0 + (2236019047/5000000000 : ℝ)*x 1 + (2063298283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296214081/10000000000 : ℝ)^2211 ≤ (33305425243143/100000000000000 : ℝ)^1699 := by
    have hnat : (4296214081 : ℕ)^2211*100000000000000^1699 ≤ 33305425243143^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296214081 10000000000 33305425243143 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236019047/5000000000 : ℝ)^2211 ≤ (17545026283377/50000000000000 : ℝ)^1699 := by
    have hnat : (2236019047 : ℕ)^2211*50000000000000^1699 ≤ 17545026283377^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236019047 5000000000 17545026283377 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063298283/5000000000 : ℝ)^2211 ≤ (31604522174823/100000000000000 : ℝ)^1699 := by
    have hnat : (2063298283 : ℕ)^2211*100000000000000^1699 ≤ 31604522174823^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063298283 5000000000 31604522174823 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296214081/10000000000 : ℝ), (2236019047/5000000000 : ℝ), (2063298283/5000000000 : ℝ)] ![(33305425243143/100000000000000 : ℝ), (17545026283377/50000000000000 : ℝ), (31604522174823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296214081/10000000000 : ℝ)|^2211 ≤ (33305425243143/100000000000000 : ℝ)^1699
        have hw : |(4296214081/10000000000 : ℝ)|=(4296214081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236019047/5000000000 : ℝ)|^2211 ≤ (17545026283377/50000000000000 : ℝ)^1699
        have hw : |(2236019047/5000000000 : ℝ)|=(2236019047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063298283/5000000000 : ℝ)|^2211 ≤ (31604522174823/100000000000000 : ℝ)^1699
        have hw : |(2063298283/5000000000 : ℝ)|=(2063298283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5703/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11403/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (4243855412848461/50000000000000000000 : ℝ) := by
    have hpowers : (11403/100000 : ℝ)^4421 ≤ (4243855412848461/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11403 : ℕ)^4421*50000000000000000000^1024 ≤ 4243855412848461^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11403 100000 4243855412848461 50000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11403/100000 : ℝ)) (X := (4243855412848461/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (4421/1024 : ℝ) ≤ (25981197091883731/100000000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^4421 ≤ (25981197091883731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1847 : ℕ)^4421*100000000000000000000^1024 ≤ 25981197091883731^1024*12500^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 25981197091883731 100000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (25981197091883731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004243855412848461/25000000000000000000 : ℝ) ≤ (5000196581070073/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (25004243855412848461/25000000000000000000 : ℝ)^1024 ≤ (5000196581070073/5000000000000000 : ℝ)^4421 := by
      have hnat : (25004243855412848461 : ℕ)^1024*5000000000000000^4421 ≤ 5000196581070073^4421*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004243855412848461 25000000000000000000 5000196581070073 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000196581070073/5000000000000000 : ℝ)) (X := (25004243855412848461/25000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034468907917580653/100000000000000000000 : ℝ) ≤ (1000079826936293/1000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (100034468907917580653/100000000000000000000 : ℝ)^1024 ≤ (1000079826936293/1000000000000000 : ℝ)^4421 := by
      have hnat : (100034468907917580653 : ℕ)^1024*1000000000000000^4421 ≤ 1000079826936293^4421*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034468907917580653 100000000000000000000 1000079826936293 1000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000079826936293/1000000000000000 : ℝ)) (X := (100034468907917580653/100000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025981197091883731/50000000000000000000 : ℝ) ≤ (5000601688292857/5000000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (50025981197091883731/50000000000000000000 : ℝ)^1024 ≤ (5000601688292857/5000000000000000 : ℝ)^4421 := by
      have hnat : (50025981197091883731 : ℕ)^1024*5000000000000000^4421 ≤ 5000601688292857^4421*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025981197091883731 50000000000000000000 5000601688292857 5000000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000601688292857/5000000000000000 : ℝ)) (X := (50025981197091883731/50000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4243855412848461/50000000000000000000 : ℝ) ≤ ((16861043630287950277/16865000000000000000 : ℝ)+2*(1582450089/1317578125000 : ℝ)*(11403/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (16861043630287950277/16865000000000000000 : ℝ)+2*(1582450089/1317578125000 : ℝ)*(11403/100000 : ℝ)=(5000196581070073/5000000000000000 : ℝ) by norm_num, show 1+2*(4243855412848461/50000000000000000000 : ℝ)=(25004243855412848461/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25981197091883731/100000000000000000000 : ℝ)+(4243855412848461/50000000000000000000 : ℝ) ≤ ((16861043630287950277/16865000000000000000 : ℝ)+(1582450089/1317578125000 : ℝ)*((1847/12500 : ℝ)+(11403/100000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (16861043630287950277/16865000000000000000 : ℝ)+(1582450089/1317578125000 : ℝ)*((1847/12500 : ℝ)+(11403/100000 : ℝ))=(1000079826936293/1000000000000000 : ℝ) by norm_num, show 1+(25981197091883731/100000000000000000000 : ℝ)+(4243855412848461/50000000000000000000 : ℝ)=(100034468907917580653/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25981197091883731/100000000000000000000 : ℝ) ≤ ((16861043630287950277/16865000000000000000 : ℝ)+2*(1582450089/1317578125000 : ℝ)*(1847/12500 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (16861043630287950277/16865000000000000000 : ℝ)+2*(1582450089/1317578125000 : ℝ)*(1847/12500 : ℝ)=(5000601688292857/5000000000000000 : ℝ) by norm_num, show 1+2*(25981197091883731/100000000000000000000 : ℝ)=(50025981197091883731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16861043630287950277/16865000000000000000 : ℝ)*(X 1 0+X 2 0)+(1582450089/1317578125000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (16861043630287950277/16865000000000000000 : ℝ)) (alpha := (1582450089/1317578125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16861043630287950277/16865000000000000000 : ℝ)*(X 0 1+X 2 1)+(1582450089/1317578125000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (16861043630287950277/16865000000000000000 : ℝ)) (alpha := (1582450089/1317578125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16861043630287950277/16865000000000000000 : ℝ)*(X 0 2+X 1 2)+(1582450089/1317578125000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (16861043630287950277/16865000000000000000 : ℝ)) (alpha := (1582450089/1317578125000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1944666803/10000000000 : ℝ)*X 0 0+(1081303973/2000000000 : ℝ)*X 0 1+(209903803/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673306271/5000000000 : ℝ)*X 1 0+(-506388889/2500000000 : ℝ)*X 1 1+(1049519/2000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673305907/5000000000 : ℝ)*X 2 0+(5247596127/10000000000 : ℝ)*X 2 1+(-2025555029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296188921/10000000000 : ℝ)*X 0 0+(4125332621/10000000000 : ℝ)*X 0 1+(2236648267/5000000000 : ℝ)*X 0 2+(4296188921/10000000000 : ℝ)*X 1 0+(4125332621/10000000000 : ℝ)*X 1 1+(2236648267/5000000000 : ℝ)*X 1 2+(4296188921/10000000000 : ℝ)*X 2 0+(4125332621/10000000000 : ℝ)*X 2 1+(2236648267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-60771179/312500000 : ℝ)*X 0 0+(2624085421/5000000000 : ℝ)*X 0 1+(1351485301/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305166531/10000000000 : ℝ)*X 1 0+(-116700613/625000000 : ℝ)*X 1 1+(5405941259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061033273/2000000000 : ℝ)*X 2 0+(2702970733/5000000000 : ℝ)*X 2 1+(-1867209751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296214081/10000000000 : ℝ)*X 0 0+(2236019047/5000000000 : ℝ)*X 0 1+(2063298283/5000000000 : ℝ)*X 0 2+(4296214081/10000000000 : ℝ)*X 1 0+(2236019047/5000000000 : ℝ)*X 1 1+(2063298283/5000000000 : ℝ)*X 1 2+(4296214081/10000000000 : ℝ)*X 2 0+(2236019047/5000000000 : ℝ)*X 2 1+(2063298283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367142301118465230111/67460000000000000000000000 : ℝ) := by norm_num
    linear_combination (415393127/25000000000000 : ℝ)*(base19) + (48559249/25000000000000 : ℝ)*(base23) + (4383649/20000000000000 : ℝ)*(lower3) + (33645387/10000000000000 : ℝ)*(upper4) + (916624917940001/20000000000000 : ℝ)*(major0) + (916624917940001/20000000000000 : ℝ)*(major1) + (916624917940001/20000000000000 : ℝ)*(major2) + (3146165911229623/50000000000000 : ℝ)*(sp0) + (6292378433109201/100000000000000 : ℝ)*(sp1) + (6292382316082819/100000000000000 : ℝ)*(sp2) + (1436932111223919/50000000000000 : ℝ)*(sp3) + (6335982571/12500000000000 : ℝ)*(sp4) + (483127621/20000000000000 : ℝ)*(sp5) + (566305001/25000000000000 : ℝ)*(sp7) + (2873866487667843/100000000000000 : ℝ)*(f.failure) + (3146191255159907/50000000000000 : ℝ)*(f.sum) + (1976575454257/421625000000000000000000000 : ℝ)*base66 + (822584472610530277/337300000000000000000000000000000 : ℝ)*base67 + (5042132842287130277/337300000000000000000000000000000 : ℝ)*base69 + (3604277670852169723/337300000000000000000000000000000 : ℝ)*base72 + (1694491965939/337300000000000000000000000 : ℝ)*base73 + (3221450897524230277/337300000000000000000000000000000 : ℝ)*base75 + (1746213725695869723/337300000000000000000000000000000 : ℝ)*base78 + (1809894278858569723/337300000000000000000000000000000 : ℝ)*base80 + (17687648096919/3373000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (20364583/2000000000000000000000 : ℝ)*base89 + (20364583/2000000000000000000000 : ℝ)*base91 + (20364583/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2204645193829295511656194863/421625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (650308279/100000000000000 : ℝ)*(base19) + (266703607/50000000000000 : ℝ)*(base23) + (1446951/800000000000 : ℝ)*(lower1) + (76373633/50000000000000 : ℝ)*(upper3) + (4579883/25000000000000 : ℝ)*(lower4) + (34951869/100000000000000 : ℝ)*(upper5) + (2308287549571727/50000000000000 : ℝ)*(major0) + (2308287549571727/50000000000000 : ℝ)*(major1) + (2308287549571727/50000000000000 : ℝ)*(major2) + (375167767/6250000000000 : ℝ)*(sp2) + (1267661652288019/20000000000000 : ℝ)*(sp4) + (1267661522226363/20000000000000 : ℝ)*(sp5) + (6338301725348609/100000000000000 : ℝ)*(sp6) + (361855220318663/12500000000000 : ℝ)*(sp7) + (361855220318663/12500000000000 : ℝ)*(f.failure) + (1267661652288019/20000000000000 : ℝ)*(f.sum) + (10967015686803/2108125000000000000000000000 : ℝ)*base66 + (23368298407860081621/843250000000000000000000000000000 : ℝ)*base68 + (9832842279016418379/843250000000000000000000000000000 : ℝ)*base69 + (162608299208854831621/843250000000000000000000000000000 : ℝ)*base72 + (3133601441047/527031250000000000000000000 : ℝ)*base74 + (33057734374525168379/843250000000000000000000000000000 : ℝ)*base75 + (2005702285359168379/843250000000000000000000000000000 : ℝ)*base77 + (13278650617438918379/843250000000000000000000000000000 : ℝ)*base79 + (86051723342231/16865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (936997/250000000000000000000 : ℝ)*base90 + (936997/250000000000000000000 : ℝ)*base92 + (936997/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1462_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1462_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1462_box_0 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-446587561/2500000000 : ℝ)*x 0 + (1346209509/2500000000 : ℝ)*x 1 + (5384837527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446587561/2500000000 : ℝ)^2211 ≤ (1063026171463/10000000000000 : ℝ)^1699 := by
    have hnat : (446587561 : ℕ)^2211*10000000000000^1699 ≤ 1063026171463^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446587561 2500000000 1063026171463 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346209509/2500000000 : ℝ)^2211 ≤ (87275140399/195312500000 : ℝ)^1699 := by
    have hnat : (1346209509 : ℕ)^2211*195312500000^1699 ≤ 87275140399^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346209509 2500000000 87275140399 195312500000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384837527/10000000000 : ℝ)^2211 ≤ (44684866387601/100000000000000 : ℝ)^1699 := by
    have hnat : (5384837527 : ℕ)^2211*100000000000000^1699 ≤ 44684866387601^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384837527 10000000000 44684866387601 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446587561/2500000000 : ℝ), (1346209509/2500000000 : ℝ), (5384837527/10000000000 : ℝ)] ![(1063026171463/10000000000000 : ℝ), (87275140399/195312500000 : ℝ), (44684866387601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446587561/2500000000 : ℝ)|^2211 ≤ (1063026171463/10000000000000 : ℝ)^1699
        have hw : |(-446587561/2500000000 : ℝ)|=(446587561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346209509/2500000000 : ℝ)|^2211 ≤ (87275140399/195312500000 : ℝ)^1699
        have hw : |(1346209509/2500000000 : ℝ)|=(1346209509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384837527/10000000000 : ℝ)|^2211 ≤ (44684866387601/100000000000000 : ℝ)^1699
        have hw : |(5384837527/10000000000 : ℝ)|=(5384837527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_1 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (528626223/1000000000 : ℝ)*x 0 + (-480476943/2500000000 : ℝ)*x 1 + (1346209323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528626223/1000000000 : ℝ)^2211 ≤ (43623301403069/100000000000000 : ℝ)^1699 := by
    have hnat : (528626223 : ℕ)^2211*100000000000000^1699 ≤ 43623301403069^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528626223 1000000000 43623301403069 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480476943/2500000000 : ℝ)^2211 ≤ (2922958682929/25000000000000 : ℝ)^1699 := by
    have hnat : (480476943 : ℕ)^2211*25000000000000^1699 ≤ 2922958682929^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480476943 2500000000 2922958682929 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346209323/2500000000 : ℝ)^2211 ≤ (22342431924919/50000000000000 : ℝ)^1699 := by
    have hnat : (1346209323 : ℕ)^2211*50000000000000^1699 ≤ 22342431924919^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346209323 2500000000 22342431924919 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528626223/1000000000 : ℝ), (-480476943/2500000000 : ℝ), (1346209323/2500000000 : ℝ)] ![(43623301403069/100000000000000 : ℝ), (2922958682929/25000000000000 : ℝ), (22342431924919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528626223/1000000000 : ℝ)|^2211 ≤ (43623301403069/100000000000000 : ℝ)^1699
        have hw : |(528626223/1000000000 : ℝ)|=(528626223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-480476943/2500000000 : ℝ)|^2211 ≤ (2922958682929/25000000000000 : ℝ)^1699
        have hw : |(-480476943/2500000000 : ℝ)|=(480476943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346209323/2500000000 : ℝ)|^2211 ≤ (22342431924919/50000000000000 : ℝ)^1699
        have hw : |(1346209323/2500000000 : ℝ)|=(1346209323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_2 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42290097/80000000 : ℝ)*x 0 + (269241893/500000000 : ℝ)*x 1 + (-1921907141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42290097/80000000 : ℝ)^2211 ≤ (43623300275471/100000000000000 : ℝ)^1699 := by
    have hnat : (42290097 : ℕ)^2211*100000000000000^1699 ≤ 43623300275471^1699*80000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42290097 80000000 43623300275471 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269241893/500000000 : ℝ)^2211 ≤ (22342434991833/50000000000000 : ℝ)^1699 := by
    have hnat : (269241893 : ℕ)^2211*50000000000000^1699 ≤ 22342434991833^1699*500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269241893 500000000 22342434991833 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921907141/10000000000 : ℝ)^2211 ≤ (1461478717033/12500000000000 : ℝ)^1699 := by
    have hnat : (1921907141 : ℕ)^2211*12500000000000^1699 ≤ 1461478717033^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921907141 10000000000 1461478717033 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42290097/80000000 : ℝ), (269241893/500000000 : ℝ), (-1921907141/10000000000 : ℝ)] ![(43623300275471/100000000000000 : ℝ), (22342434991833/50000000000000 : ℝ), (1461478717033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42290097/80000000 : ℝ)|^2211 ≤ (43623300275471/100000000000000 : ℝ)^1699
        have hw : |(42290097/80000000 : ℝ)|=(42290097/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269241893/500000000 : ℝ)|^2211 ≤ (22342434991833/50000000000000 : ℝ)^1699
        have hw : |(269241893/500000000 : ℝ)|=(269241893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921907141/10000000000 : ℝ)|^2211 ≤ (1461478717033/12500000000000 : ℝ)^1699
        have hw : |(-1921907141/10000000000 : ℝ)|=(1921907141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_3 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (555231167/1250000000 : ℝ)*x 0 + (528376021/1250000000 : ℝ)*x 1 + (2113504233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (555231167/1250000000 : ℝ)^2211 ≤ (34782105218837/100000000000000 : ℝ)^1699 := by
    have hnat : (555231167 : ℕ)^2211*100000000000000^1699 ≤ 34782105218837^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555231167 1250000000 34782105218837 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528376021/1250000000 : ℝ)^2211 ≤ (3260894588937/10000000000000 : ℝ)^1699 := by
    have hnat : (528376021 : ℕ)^2211*10000000000000^1699 ≤ 3260894588937^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528376021 1250000000 3260894588937 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113504233/5000000000 : ℝ)^2211 ≤ (32608948881051/100000000000000 : ℝ)^1699 := by
    have hnat : (2113504233 : ℕ)^2211*100000000000000^1699 ≤ 32608948881051^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113504233 5000000000 32608948881051 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(555231167/1250000000 : ℝ), (528376021/1250000000 : ℝ), (2113504233/5000000000 : ℝ)] ![(34782105218837/100000000000000 : ℝ), (3260894588937/10000000000000 : ℝ), (32608948881051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(555231167/1250000000 : ℝ)|^2211 ≤ (34782105218837/100000000000000 : ℝ)^1699
        have hw : |(555231167/1250000000 : ℝ)|=(555231167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528376021/1250000000 : ℝ)|^2211 ≤ (3260894588937/10000000000000 : ℝ)^1699
        have hw : |(528376021/1250000000 : ℝ)|=(528376021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113504233/5000000000 : ℝ)|^2211 ≤ (32608948881051/100000000000000 : ℝ)^1699
        have hw : |(2113504233/5000000000 : ℝ)|=(2113504233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_4 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1052857563/5000000000 : ℝ)*x 0 + (5266970903/10000000000 : ℝ)*x 1 + (658371391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052857563/5000000000 : ℝ)^2211 ≤ (13167507140877/100000000000000 : ℝ)^1699 := by
    have hnat : (1052857563 : ℕ)^2211*100000000000000^1699 ≤ 13167507140877^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052857563 5000000000 13167507140877 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266970903/10000000000 : ℝ)^2211 ≤ (43416245212911/100000000000000 : ℝ)^1699 := by
    have hnat : (5266970903 : ℕ)^2211*100000000000000^1699 ≤ 43416245212911^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266970903 10000000000 43416245212911 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658371391/1250000000 : ℝ)^2211 ≤ (43416247626533/100000000000000 : ℝ)^1699 := by
    have hnat : (658371391 : ℕ)^2211*100000000000000^1699 ≤ 43416247626533^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658371391 1250000000 43416247626533 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1052857563/5000000000 : ℝ), (5266970903/10000000000 : ℝ), (658371391/1250000000 : ℝ)] ![(13167507140877/100000000000000 : ℝ), (43416245212911/100000000000000 : ℝ), (43416247626533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1052857563/5000000000 : ℝ)|^2211 ≤ (13167507140877/100000000000000 : ℝ)^1699
        have hw : |(-1052857563/5000000000 : ℝ)|=(1052857563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266970903/10000000000 : ℝ)|^2211 ≤ (43416245212911/100000000000000 : ℝ)^1699
        have hw : |(5266970903/10000000000 : ℝ)|=(5266970903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658371391/1250000000 : ℝ)|^2211 ≤ (43416247626533/100000000000000 : ℝ)^1699
        have hw : |(658371391/1250000000 : ℝ)|=(658371391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_5 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536864091/1000000000 : ℝ)*x 0 + (-492491219/2500000000 : ℝ)*x 1 + (2633485521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536864091/1000000000 : ℝ)^2211 ≤ (44510038573709/100000000000000 : ℝ)^1699 := by
    have hnat : (536864091 : ℕ)^2211*100000000000000^1699 ≤ 44510038573709^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536864091 1000000000 44510038573709 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492491219/2500000000 : ℝ)^2211 ≤ (3018428677723/25000000000000 : ℝ)^1699 := by
    have hnat : (492491219 : ℕ)^2211*25000000000000^1699 ≤ 3018428677723^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492491219 2500000000 3018428677723 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633485521/5000000000 : ℝ)^2211 ≤ (43416246703993/100000000000000 : ℝ)^1699 := by
    have hnat : (2633485521 : ℕ)^2211*100000000000000^1699 ≤ 43416246703993^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633485521 5000000000 43416246703993 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536864091/1000000000 : ℝ), (-492491219/2500000000 : ℝ), (2633485521/5000000000 : ℝ)] ![(44510038573709/100000000000000 : ℝ), (3018428677723/25000000000000 : ℝ), (43416246703993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536864091/1000000000 : ℝ)|^2211 ≤ (44510038573709/100000000000000 : ℝ)^1699
        have hw : |(536864091/1000000000 : ℝ)|=(536864091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492491219/2500000000 : ℝ)|^2211 ≤ (3018428677723/25000000000000 : ℝ)^1699
        have hw : |(-492491219/2500000000 : ℝ)|=(492491219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633485521/5000000000 : ℝ)|^2211 ≤ (43416246703993/100000000000000 : ℝ)^1699
        have hw : |(2633485521/5000000000 : ℝ)|=(2633485521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_6 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2684320571/5000000000 : ℝ)*x 0 + (2633485459/5000000000 : ℝ)*x 1 + (-246245591/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684320571/5000000000 : ℝ)^2211 ≤ (22255020538401/50000000000000 : ℝ)^1699 := by
    have hnat : (2684320571 : ℕ)^2211*50000000000000^1699 ≤ 22255020538401^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684320571 5000000000 22255020538401 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633485459/5000000000 : ℝ)^2211 ≤ (43416245373819/100000000000000 : ℝ)^1699 := by
    have hnat : (2633485459 : ℕ)^2211*100000000000000^1699 ≤ 43416245373819^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633485459 5000000000 43416245373819 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246245591/1250000000 : ℝ)^2211 ≤ (377303547827/3125000000000 : ℝ)^1699 := by
    have hnat : (246245591 : ℕ)^2211*3125000000000^1699 ≤ 377303547827^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246245591 1250000000 377303547827 3125000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684320571/5000000000 : ℝ), (2633485459/5000000000 : ℝ), (-246245591/1250000000 : ℝ)] ![(22255020538401/50000000000000 : ℝ), (43416245373819/100000000000000 : ℝ), (377303547827/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684320571/5000000000 : ℝ)|^2211 ≤ (22255020538401/50000000000000 : ℝ)^1699
        have hw : |(2684320571/5000000000 : ℝ)|=(2684320571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633485459/5000000000 : ℝ)|^2211 ≤ (43416245373819/100000000000000 : ℝ)^1699
        have hw : |(2633485459/5000000000 : ℝ)|=(2633485459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246245591/1250000000 : ℝ)|^2211 ≤ (377303547827/3125000000000 : ℝ)^1699
        have hw : |(-246245591/1250000000 : ℝ)|=(246245591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_7 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1037360111/2500000000 : ℝ)*x 0 + (68330669/156250000 : ℝ)*x 1 + (874632551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037360111/2500000000 : ℝ)^2211 ≤ (31832390544859/100000000000000 : ℝ)^1699 := by
    have hnat : (1037360111 : ℕ)^2211*100000000000000^1699 ≤ 31832390544859^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037360111 2500000000 31832390544859 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68330669/156250000 : ℝ)^2211 ≤ (34083805031789/100000000000000 : ℝ)^1699 := by
    have hnat : (68330669 : ℕ)^2211*100000000000000^1699 ≤ 34083805031789^1699*156250000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68330669 156250000 34083805031789 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874632551/2000000000 : ℝ)^2211 ≤ (34083804413093/100000000000000 : ℝ)^1699 := by
    have hnat : (874632551 : ℕ)^2211*100000000000000^1699 ≤ 34083804413093^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874632551 2000000000 34083804413093 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037360111/2500000000 : ℝ), (68330669/156250000 : ℝ), (874632551/2000000000 : ℝ)] ![(31832390544859/100000000000000 : ℝ), (34083805031789/100000000000000 : ℝ), (34083804413093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037360111/2500000000 : ℝ)|^2211 ≤ (31832390544859/100000000000000 : ℝ)^1699
        have hw : |(1037360111/2500000000 : ℝ)|=(1037360111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68330669/156250000 : ℝ)|^2211 ≤ (34083805031789/100000000000000 : ℝ)^1699
        have hw : |(68330669/156250000 : ℝ)|=(68330669/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874632551/2000000000 : ℝ)|^2211 ≤ (34083804413093/100000000000000 : ℝ)^1699
        have hw : |(874632551/2000000000 : ℝ)|=(874632551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_8 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019189253/5000000000 : ℝ)*x 0 + (1037059849/2000000000 : ℝ)*x 1 + (269939529/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019189253/5000000000 : ℝ)^2211 ≤ (3155551280247/25000000000000 : ℝ)^1699 := by
    have hnat : (1019189253 : ℕ)^2211*25000000000000^1699 ≤ 3155551280247^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019189253 5000000000 3155551280247 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037059849/2000000000 : ℝ)^2211 ≤ (42542190769251/100000000000000 : ℝ)^1699 := by
    have hnat : (1037059849 : ℕ)^2211*100000000000000^1699 ≤ 42542190769251^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037059849 2000000000 42542190769251 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269939529/500000000 : ℝ)^2211 ≤ (179342416363/400000000000 : ℝ)^1699 := by
    have hnat : (269939529 : ℕ)^2211*400000000000^1699 ≤ 179342416363^1699*500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269939529 500000000 179342416363 400000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019189253/5000000000 : ℝ), (1037059849/2000000000 : ℝ), (269939529/500000000 : ℝ)] ![(3155551280247/25000000000000 : ℝ), (42542190769251/100000000000000 : ℝ), (179342416363/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019189253/5000000000 : ℝ)|^2211 ≤ (3155551280247/25000000000000 : ℝ)^1699
        have hw : |(-1019189253/5000000000 : ℝ)|=(1019189253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037059849/2000000000 : ℝ)|^2211 ≤ (42542190769251/100000000000000 : ℝ)^1699
        have hw : |(1037059849/2000000000 : ℝ)|=(1037059849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269939529/500000000 : ℝ)|^2211 ≤ (179342416363/400000000000 : ℝ)^1699
        have hw : |(269939529/500000000 : ℝ)|=(269939529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_9 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276506217/10000000000 : ℝ)*x 0 + (-383218857/2000000000 : ℝ)*x 1 + (5398790907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276506217/10000000000 : ℝ)^2211 ≤ (21759280200631/50000000000000 : ℝ)^1699 := by
    have hnat : (5276506217 : ℕ)^2211*50000000000000^1699 ≤ 21759280200631^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276506217 10000000000 21759280200631 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383218857/2000000000 : ℝ)^2211 ≤ (11645831952639/100000000000000 : ℝ)^1699 := by
    have hnat : (383218857 : ℕ)^2211*100000000000000^1699 ≤ 11645831952639^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383218857 2000000000 11645831952639 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398790907/10000000000 : ℝ)^2211 ≤ (5604450953097/12500000000000 : ℝ)^1699 := by
    have hnat : (5398790907 : ℕ)^2211*12500000000000^1699 ≤ 5604450953097^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398790907 10000000000 5604450953097 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276506217/10000000000 : ℝ), (-383218857/2000000000 : ℝ), (5398790907/10000000000 : ℝ)] ![(21759280200631/50000000000000 : ℝ), (11645831952639/100000000000000 : ℝ), (5604450953097/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276506217/10000000000 : ℝ)|^2211 ≤ (21759280200631/50000000000000 : ℝ)^1699
        have hw : |(5276506217/10000000000 : ℝ)|=(5276506217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383218857/2000000000 : ℝ)|^2211 ≤ (11645831952639/100000000000000 : ℝ)^1699
        have hw : |(-383218857/2000000000 : ℝ)|=(383218857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398790907/10000000000 : ℝ)|^2211 ≤ (5604450953097/12500000000000 : ℝ)^1699
        have hw : |(5398790907/10000000000 : ℝ)|=(5398790907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_10 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276506237/10000000000 : ℝ)*x 0 + (5398790993/10000000000 : ℝ)*x 1 + (-958047071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276506237/10000000000 : ℝ)^2211 ≤ (43518560615923/100000000000000 : ℝ)^1699 := by
    have hnat : (5276506237 : ℕ)^2211*100000000000000^1699 ≤ 43518560615923^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276506237 10000000000 43518560615923 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398790993/10000000000 : ℝ)^2211 ≤ (22417804277107/50000000000000 : ℝ)^1699 := by
    have hnat : (5398790993 : ℕ)^2211*50000000000000^1699 ≤ 22417804277107^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398790993 10000000000 22417804277107 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958047071/5000000000 : ℝ)^2211 ≤ (11645830821581/100000000000000 : ℝ)^1699 := by
    have hnat : (958047071 : ℕ)^2211*100000000000000^1699 ≤ 11645830821581^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958047071 5000000000 11645830821581 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276506237/10000000000 : ℝ), (5398790993/10000000000 : ℝ), (-958047071/5000000000 : ℝ)] ![(43518560615923/100000000000000 : ℝ), (22417804277107/50000000000000 : ℝ), (11645830821581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276506237/10000000000 : ℝ)|^2211 ≤ (43518560615923/100000000000000 : ℝ)^1699
        have hw : |(5276506237/10000000000 : ℝ)|=(5276506237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398790993/10000000000 : ℝ)|^2211 ≤ (22417804277107/50000000000000 : ℝ)^1699
        have hw : |(5398790993/10000000000 : ℝ)|=(5398790993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-958047071/5000000000 : ℝ)|^2211 ≤ (11645830821581/100000000000000 : ℝ)^1699
        have hw : |(-958047071/5000000000 : ℝ)|=(958047071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_11 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (447590823/1000000000 : ℝ)*x 0 + (841938439/2000000000 : ℝ)*x 1 + (131552863/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447590823/1000000000 : ℝ)^2211 ≤ (35129576188157/100000000000000 : ℝ)^1699 := by
    have hnat : (447590823 : ℕ)^2211*100000000000000^1699 ≤ 35129576188157^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447590823 1000000000 35129576188157 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841938439/2000000000 : ℝ)^2211 ≤ (8108803701307/25000000000000 : ℝ)^1699 := by
    have hnat : (841938439 : ℕ)^2211*25000000000000^1699 ≤ 8108803701307^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841938439 2000000000 8108803701307 25000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131552863/312500000 : ℝ)^2211 ≤ (16217604499859/50000000000000 : ℝ)^1699 := by
    have hnat : (131552863 : ℕ)^2211*50000000000000^1699 ≤ 16217604499859^1699*312500000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131552863 312500000 16217604499859 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447590823/1000000000 : ℝ), (841938439/2000000000 : ℝ), (131552863/312500000 : ℝ)] ![(35129576188157/100000000000000 : ℝ), (8108803701307/25000000000000 : ℝ), (16217604499859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447590823/1000000000 : ℝ)|^2211 ≤ (35129576188157/100000000000000 : ℝ)^1699
        have hw : |(447590823/1000000000 : ℝ)|=(447590823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(841938439/2000000000 : ℝ)|^2211 ≤ (8108803701307/25000000000000 : ℝ)^1699
        have hw : |(841938439/2000000000 : ℝ)|=(841938439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131552863/312500000 : ℝ)|^2211 ≤ (16217604499859/50000000000000 : ℝ)^1699
        have hw : |(131552863/312500000 : ℝ)|=(131552863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_12 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-185381297/1000000000 : ℝ)*x 0 + (1366137013/2500000000 : ℝ)*x 1 + (5255830493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185381297/1000000000 : ℝ)^2211 ≤ (11155649087197/100000000000000 : ℝ)^1699 := by
    have hnat : (185381297 : ℕ)^2211*100000000000000^1699 ≤ 11155649087197^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185381297 1000000000 11155649087197 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366137013/2500000000 : ℝ)^2211 ≤ (22773786541741/50000000000000 : ℝ)^1699 := by
    have hnat : (1366137013 : ℕ)^2211*50000000000000^1699 ≤ 22773786541741^1699*2500000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366137013 2500000000 22773786541741 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255830493/10000000000 : ℝ)^2211 ≤ (4329677782203/10000000000000 : ℝ)^1699 := by
    have hnat : (5255830493 : ℕ)^2211*10000000000000^1699 ≤ 4329677782203^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255830493 10000000000 4329677782203 10000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185381297/1000000000 : ℝ), (1366137013/2500000000 : ℝ), (5255830493/10000000000 : ℝ)] ![(11155649087197/100000000000000 : ℝ), (22773786541741/50000000000000 : ℝ), (4329677782203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185381297/1000000000 : ℝ)|^2211 ≤ (11155649087197/100000000000000 : ℝ)^1699
        have hw : |(-185381297/1000000000 : ℝ)|=(185381297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366137013/2500000000 : ℝ)|^2211 ≤ (22773786541741/50000000000000 : ℝ)^1699
        have hw : |(1366137013/2500000000 : ℝ)|=(1366137013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255830493/10000000000 : ℝ)|^2211 ≤ (4329677782203/10000000000000 : ℝ)^1699
        have hw : |(5255830493/10000000000 : ℝ)|=(5255830493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_13 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (84006657/156250000 : ℝ)*x 0 + (-246801117/1250000000 : ℝ)*x 1 + (2627915149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84006657/156250000 : ℝ)^2211 ≤ (22297026139939/50000000000000 : ℝ)^1699 := by
    have hnat : (84006657 : ℕ)^2211*50000000000000^1699 ≤ 22297026139939^1699*156250000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84006657 156250000 22297026139939 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246801117/1250000000 : ℝ)^2211 ≤ (302729299379/2500000000000 : ℝ)^1699 := by
    have hnat : (246801117 : ℕ)^2211*2500000000000^1699 ≤ 302729299379^1699*1250000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246801117 1250000000 302729299379 2500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627915149/5000000000 : ℝ)^2211 ≤ (21648387865779/50000000000000 : ℝ)^1699 := by
    have hnat : (2627915149 : ℕ)^2211*50000000000000^1699 ≤ 21648387865779^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627915149 5000000000 21648387865779 50000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84006657/156250000 : ℝ), (-246801117/1250000000 : ℝ), (2627915149/5000000000 : ℝ)] ![(22297026139939/50000000000000 : ℝ), (302729299379/2500000000000 : ℝ), (21648387865779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84006657/156250000 : ℝ)|^2211 ≤ (22297026139939/50000000000000 : ℝ)^1699
        have hw : |(84006657/156250000 : ℝ)|=(84006657/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-246801117/1250000000 : ℝ)|^2211 ≤ (302729299379/2500000000000 : ℝ)^1699
        have hw : |(-246801117/1250000000 : ℝ)|=(246801117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627915149/5000000000 : ℝ)|^2211 ≤ (21648387865779/50000000000000 : ℝ)^1699
        have hw : |(2627915149/5000000000 : ℝ)|=(2627915149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_14 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1075285213/2000000000 : ℝ)*x 0 + (2627915217/5000000000 : ℝ)*x 1 + (-1974408731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075285213/2000000000 : ℝ)^2211 ≤ (356752419707/800000000000 : ℝ)^1699 := by
    have hnat : (1075285213 : ℕ)^2211*800000000000^1699 ≤ 356752419707^1699*2000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075285213 2000000000 356752419707 800000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627915217/5000000000 : ℝ)^2211 ≤ (5412097148691/12500000000000 : ℝ)^1699 := by
    have hnat : (2627915217 : ℕ)^2211*12500000000000^1699 ≤ 5412097148691^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627915217 5000000000 5412097148691 12500000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1974408731/10000000000 : ℝ)^2211 ≤ (12109170338997/100000000000000 : ℝ)^1699 := by
    have hnat : (1974408731 : ℕ)^2211*100000000000000^1699 ≤ 12109170338997^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1974408731 10000000000 12109170338997 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075285213/2000000000 : ℝ), (2627915217/5000000000 : ℝ), (-1974408731/10000000000 : ℝ)] ![(356752419707/800000000000 : ℝ), (5412097148691/12500000000000 : ℝ), (12109170338997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075285213/2000000000 : ℝ)|^2211 ≤ (356752419707/800000000000 : ℝ)^1699
        have hw : |(1075285213/2000000000 : ℝ)|=(1075285213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627915217/5000000000 : ℝ)|^2211 ≤ (5412097148691/12500000000000 : ℝ)^1699
        have hw : |(2627915217/5000000000 : ℝ)|=(2627915217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1974408731/10000000000 : ℝ)|^2211 ≤ (12109170338997/100000000000000 : ℝ)^1699
        have hw : |(-1974408731/10000000000 : ℝ)|=(1974408731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1462_box_15 (p : ℝ) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ)) (x : Fin 3 → ℝ) :
    (412135183/1000000000 : ℝ)*x 0 + (2193482957/5000000000 : ℝ)*x 1 + (4386965903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412135183/1000000000 : ℝ)^2211 ≤ (31552259334271/100000000000000 : ℝ)^1699 := by
    have hnat : (412135183 : ℕ)^2211*100000000000000^1699 ≤ 31552259334271^1699*1000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412135183 1000000000 31552259334271 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193482957/5000000000 : ℝ)^2211 ≤ (34223870379503/100000000000000 : ℝ)^1699 := by
    have hnat : (2193482957 : ℕ)^2211*100000000000000^1699 ≤ 34223870379503^1699*5000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193482957 5000000000 34223870379503 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386965903/10000000000 : ℝ)^2211 ≤ (34223870267829/100000000000000 : ℝ)^1699 := by
    have hnat : (4386965903 : ℕ)^2211*100000000000000^1699 ≤ 34223870267829^1699*10000000000^2211 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386965903 10000000000 34223870267829 100000000000000 2211 1699 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2211/512 : ℝ)) 2211 1699 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412135183/1000000000 : ℝ), (2193482957/5000000000 : ℝ), (4386965903/10000000000 : ℝ)] ![(31552259334271/100000000000000 : ℝ), (34223870379503/100000000000000 : ℝ), (34223870267829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412135183/1000000000 : ℝ)|^2211 ≤ (31552259334271/100000000000000 : ℝ)^1699
        have hw : |(412135183/1000000000 : ℝ)|=(412135183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2193482957/5000000000 : ℝ)|^2211 ≤ (34223870379503/100000000000000 : ℝ)^1699
        have hw : |(2193482957/5000000000 : ℝ)|=(2193482957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386965903/10000000000 : ℝ)|^2211 ≤ (34223870267829/100000000000000 : ℝ)^1699
        have hw : |(4386965903/10000000000 : ℝ)|=(4386965903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1462_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62921/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2959/5000 : ℝ) ∧ (20157/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10601/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5703/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5703/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5703/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5703/50000 : ℝ) ^ (4421/1024 : ℝ) ≤ (8497355837853073/100000000000000000000 : ℝ) := by
    have hpowers : (5703/50000 : ℝ)^4421 ≤ (8497355837853073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5703 : ℕ)^4421*100000000000000000000^1024 ≤ 8497355837853073^1024*50000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5703 50000 8497355837853073 100000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5703/50000 : ℝ)) (X := (8497355837853073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (4421/1024 : ℝ) ≤ (2595843051008007/10000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^4421 ≤ (2595843051008007/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14773 : ℕ)^4421*10000000000000000000^1024 ≤ 2595843051008007^1024*100000^4421 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 2595843051008007 10000000000000000000 4421 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (2595843051008007/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008497355837853073/50000000000000000000 : ℝ) ≤ (2500098402220217/2500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (50008497355837853073/50000000000000000000 : ℝ)^1024 ≤ (2500098402220217/2500000000000000 : ℝ)^4421 := by
      have hnat : (50008497355837853073 : ℕ)^1024*2500000000000000^4421 ≤ 2500098402220217^4421*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008497355837853073 50000000000000000000 2500098402220217 2500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500098402220217/2500000000000000 : ℝ)) (X := (50008497355837853073/50000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034455786347933143/100000000000000000000 : ℝ) ≤ (500039898275961/500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (100034455786347933143/100000000000000000000 : ℝ)^1024 ≤ (500039898275961/500000000000000 : ℝ)^4421 := by
      have hnat : (100034455786347933143 : ℕ)^1024*500000000000000^4421 ≤ 500039898275961^4421*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034455786347933143 100000000000000000000 500039898275961 500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500039898275961/500000000000000 : ℝ)) (X := (100034455786347933143/100000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002595843051008007/5000000000000000000 : ℝ) ≤ (2500300580539393/2500000000000000 : ℝ) ^ (4421/1024 : ℝ) := by
    have hpowers : (5002595843051008007/5000000000000000000 : ℝ)^1024 ≤ (2500300580539393/2500000000000000 : ℝ)^4421 := by
      have hnat : (5002595843051008007 : ℕ)^1024*2500000000000000^4421 ≤ 2500300580539393^4421*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002595843051008007 5000000000000000000 2500300580539393 2500000000000000 1024 4421 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500300580539393/2500000000000000 : ℝ)) (X := (5002595843051008007/5000000000000000000 : ℝ)) (by norm_num) 4421 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8497355837853073/100000000000000000000 : ℝ) ≤ ((8415525274366949183/8417500000000000000 : ℝ)+2*(25272289897/21043750000000 : ℝ)*(5703/50000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (8415525274366949183/8417500000000000000 : ℝ)+2*(25272289897/21043750000000 : ℝ)*(5703/50000 : ℝ)=(2500098402220217/2500000000000000 : ℝ) by norm_num, show 1+2*(8497355837853073/100000000000000000000 : ℝ)=(50008497355837853073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2595843051008007/10000000000000000000 : ℝ)+(8497355837853073/100000000000000000000 : ℝ) ≤ ((8415525274366949183/8417500000000000000 : ℝ)+(25272289897/21043750000000 : ℝ)*((14773/100000 : ℝ)+(5703/50000 : ℝ)))^(4421/1024 : ℝ) := by
    rw [show (8415525274366949183/8417500000000000000 : ℝ)+(25272289897/21043750000000 : ℝ)*((14773/100000 : ℝ)+(5703/50000 : ℝ))=(500039898275961/500000000000000 : ℝ) by norm_num, show 1+(2595843051008007/10000000000000000000 : ℝ)+(8497355837853073/100000000000000000000 : ℝ)=(100034455786347933143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2595843051008007/10000000000000000000 : ℝ) ≤ ((8415525274366949183/8417500000000000000 : ℝ)+2*(25272289897/21043750000000 : ℝ)*(14773/100000 : ℝ))^(4421/1024 : ℝ) := by
    rw [show (8415525274366949183/8417500000000000000 : ℝ)+2*(25272289897/21043750000000 : ℝ)*(14773/100000 : ℝ)=(2500300580539393/2500000000000000 : ℝ) by norm_num, show 1+2*(2595843051008007/10000000000000000000 : ℝ)=(5002595843051008007/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8415525274366949183/8417500000000000000 : ℝ)*(X 1 0+X 2 0)+(25272289897/21043750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (8415525274366949183/8417500000000000000 : ℝ)) (alpha := (25272289897/21043750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8415525274366949183/8417500000000000000 : ℝ)*(X 0 1+X 2 1)+(25272289897/21043750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (8415525274366949183/8417500000000000000 : ℝ)) (alpha := (25272289897/21043750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8415525274366949183/8417500000000000000 : ℝ)*(X 0 2+X 1 2)+(25272289897/21043750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4421/1024 : ℝ)) (lo := (5703/50000 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (8415525274366949183/8417500000000000000 : ℝ)) (alpha := (25272289897/21043750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-446587561/2500000000 : ℝ)*X 0 0+(1346209509/2500000000 : ℝ)*X 0 1+(5384837527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528626223/1000000000 : ℝ)*X 1 0+(-480476943/2500000000 : ℝ)*X 1 1+(1346209323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42290097/80000000 : ℝ)*X 2 0+(269241893/500000000 : ℝ)*X 2 1+(-1921907141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((555231167/1250000000 : ℝ)*X 0 0+(528376021/1250000000 : ℝ)*X 0 1+(2113504233/5000000000 : ℝ)*X 0 2+(555231167/1250000000 : ℝ)*X 1 0+(528376021/1250000000 : ℝ)*X 1 1+(2113504233/5000000000 : ℝ)*X 1 2+(555231167/1250000000 : ℝ)*X 2 0+(528376021/1250000000 : ℝ)*X 2 1+(2113504233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1052857563/5000000000 : ℝ)*X 0 0+(5266970903/10000000000 : ℝ)*X 0 1+(658371391/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((536864091/1000000000 : ℝ)*X 1 0+(-492491219/2500000000 : ℝ)*X 1 1+(2633485521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684320571/5000000000 : ℝ)*X 2 0+(2633485459/5000000000 : ℝ)*X 2 1+(-246245591/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037360111/2500000000 : ℝ)*X 0 0+(68330669/156250000 : ℝ)*X 0 1+(874632551/2000000000 : ℝ)*X 0 2+(1037360111/2500000000 : ℝ)*X 1 0+(68330669/156250000 : ℝ)*X 1 1+(874632551/2000000000 : ℝ)*X 1 2+(1037360111/2500000000 : ℝ)*X 2 0+(68330669/156250000 : ℝ)*X 2 1+(874632551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1019189253/5000000000 : ℝ)*X 0 0+(1037059849/2000000000 : ℝ)*X 0 1+(269939529/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276506217/10000000000 : ℝ)*X 1 0+(-383218857/2000000000 : ℝ)*X 1 1+(5398790907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276506237/10000000000 : ℝ)*X 2 0+(5398790993/10000000000 : ℝ)*X 2 1+(-958047071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((447590823/1000000000 : ℝ)*X 0 0+(841938439/2000000000 : ℝ)*X 0 1+(131552863/312500000 : ℝ)*X 0 2+(447590823/1000000000 : ℝ)*X 1 0+(841938439/2000000000 : ℝ)*X 1 1+(131552863/312500000 : ℝ)*X 1 2+(447590823/1000000000 : ℝ)*X 2 0+(841938439/2000000000 : ℝ)*X 2 1+(131552863/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-185381297/1000000000 : ℝ)*X 0 0+(1366137013/2500000000 : ℝ)*X 0 1+(5255830493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((84006657/156250000 : ℝ)*X 1 0+(-246801117/1250000000 : ℝ)*X 1 1+(2627915149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1075285213/2000000000 : ℝ)*X 2 0+(2627915217/5000000000 : ℝ)*X 2 1+(-1974408731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((412135183/1000000000 : ℝ)*X 0 0+(2193482957/5000000000 : ℝ)*X 0 1+(4386965903/10000000000 : ℝ)*X 0 2+(412135183/1000000000 : ℝ)*X 1 0+(2193482957/5000000000 : ℝ)*X 1 1+(4386965903/10000000000 : ℝ)*X 1 2+(412135183/1000000000 : ℝ)*X 2 0+(2193482957/5000000000 : ℝ)*X 2 1+(4386965903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1462_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62921/100000 : ℝ) ≤ (-4728723623272079613293034561627/7515625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1933353/50000000000000 : ℝ)*(upper1) + (7896509/10000000000000 : ℝ)*(lower2) + (16176989/50000000000000 : ℝ)*(lower3) + (16556363/50000000000000 : ℝ)*(upper5) + (763133586113339/25000000000000 : ℝ)*(major0) + (763133586113339/25000000000000 : ℝ)*(major1) + (763133586113339/25000000000000 : ℝ)*(major2) + (284536427/12500000000000 : ℝ)*(sp2) + (642830513/50000000000000 : ℝ)*(sp3) + (2105968875707537/50000000000000 : ℝ)*(sp4) + (2105968876596603/50000000000000 : ℝ)*(sp5) + (421193547690179/10000000000000 : ℝ)*(sp6) + (957051253019633/50000000000000 : ℝ)*(sp7) + (444533/25000000000000 : ℝ)*(sp12) + (478525947925073/25000000000000 : ℝ)*(f.failure) + (2105968876596603/50000000000000 : ℝ)*(f.sum) + (2228880271041/601250000000000000000000000 : ℝ)*base66 + (167912255831924709/30062500000000000000000000000000 : ℝ)*base68 + (104052362500924709/30062500000000000000000000000000 : ℝ)*base70 + (39400963081200291/30062500000000000000000000000000 : ℝ)*base71 + (940304835947/300625000000000000000000000 : ℝ)*base73 + (186573266752424709/30062500000000000000000000000000 : ℝ)*base76 + (245748033876299709/30062500000000000000000000000000 : ℝ)*base78 + (58231097295299709/30062500000000000000000000000000 : ℝ)*base80 + (8856562894117/1202500000000000000000000000 : ℝ)*base82 + (2226787/500000000000000000000 : ℝ)*base90 + (2226787/500000000000000000000 : ℝ)*base92 + (2226787/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2959/5000 : ℝ) ≤ (841498706368630640855772272313/1421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21034367/12500000000000 : ℝ)*(lower1) + (8243537/100000000000000 : ℝ)*(lower2) + (108162497/50000000000000 : ℝ)*(upper4) + (97664370957687/3125000000000 : ℝ)*(major0) + (97664370957687/3125000000000 : ℝ)*(major1) + (97664370957687/3125000000000 : ℝ)*(major2) + (2135538344337947/50000000000000 : ℝ)*(sp0) + (2135442080773167/50000000000000 : ℝ)*(sp1) + (533884604753561/12500000000000 : ℝ)*(sp2) + (979850894188443/50000000000000 : ℝ)*(sp3) + (1104893321/12500000000000 : ℝ)*(sp6) + (4833539437/100000000000000 : ℝ)*(sp7) + (8988499161/100000000000000 : ℝ)*(sp8) + (201515628721/100000000000000 : ℝ)*(sp9) + (1959706621916323/100000000000000 : ℝ)*(f.failure) + (266942854823441/6250000000000 : ℝ)*(f.sum) + (2148742281277/227500000000000000000000000 : ℝ)*base65 + (4842729168683309/1421875000000000000000000000000 : ℝ)*base68 + (782204319620809/1421875000000000000000000000000 : ℝ)*base70 + (4623965071995809/1421875000000000000000000000000 : ℝ)*base72 + (1122168760621/455000000000000000000000000 : ℝ)*base74 + (157449848716273/177734375000000000000000000000 : ℝ)*base76 + (946196508568217/710937500000000000000000000000 : ℝ)*base78 + (6567927086099467/710937500000000000000000000000 : ℝ)*base80 + (969835976019/455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (8939463/2000000000000000000000 : ℝ)*base89 + (8939463/2000000000000000000000 : ℝ)*base91 + (8939463/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20157/25000 : ℝ) ≤ (84838810633882866041649009/105218750000000000000000000 : ℝ) := by norm_num
    linear_combination (15546727/100000000000000 : ℝ)*(upper1) + (7152379/50000000000000 : ℝ)*(upper3) + (117048431/100000000000000 : ℝ)*(upper4) + (91894303/100000000000000 : ℝ)*(lower5) + (686248229246679/20000000000000 : ℝ)*(major0) + (686248229246679/20000000000000 : ℝ)*(major1) + (686248229246679/20000000000000 : ℝ)*(major2) + (110659361261/100000000000000 : ℝ)*(sp1) + (27629440881/12500000000000 : ℝ)*(sp2) + (55967089551/100000000000000 : ℝ)*(sp3) + (234201596680701/5000000000000 : ℝ)*(sp8) + (4683921274252759/100000000000000 : ℝ)*(sp9) + (4683810898086973/100000000000000 : ℝ)*(sp10) + (2151517429677437/100000000000000 : ℝ)*(sp11) + (537893349191747/25000000000000 : ℝ)*(f.failure) + (234201596680701/5000000000000 : ℝ)*(f.sum) + (7699510590983/1683500000000000000000000000 : ℝ)*base65 + (637560329556663257/168350000000000000000000000000000 : ℝ)*base67 + (840781191150413257/168350000000000000000000000000000 : ℝ)*base69 + (1762845787435063257/168350000000000000000000000000000 : ℝ)*base71 + (1747977875523/420875000000000000000000000 : ℝ)*base74 + (692866437658336743/168350000000000000000000000000000 : ℝ)*base76 + (394733345892736743/168350000000000000000000000000000 : ℝ)*base78 + (348980193834486743/168350000000000000000000000000000 : ℝ)*base80 + (37222263843/8417500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (728793/500000000000000000000 : ℝ)*base90 + (728793/500000000000000000000 : ℝ)*base92 + (728793/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-10601/12500 : ℝ) ≤ (-44615460020340666858850160362467/52609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7344379/50000000000000 : ℝ)*(lower1) + (75664439/100000000000000 : ℝ)*(lower2) + (8052749/50000000000000 : ℝ)*(lower3) + (26488781/100000000000000 : ℝ)*(upper5) + (867276746176683/25000000000000 : ℝ)*(major0) + (867276746176683/25000000000000 : ℝ)*(major1) + (867276746176683/25000000000000 : ℝ)*(major2) + (2069541449/50000000000000 : ℝ)*(sp4) + (2710270607/3125000000000 : ℝ)*(sp5) + (26162864189/50000000000000 : ℝ)*(sp7) + (4791160892804329/100000000000000 : ℝ)*(sp12) + (4791078303227803/100000000000000 : ℝ)*(sp13) + (4791165031887227/100000000000000 : ℝ)*(sp14) + (2175264995535127/100000000000000 : ℝ)*(sp15) + (435063464252701/20000000000000 : ℝ)*(f.failure) + (4791165031887227/100000000000000 : ℝ)*(f.sum) + (6151391685431/4208750000000000000000000000 : ℝ)*base65 + (1599302433812600011/210437500000000000000000000000000 : ℝ)*base68 + (937243496810649989/210437500000000000000000000000000 : ℝ)*base69 + (299640722377024989/210437500000000000000000000000000 : ℝ)*base71 + (49375812610413/8417500000000000000000000000 : ℝ)*base74 + (1129456696642712489/210437500000000000000000000000000 : ℝ)*base75 + (780927410492212489/210437500000000000000000000000000 : ℝ)*base77 + (562861101649989/210437500000000000000000000000000 : ℝ)*base79 + (47284506217387/8417500000000000000000000000 : ℝ)*base81 + (133881/400000000000000000000 : ℝ)*base89 + (133881/400000000000000000000 : ℝ)*base91 + (133881/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1462_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62921/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2959/5000 : ℝ) else (20157/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10601/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1462_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1462_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62921/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2959/5000 : ℝ) else (20157/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10601/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1462_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1462_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4421/1024 : ℝ) ≤ p) (hpb : p ≤ (2211/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31895181/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62921/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2959/5000 : ℝ) else (20157/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10601/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1462_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

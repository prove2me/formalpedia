-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1650_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:39.171454+00:00
-- url     : https://prove2.me/submissions/b91c2c4c-2a7b-4639-bbc2-d081992d763f

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
theorem support_rectangle_w1650_s3_0 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-804257553/5000000000 : ℝ)*x 0 + (2723802821/5000000000 : ℝ)*x 1 + (323990337/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804257553/5000000000 : ℝ)^4919 ≤ (621832497143/6250000000000 : ℝ)^3895 := by
    have hnat : (804257553 : ℕ)^4919*6250000000000^3895 ≤ 621832497143^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804257553 5000000000 621832497143 6250000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723802821/5000000000 : ℝ)^4919 ≤ (9287179085603/20000000000000 : ℝ)^3895 := by
    have hnat : (2723802821 : ℕ)^4919*20000000000000^3895 ≤ 9287179085603^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723802821 5000000000 9287179085603 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323990337/625000000 : ℝ)^4919 ≤ (21807392298829/50000000000000 : ℝ)^3895 := by
    have hnat : (323990337 : ℕ)^4919*50000000000000^3895 ≤ 21807392298829^3895*625000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323990337 625000000 21807392298829 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-804257553/5000000000 : ℝ), (2723802821/5000000000 : ℝ), (323990337/625000000 : ℝ)] ![(621832497143/6250000000000 : ℝ), (9287179085603/20000000000000 : ℝ), (21807392298829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-804257553/5000000000 : ℝ)|^4919 ≤ (621832497143/6250000000000 : ℝ)^3895
        have hw : |(-804257553/5000000000 : ℝ)|=(804257553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723802821/5000000000 : ℝ)|^4919 ≤ (9287179085603/20000000000000 : ℝ)^3895
        have hw : |(2723802821/5000000000 : ℝ)|=(2723802821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323990337/625000000 : ℝ)|^4919 ≤ (21807392298829/50000000000000 : ℝ)^3895
        have hw : |(323990337/625000000 : ℝ)|=(323990337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_1 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069552643/2000000000 : ℝ)*x 0 + (-1744298097/10000000000 : ℝ)*x 1 + (5183845433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069552643/2000000000 : ℝ)^4919 ≤ (45363684251373/100000000000000 : ℝ)^3895 := by
    have hnat : (1069552643 : ℕ)^4919*100000000000000^3895 ≤ 45363684251373^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069552643 2000000000 45363684251373 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744298097/10000000000 : ℝ)^4919 ≤ (11021530699397/100000000000000 : ℝ)^3895 := by
    have hnat : (1744298097 : ℕ)^4919*100000000000000^3895 ≤ 11021530699397^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744298097 10000000000 11021530699397 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183845433/10000000000 : ℝ)^4919 ≤ (8722957006661/20000000000000 : ℝ)^3895 := by
    have hnat : (5183845433 : ℕ)^4919*20000000000000^3895 ≤ 8722957006661^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183845433 10000000000 8722957006661 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069552643/2000000000 : ℝ), (-1744298097/10000000000 : ℝ), (5183845433/10000000000 : ℝ)] ![(45363684251373/100000000000000 : ℝ), (11021530699397/100000000000000 : ℝ), (8722957006661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069552643/2000000000 : ℝ)|^4919 ≤ (45363684251373/100000000000000 : ℝ)^3895
        have hw : |(1069552643/2000000000 : ℝ)|=(1069552643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1744298097/10000000000 : ℝ)|^4919 ≤ (11021530699397/100000000000000 : ℝ)^3895
        have hw : |(-1744298097/10000000000 : ℝ)|=(1744298097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183845433/10000000000 : ℝ)|^4919 ≤ (8722957006661/20000000000000 : ℝ)^3895
        have hw : |(5183845433/10000000000 : ℝ)|=(5183845433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_2 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673881601/5000000000 : ℝ)*x 0 + (2591922713/5000000000 : ℝ)*x 1 + (-1744298123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673881601/5000000000 : ℝ)^4919 ≤ (22681842056053/50000000000000 : ℝ)^3895 := by
    have hnat : (2673881601 : ℕ)^4919*50000000000000^3895 ≤ 22681842056053^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673881601 5000000000 22681842056053 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591922713/5000000000 : ℝ)^4919 ≤ (21807392479463/50000000000000 : ℝ)^3895 := by
    have hnat : (2591922713 : ℕ)^4919*50000000000000^3895 ≤ 21807392479463^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591922713 5000000000 21807392479463 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744298123/10000000000 : ℝ)^4919 ≤ (1377691363359/12500000000000 : ℝ)^3895 := by
    have hnat : (1744298123 : ℕ)^4919*12500000000000^3895 ≤ 1377691363359^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744298123 10000000000 1377691363359 12500000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673881601/5000000000 : ℝ), (2591922713/5000000000 : ℝ), (-1744298123/10000000000 : ℝ)] ![(22681842056053/50000000000000 : ℝ), (21807392479463/50000000000000 : ℝ), (1377691363359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673881601/5000000000 : ℝ)|^4919 ≤ (22681842056053/50000000000000 : ℝ)^3895
        have hw : |(2673881601/5000000000 : ℝ)|=(2673881601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591922713/5000000000 : ℝ)|^4919 ≤ (21807392479463/50000000000000 : ℝ)^3895
        have hw : |(2591922713/5000000000 : ℝ)|=(2591922713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1744298123/10000000000 : ℝ)|^4919 ≤ (1377691363359/12500000000000 : ℝ)^3895
        have hw : |(-1744298123/10000000000 : ℝ)|=(1744298123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_3 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130647407/312500000 : ℝ)*x 0 + (192480391/500000000 : ℝ)*x 1 + (4532021723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130647407/312500000 : ℝ)^4919 ≤ (33241235987423/100000000000000 : ℝ)^3895 := by
    have hnat : (130647407 : ℕ)^4919*100000000000000^3895 ≤ 33241235987423^3895*312500000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130647407 312500000 33241235987423 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192480391/500000000 : ℝ)^4919 ≤ (3743967038223/12500000000000 : ℝ)^3895 := by
    have hnat : (192480391 : ℕ)^4919*12500000000000^3895 ≤ 3743967038223^3895*500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192480391 500000000 3743967038223 12500000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532021723/10000000000 : ℝ)^4919 ≤ (9201756926027/25000000000000 : ℝ)^3895 := by
    have hnat : (4532021723 : ℕ)^4919*25000000000000^3895 ≤ 9201756926027^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532021723 10000000000 9201756926027 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130647407/312500000 : ℝ), (192480391/500000000 : ℝ), (4532021723/10000000000 : ℝ)] ![(33241235987423/100000000000000 : ℝ), (3743967038223/12500000000000 : ℝ), (9201756926027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130647407/312500000 : ℝ)|^4919 ≤ (33241235987423/100000000000000 : ℝ)^3895
        have hw : |(130647407/312500000 : ℝ)|=(130647407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192480391/500000000 : ℝ)|^4919 ≤ (3743967038223/12500000000000 : ℝ)^3895
        have hw : |(192480391/500000000 : ℝ)|=(192480391/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532021723/10000000000 : ℝ)|^4919 ≤ (9201756926027/25000000000000 : ℝ)^3895
        have hw : |(4532021723/10000000000 : ℝ)|=(4532021723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_4 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-804289571/5000000000 : ℝ)*x 0 + (5185843027/10000000000 : ℝ)*x 1 + (5445587237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804289571/5000000000 : ℝ)^4919 ≤ (9949820177779/100000000000000 : ℝ)^3895 := by
    have hnat : (804289571 : ℕ)^4919*100000000000000^3895 ≤ 9949820177779^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804289571 5000000000 9949820177779 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185843027/10000000000 : ℝ)^4919 ≤ (10909002906351/25000000000000 : ℝ)^3895 := by
    have hnat : (5185843027 : ℕ)^4919*25000000000000^3895 ≤ 10909002906351^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185843027 10000000000 10909002906351 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445587237/10000000000 : ℝ)^4919 ≤ (46414168181939/100000000000000 : ℝ)^3895 := by
    have hnat : (5445587237 : ℕ)^4919*100000000000000^3895 ≤ 46414168181939^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445587237 10000000000 46414168181939 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-804289571/5000000000 : ℝ), (5185843027/10000000000 : ℝ), (5445587237/10000000000 : ℝ)] ![(9949820177779/100000000000000 : ℝ), (10909002906351/25000000000000 : ℝ), (46414168181939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-804289571/5000000000 : ℝ)|^4919 ≤ (9949820177779/100000000000000 : ℝ)^3895
        have hw : |(-804289571/5000000000 : ℝ)|=(804289571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185843027/10000000000 : ℝ)|^4919 ≤ (10909002906351/25000000000000 : ℝ)^3895
        have hw : |(5185843027/10000000000 : ℝ)|=(5185843027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445587237/10000000000 : ℝ)|^4919 ≤ (46414168181939/100000000000000 : ℝ)^3895
        have hw : |(5445587237/10000000000 : ℝ)|=(5445587237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_5 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638649101/5000000000 : ℝ)*x 0 + (-296511231/2000000000 : ℝ)*x 1 + (5445587547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638649101/5000000000 : ℝ)^4919 ≤ (4461011405339/10000000000000 : ℝ)^3895 := by
    have hnat : (2638649101 : ℕ)^4919*10000000000000^3895 ≤ 4461011405339^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638649101 5000000000 4461011405339 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296511231/2000000000 : ℝ)^4919 ≤ (8975714422919/100000000000000 : ℝ)^3895 := by
    have hnat : (296511231 : ℕ)^4919*100000000000000^3895 ≤ 8975714422919^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296511231 2000000000 8975714422919 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445587547/10000000000 : ℝ)^4919 ≤ (46414171518791/100000000000000 : ℝ)^3895 := by
    have hnat : (5445587547 : ℕ)^4919*100000000000000^3895 ≤ 46414171518791^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445587547 10000000000 46414171518791 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638649101/5000000000 : ℝ), (-296511231/2000000000 : ℝ), (5445587547/10000000000 : ℝ)] ![(4461011405339/10000000000000 : ℝ), (8975714422919/100000000000000 : ℝ), (46414171518791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638649101/5000000000 : ℝ)|^4919 ≤ (4461011405339/10000000000000 : ℝ)^3895
        have hw : |(2638649101/5000000000 : ℝ)|=(2638649101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296511231/2000000000 : ℝ)|^4919 ≤ (8975714422919/100000000000000 : ℝ)^3895
        have hw : |(-296511231/2000000000 : ℝ)|=(296511231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445587547/10000000000 : ℝ)|^4919 ≤ (46414171518791/100000000000000 : ℝ)^3895
        have hw : |(5445587547/10000000000 : ℝ)|=(5445587547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_6 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277298193/10000000000 : ℝ)*x 0 + (5445587457/10000000000 : ℝ)*x 1 + (-1482556293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277298193/10000000000 : ℝ)^4919 ≤ (4461011395731/10000000000000 : ℝ)^3895 := by
    have hnat : (5277298193 : ℕ)^4919*10000000000000^3895 ≤ 4461011395731^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277298193 10000000000 4461011395731 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445587457/10000000000 : ℝ)^4919 ≤ (11603542637507/25000000000000 : ℝ)^3895 := by
    have hnat : (5445587457 : ℕ)^4919*25000000000000^3895 ≤ 11603542637507^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445587457 10000000000 11603542637507 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482556293/10000000000 : ℝ)^4919 ≤ (179514309561/2000000000000 : ℝ)^3895 := by
    have hnat : (1482556293 : ℕ)^4919*2000000000000^3895 ≤ 179514309561^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482556293 10000000000 179514309561 2000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277298193/10000000000 : ℝ), (5445587457/10000000000 : ℝ), (-1482556293/10000000000 : ℝ)] ![(4461011395731/10000000000000 : ℝ), (11603542637507/25000000000000 : ℝ), (179514309561/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277298193/10000000000 : ℝ)|^4919 ≤ (4461011395731/10000000000000 : ℝ)^3895
        have hw : |(5277298193/10000000000 : ℝ)|=(5277298193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445587457/10000000000 : ℝ)|^4919 ≤ (11603542637507/25000000000000 : ℝ)^3895
        have hw : |(5445587457/10000000000 : ℝ)|=(5445587457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1482556293/10000000000 : ℝ)|^4919 ≤ (179514309561/2000000000000 : ℝ)^3895
        have hw : |(-1482556293/10000000000 : ℝ)|=(1482556293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s3_7 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180883807/10000000000 : ℝ)*x 0 + (4526854707/10000000000 : ℝ)*x 1 + (240926823/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180883807/10000000000 : ℝ)^4919 ≤ (16621455368371/50000000000000 : ℝ)^3895 := by
    have hnat : (4180883807 : ℕ)^4919*50000000000000^3895 ≤ 16621455368371^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180883807 10000000000 16621455368371 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526854707/10000000000 : ℝ)^4919 ≤ (735080781163/2000000000000 : ℝ)^3895 := by
    have hnat : (4526854707 : ℕ)^4919*2000000000000^3895 ≤ 735080781163^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526854707 10000000000 735080781163 2000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240926823/625000000 : ℝ)^4919 ≤ (30003050192831/100000000000000 : ℝ)^3895 := by
    have hnat : (240926823 : ℕ)^4919*100000000000000^3895 ≤ 30003050192831^3895*625000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240926823 625000000 30003050192831 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180883807/10000000000 : ℝ), (4526854707/10000000000 : ℝ), (240926823/625000000 : ℝ)] ![(16621455368371/50000000000000 : ℝ), (735080781163/2000000000000 : ℝ), (30003050192831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180883807/10000000000 : ℝ)|^4919 ≤ (16621455368371/50000000000000 : ℝ)^3895
        have hw : |(4180883807/10000000000 : ℝ)|=(4180883807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526854707/10000000000 : ℝ)|^4919 ≤ (735080781163/2000000000000 : ℝ)^3895
        have hw : |(4526854707/10000000000 : ℝ)|=(4526854707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240926823/625000000 : ℝ)|^4919 ≤ (30003050192831/100000000000000 : ℝ)^3895
        have hw : |(240926823/625000000 : ℝ)|=(240926823/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1650_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5333/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16273/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10601/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10601/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10601/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10601/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10601/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10601/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10601/100000 : ℝ) ^ (4915/1024 : ℝ) ≤ (524560006772543/25000000000000000000 : ℝ) := by
    have hpowers : (10601/100000 : ℝ)^4915 ≤ (524560006772543/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10601 : ℕ)^4915*25000000000000000000^1024 ≤ 524560006772543^1024*100000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10601 100000 524560006772543 25000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10601/100000 : ℝ)) (X := (524560006772543/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8173/50000 : ℝ) ^ (4915/1024 : ℝ) ≤ (16769835579301559/100000000000000000000 : ℝ) := by
    have hpowers : (8173/50000 : ℝ)^4915 ≤ (16769835579301559/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8173 : ℕ)^4915*100000000000000000000^1024 ≤ 16769835579301559^1024*50000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8173 50000 16769835579301559 100000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8173/50000 : ℝ)) (X := (16769835579301559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500524560006772543/12500000000000000000 : ℝ) ≤ (2500021857193271/2500000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (12500524560006772543/12500000000000000000 : ℝ)^1024 ≤ (2500021857193271/2500000000000000 : ℝ)^4915 := by
      have hnat : (12500524560006772543 : ℕ)^1024*2500000000000000^4915 ≤ 2500021857193271^4915*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500524560006772543 12500000000000000000 2500021857193271 2500000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500021857193271/2500000000000000 : ℝ)) (X := (12500524560006772543/12500000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018868075606391731/100000000000000000000 : ℝ) ≤ (500019653577411/500000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (100018868075606391731/100000000000000000000 : ℝ)^1024 ≤ (500019653577411/500000000000000 : ℝ)^4915 := by
      have hnat : (100018868075606391731 : ℕ)^1024*500000000000000^4915 ≤ 500019653577411^4915*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018868075606391731 100000000000000000000 500019653577411 500000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500019653577411/500000000000000 : ℝ)) (X := (100018868075606391731/100000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016769835579301559/50000000000000000000 : ℝ) ≤ (2500174678580839/2500000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50016769835579301559/50000000000000000000 : ℝ)^1024 ≤ (2500174678580839/2500000000000000 : ℝ)^4915 := by
      have hnat : (50016769835579301559 : ℕ)^1024*2500000000000000^4915 ≤ 2500174678580839^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016769835579301559 50000000000000000000 2500174678580839 2500000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500174678580839/2500000000000000 : ℝ)) (X := (50016769835579301559/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(524560006772543/25000000000000000000 : ℝ) ≤ ((14361005510045733527/14362500000000000000 : ℝ)+2*(9551336723/17953125000000 : ℝ)*(10601/100000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (14361005510045733527/14362500000000000000 : ℝ)+2*(9551336723/17953125000000 : ℝ)*(10601/100000 : ℝ)=(2500021857193271/2500000000000000 : ℝ) by norm_num, show 1+2*(524560006772543/25000000000000000000 : ℝ)=(12500524560006772543/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16769835579301559/100000000000000000000 : ℝ)+(524560006772543/25000000000000000000 : ℝ) ≤ ((14361005510045733527/14362500000000000000 : ℝ)+(9551336723/17953125000000 : ℝ)*((8173/50000 : ℝ)+(10601/100000 : ℝ)))^(4915/1024 : ℝ) := by
    rw [show (14361005510045733527/14362500000000000000 : ℝ)+(9551336723/17953125000000 : ℝ)*((8173/50000 : ℝ)+(10601/100000 : ℝ))=(500019653577411/500000000000000 : ℝ) by norm_num, show 1+(16769835579301559/100000000000000000000 : ℝ)+(524560006772543/25000000000000000000 : ℝ)=(100018868075606391731/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16769835579301559/100000000000000000000 : ℝ) ≤ ((14361005510045733527/14362500000000000000 : ℝ)+2*(9551336723/17953125000000 : ℝ)*(8173/50000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (14361005510045733527/14362500000000000000 : ℝ)+2*(9551336723/17953125000000 : ℝ)*(8173/50000 : ℝ)=(2500174678580839/2500000000000000 : ℝ) by norm_num, show 1+2*(16769835579301559/100000000000000000000 : ℝ)=(50016769835579301559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14361005510045733527/14362500000000000000 : ℝ)*(X 1 0+X 2 0)+(9551336723/17953125000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (10601/100000 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (14361005510045733527/14362500000000000000 : ℝ)) (alpha := (9551336723/17953125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14361005510045733527/14362500000000000000 : ℝ)*(X 0 1+X 2 1)+(9551336723/17953125000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (10601/100000 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (14361005510045733527/14362500000000000000 : ℝ)) (alpha := (9551336723/17953125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14361005510045733527/14362500000000000000 : ℝ)*(X 0 2+X 1 2)+(9551336723/17953125000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (10601/100000 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (14361005510045733527/14362500000000000000 : ℝ)) (alpha := (9551336723/17953125000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-804257553/5000000000 : ℝ)*X 0 0+(2723802821/5000000000 : ℝ)*X 0 1+(323990337/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069552643/2000000000 : ℝ)*X 1 0+(-1744298097/10000000000 : ℝ)*X 1 1+(5183845433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673881601/5000000000 : ℝ)*X 2 0+(2591922713/5000000000 : ℝ)*X 2 1+(-1744298123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((130647407/312500000 : ℝ)*X 0 0+(192480391/500000000 : ℝ)*X 0 1+(4532021723/10000000000 : ℝ)*X 0 2+(130647407/312500000 : ℝ)*X 1 0+(192480391/500000000 : ℝ)*X 1 1+(4532021723/10000000000 : ℝ)*X 1 2+(130647407/312500000 : ℝ)*X 2 0+(192480391/500000000 : ℝ)*X 2 1+(4532021723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-804289571/5000000000 : ℝ)*X 0 0+(5185843027/10000000000 : ℝ)*X 0 1+(5445587237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638649101/5000000000 : ℝ)*X 1 0+(-296511231/2000000000 : ℝ)*X 1 1+(5445587547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277298193/10000000000 : ℝ)*X 2 0+(5445587457/10000000000 : ℝ)*X 2 1+(-1482556293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180883807/10000000000 : ℝ)*X 0 0+(4526854707/10000000000 : ℝ)*X 0 1+(240926823/625000000 : ℝ)*X 0 2+(4180883807/10000000000 : ℝ)*X 1 0+(4526854707/10000000000 : ℝ)*X 1 1+(240926823/625000000 : ℝ)*X 1 2+(4180883807/10000000000 : ℝ)*X 2 0+(4526854707/10000000000 : ℝ)*X 2 1+(240926823/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29637170847923420854065327/3740234375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1421806389/100000000000000 : ℝ)*(base19) + (10345701/800000000000 : ℝ)*(base23) + (12768027/20000000000000 : ℝ)*(lower2) + (236017377/100000000000000 : ℝ)*(upper3) + (128303321/100000000000000 : ℝ)*(upper5) + (328547471022021/12500000000000 : ℝ)*(major0) + (328547471022021/12500000000000 : ℝ)*(major1) + (328547471022021/12500000000000 : ℝ)*(major2) + (3791340957364927/100000000000000 : ℝ)*(sp0) + (1895678637036041/50000000000000 : ℝ)*(sp1) + (1895678701332923/50000000000000 : ℝ)*(sp2) + (36634820951807/2500000000000 : ℝ)*(sp3) + (3547702709/20000000000000 : ℝ)*(sp4) + (7738272223/100000000000000 : ℝ)*(sp7) + (1465400576344503/100000000000000 : ℝ)*(f.failure) + (473919836984809/12500000000000 : ℝ)*(f.sum) + (11426870708059/9575000000000000000000000000 : ℝ)*base66 + (6608336270679811/59843750000000000000000000000000 : ℝ)*base68 + (372904069140413939/59843750000000000000000000000000 : ℝ)*base69 + (332328758419476439/59843750000000000000000000000000 : ℝ)*base71 + (13054649405091/9575000000000000000000000000 : ℝ)*base73 + (235651832651195189/59843750000000000000000000000000 : ℝ)*base75 + (59265601334163939/59843750000000000000000000000000 : ℝ)*base77 + (500142461776038939/59843750000000000000000000000000 : ℝ)*base79 + (7963447647083/4787500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10968027/2000000000000000000000 : ℝ)*base89 + (10968027/2000000000000000000000 : ℝ)*base91 + (10968027/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (553917915869448999185540471/47875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1127317023/100000000000000 : ℝ)*(base19) + (1705337901/100000000000000 : ℝ)*(base23) + (64449219/20000000000000 : ℝ)*(upper3) + (124127177/50000000000000 : ℝ)*(lower4) + (13587637/20000000000000 : ℝ)*(upper5) + (533797148259073/20000000000000 : ℝ)*(major0) + (533797148259073/20000000000000 : ℝ)*(major1) + (533797148259073/20000000000000 : ℝ)*(major2) + (11863908529/100000000000000 : ℝ)*(sp1) + (20414172437/100000000000000 : ℝ)*(sp2) + (3849931472318727/100000000000000 : ℝ)*(sp4) + (153996739243727/4000000000000 : ℝ)*(sp5) + (962477338202097/25000000000000 : ℝ)*(sp6) + (148803962460243/10000000000000 : ℝ)*(sp7) + (148803962460243/10000000000000 : ℝ)*(f.failure) + (3849931472318727/100000000000000 : ℝ)*(f.sum) + (2316828892601/718125000000000000000000000 : ℝ)*base65 + (109718415662830157/95750000000000000000000000000000 : ℝ)*base67 + (780063440512169843/95750000000000000000000000000000 : ℝ)*base70 + (202004328500830157/95750000000000000000000000000000 : ℝ)*base71 + (2283999038197/1436250000000000000000000000 : ℝ)*base73 + (374639028259419843/95750000000000000000000000000000 : ℝ)*base76 + (28367688988919843/95750000000000000000000000000000 : ℝ)*base78 + (330774274378919843/95750000000000000000000000000000 : ℝ)*base80 + (18727427535797/5745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (840313/200000000000000000000 : ℝ)*base90 + (840313/200000000000000000000 : ℝ)*base92 + (840313/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1650_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5333/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1650_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1650_s4_0 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1608560813/10000000000 : ℝ)*x 0 + (1361844133/2500000000 : ℝ)*x 1 + (5184043907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1608560813/10000000000 : ℝ)^4919 ≤ (155463703101/1562500000000 : ℝ)^3895 := by
    have hnat : (1608560813 : ℕ)^4919*1562500000000^3895 ≤ 155463703101^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608560813 10000000000 155463703101 1562500000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361844133/2500000000 : ℝ)^4919 ≤ (46433429052681/100000000000000 : ℝ)^3895 := by
    have hnat : (1361844133 : ℕ)^4919*100000000000000^3895 ≤ 46433429052681^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361844133 2500000000 46433429052681 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184043907/10000000000 : ℝ)^4919 ≤ (2726055871097/6250000000000 : ℝ)^3895 := by
    have hnat : (5184043907 : ℕ)^4919*6250000000000^3895 ≤ 2726055871097^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184043907 10000000000 2726055871097 6250000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1608560813/10000000000 : ℝ), (1361844133/2500000000 : ℝ), (5184043907/10000000000 : ℝ)] ![(155463703101/1562500000000 : ℝ), (46433429052681/100000000000000 : ℝ), (2726055871097/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1608560813/10000000000 : ℝ)|^4919 ≤ (155463703101/1562500000000 : ℝ)^3895
        have hw : |(-1608560813/10000000000 : ℝ)|=(1608560813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361844133/2500000000 : ℝ)|^4919 ≤ (46433429052681/100000000000000 : ℝ)^3895
        have hw : |(1361844133/2500000000 : ℝ)|=(1361844133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184043907/10000000000 : ℝ)|^4919 ≤ (2726055871097/6250000000000 : ℝ)^3895
        have hw : |(5184043907/10000000000 : ℝ)|=(5184043907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_1 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347700891/10000000000 : ℝ)*x 0 + (-436029371/2500000000 : ℝ)*x 1 + (2592021953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347700891/10000000000 : ℝ)^4919 ≤ (22681508291993/50000000000000 : ℝ)^3895 := by
    have hnat : (5347700891 : ℕ)^4919*50000000000000^3895 ≤ 22681508291993^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347700891 10000000000 22681508291993 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436029371/2500000000 : ℝ)^4919 ≤ (11020089468171/100000000000000 : ℝ)^3895 := by
    have hnat : (436029371 : ℕ)^4919*100000000000000^3895 ≤ 11020089468171^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436029371 2500000000 11020089468171 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592021953/5000000000 : ℝ)^4919 ≤ (21808446963463/50000000000000 : ℝ)^3895 := by
    have hnat : (2592021953 : ℕ)^4919*50000000000000^3895 ≤ 21808446963463^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592021953 5000000000 21808446963463 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347700891/10000000000 : ℝ), (-436029371/2500000000 : ℝ), (2592021953/5000000000 : ℝ)] ![(22681508291993/50000000000000 : ℝ), (11020089468171/100000000000000 : ℝ), (21808446963463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347700891/10000000000 : ℝ)|^4919 ≤ (22681508291993/50000000000000 : ℝ)^3895
        have hw : |(5347700891/10000000000 : ℝ)|=(5347700891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436029371/2500000000 : ℝ)|^4919 ≤ (11020089468171/100000000000000 : ℝ)^3895
        have hw : |(-436029371/2500000000 : ℝ)|=(436029371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592021953/5000000000 : ℝ)|^4919 ≤ (21808446963463/50000000000000 : ℝ)^3895
        have hw : |(2592021953/5000000000 : ℝ)|=(2592021953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_2 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336925223/2500000000 : ℝ)*x 0 + (2592021953/5000000000 : ℝ)*x 1 + (-436029371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336925223/2500000000 : ℝ)^4919 ≤ (45363016594699/100000000000000 : ℝ)^3895 := by
    have hnat : (1336925223 : ℕ)^4919*100000000000000^3895 ≤ 45363016594699^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336925223 2500000000 45363016594699 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592021953/5000000000 : ℝ)^4919 ≤ (21808446963463/50000000000000 : ℝ)^3895 := by
    have hnat : (2592021953 : ℕ)^4919*50000000000000^3895 ≤ 21808446963463^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592021953 5000000000 21808446963463 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436029371/2500000000 : ℝ)^4919 ≤ (11020089468171/100000000000000 : ℝ)^3895 := by
    have hnat : (436029371 : ℕ)^4919*100000000000000^3895 ≤ 11020089468171^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436029371 2500000000 11020089468171 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336925223/2500000000 : ℝ), (2592021953/5000000000 : ℝ), (-436029371/2500000000 : ℝ)] ![(45363016594699/100000000000000 : ℝ), (21808446963463/50000000000000 : ℝ), (11020089468171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336925223/2500000000 : ℝ)|^4919 ≤ (45363016594699/100000000000000 : ℝ)^3895
        have hw : |(1336925223/2500000000 : ℝ)|=(1336925223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592021953/5000000000 : ℝ)|^4919 ≤ (21808446963463/50000000000000 : ℝ)^3895
        have hw : |(2592021953/5000000000 : ℝ)|=(2592021953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436029371/2500000000 : ℝ)|^4919 ≤ (11020089468171/100000000000000 : ℝ)^3895
        have hw : |(-436029371/2500000000 : ℝ)|=(436029371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_3 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2090373269/5000000000 : ℝ)*x 0 + (1925079041/5000000000 : ℝ)*x 1 + (566433207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090373269/5000000000 : ℝ)^4919 ≤ (3324153235059/10000000000000 : ℝ)^3895 := by
    have hnat : (2090373269 : ℕ)^4919*10000000000000^3895 ≤ 3324153235059^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090373269 5000000000 3324153235059 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1925079041/5000000000 : ℝ)^4919 ≤ (5991428651667/20000000000000 : ℝ)^3895 := by
    have hnat : (1925079041 : ℕ)^4919*20000000000000^3895 ≤ 5991428651667^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925079041 5000000000 5991428651667 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566433207/1250000000 : ℝ)^4919 ≤ (36801324377491/100000000000000 : ℝ)^3895 := by
    have hnat : (566433207 : ℕ)^4919*100000000000000^3895 ≤ 36801324377491^3895*1250000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566433207 1250000000 36801324377491 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090373269/5000000000 : ℝ), (1925079041/5000000000 : ℝ), (566433207/1250000000 : ℝ)] ![(3324153235059/10000000000000 : ℝ), (5991428651667/20000000000000 : ℝ), (36801324377491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090373269/5000000000 : ℝ)|^4919 ≤ (3324153235059/10000000000000 : ℝ)^3895
        have hw : |(2090373269/5000000000 : ℝ)|=(2090373269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1925079041/5000000000 : ℝ)|^4919 ≤ (5991428651667/20000000000000 : ℝ)^3895
        have hw : |(1925079041/5000000000 : ℝ)|=(1925079041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566433207/1250000000 : ℝ)|^4919 ≤ (36801324377491/100000000000000 : ℝ)^3895
        have hw : |(566433207/1250000000 : ℝ)|=(566433207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_4 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402156223/2500000000 : ℝ)*x 0 + (5186034589/10000000000 : ℝ)*x 1 + (5445364917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402156223/2500000000 : ℝ)^4919 ≤ (1990035512319/20000000000000 : ℝ)^3895 := by
    have hnat : (402156223 : ℕ)^4919*20000000000000^3895 ≤ 1990035512319^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402156223 2500000000 1990035512319 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186034589/10000000000 : ℝ)^4919 ≤ (21819023645681/50000000000000 : ℝ)^3895 := by
    have hnat : (5186034589 : ℕ)^4919*50000000000000^3895 ≤ 21819023645681^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186034589 10000000000 21819023645681 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445364917/10000000000 : ℝ)^4919 ≤ (11602943783477/25000000000000 : ℝ)^3895 := by
    have hnat : (5445364917 : ℕ)^4919*25000000000000^3895 ≤ 11602943783477^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445364917 10000000000 11602943783477 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402156223/2500000000 : ℝ), (5186034589/10000000000 : ℝ), (5445364917/10000000000 : ℝ)] ![(1990035512319/20000000000000 : ℝ), (21819023645681/50000000000000 : ℝ), (11602943783477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402156223/2500000000 : ℝ)|^4919 ≤ (1990035512319/20000000000000 : ℝ)^3895
        have hw : |(-402156223/2500000000 : ℝ)|=(402156223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186034589/10000000000 : ℝ)|^4919 ≤ (21819023645681/50000000000000 : ℝ)^3895
        have hw : |(5186034589/10000000000 : ℝ)|=(5186034589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445364917/10000000000 : ℝ)|^4919 ≤ (11602943783477/25000000000000 : ℝ)^3895
        have hw : |(5445364917/10000000000 : ℝ)|=(5445364917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_5 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659668821/1250000000 : ℝ)*x 0 + (-1482796501/10000000000 : ℝ)*x 1 + (1361341221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659668821/1250000000 : ℝ)^4919 ≤ (44610673091/100000000000 : ℝ)^3895 := by
    have hnat : (659668821 : ℕ)^4919*100000000000^3895 ≤ 44610673091^3895*1250000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659668821 1250000000 44610673091 100000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1482796501/10000000000 : ℝ)^4919 ≤ (359102084709/4000000000000 : ℝ)^3895 := by
    have hnat : (1482796501 : ℕ)^4919*4000000000000^3895 ≤ 359102084709^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482796501 10000000000 359102084709 4000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361341221/2500000000 : ℝ)^4919 ≤ (46411774778699/100000000000000 : ℝ)^3895 := by
    have hnat : (1361341221 : ℕ)^4919*100000000000000^3895 ≤ 46411774778699^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361341221 2500000000 46411774778699 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659668821/1250000000 : ℝ), (-1482796501/10000000000 : ℝ), (1361341221/2500000000 : ℝ)] ![(44610673091/100000000000 : ℝ), (359102084709/4000000000000 : ℝ), (46411774778699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659668821/1250000000 : ℝ)|^4919 ≤ (44610673091/100000000000 : ℝ)^3895
        have hw : |(659668821/1250000000 : ℝ)|=(659668821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1482796501/10000000000 : ℝ)|^4919 ≤ (359102084709/4000000000000 : ℝ)^3895
        have hw : |(-1482796501/10000000000 : ℝ)|=(1482796501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361341221/2500000000 : ℝ)|^4919 ≤ (46411774778699/100000000000000 : ℝ)^3895
        have hw : |(1361341221/2500000000 : ℝ)|=(1361341221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_6 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659668823/1250000000 : ℝ)*x 0 + (1361341219/2500000000 : ℝ)*x 1 + (-148279649/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659668823/1250000000 : ℝ)^4919 ≤ (4461067326181/10000000000000 : ℝ)^3895 := by
    have hnat : (659668823 : ℕ)^4919*10000000000000^3895 ≤ 4461067326181^3895*1250000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659668823 1250000000 4461067326181 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1361341219/2500000000 : ℝ)^4919 ≤ (46411774692587/100000000000000 : ℝ)^3895 := by
    have hnat : (1361341219 : ℕ)^4919*100000000000000^3895 ≤ 46411774692587^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361341219 2500000000 46411774692587 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148279649/1000000000 : ℝ)^4919 ≤ (8977552033617/100000000000000 : ℝ)^3895 := by
    have hnat : (148279649 : ℕ)^4919*100000000000000^3895 ≤ 8977552033617^3895*1000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148279649 1000000000 8977552033617 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659668823/1250000000 : ℝ), (1361341219/2500000000 : ℝ), (-148279649/1000000000 : ℝ)] ![(4461067326181/10000000000000 : ℝ), (46411774692587/100000000000000 : ℝ), (8977552033617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659668823/1250000000 : ℝ)|^4919 ≤ (4461067326181/10000000000000 : ℝ)^3895
        have hw : |(659668823/1250000000 : ℝ)|=(659668823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1361341219/2500000000 : ℝ)|^4919 ≤ (46411774692587/100000000000000 : ℝ)^3895
        have hw : |(1361341219/2500000000 : ℝ)|=(1361341219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-148279649/1000000000 : ℝ)|^4919 ≤ (8977552033617/100000000000000 : ℝ)^3895
        have hw : |(-148279649/1000000000 : ℝ)|=(148279649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s4_7 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836182477/2000000000 : ℝ)*x 0 + (2263157623/5000000000 : ℝ)*x 1 + (771072539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836182477/2000000000 : ℝ)^4919 ≤ (33243197704119/100000000000000 : ℝ)^3895 := by
    have hnat : (836182477 : ℕ)^4919*100000000000000^3895 ≤ 33243197704119^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836182477 2000000000 33243197704119 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263157623/5000000000 : ℝ)^4919 ≤ (3674850770831/10000000000000 : ℝ)^3895 := by
    have hnat : (2263157623 : ℕ)^4919*10000000000000^3895 ≤ 3674850770831^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263157623 5000000000 3674850770831 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771072539/2000000000 : ℝ)^4919 ≤ (30008294570217/100000000000000 : ℝ)^3895 := by
    have hnat : (771072539 : ℕ)^4919*100000000000000^3895 ≤ 30008294570217^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771072539 2000000000 30008294570217 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836182477/2000000000 : ℝ), (2263157623/5000000000 : ℝ), (771072539/2000000000 : ℝ)] ![(33243197704119/100000000000000 : ℝ), (3674850770831/10000000000000 : ℝ), (30008294570217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836182477/2000000000 : ℝ)|^4919 ≤ (33243197704119/100000000000000 : ℝ)^3895
        have hw : |(836182477/2000000000 : ℝ)|=(836182477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263157623/5000000000 : ℝ)|^4919 ≤ (3674850770831/10000000000000 : ℝ)^3895
        have hw : |(2263157623/5000000000 : ℝ)|=(2263157623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771072539/2000000000 : ℝ)|^4919 ≤ (30008294570217/100000000000000 : ℝ)^3895
        have hw : |(771072539/2000000000 : ℝ)|=(771072539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1650_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5333/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1067/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4067/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16273/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5333/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16273/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5333/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16273/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5333/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16273/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5333/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16273/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5333/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16273/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5333/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5333/50000 : ℝ) ^ (4915/1024 : ℝ) ≤ (432142937737787/20000000000000000000 : ℝ) := by
    have hpowers : (5333/50000 : ℝ)^4915 ≤ (432142937737787/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5333 : ℕ)^4915*20000000000000000000^1024 ≤ 432142937737787^1024*50000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5333 50000 432142937737787 20000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5333/50000 : ℝ)) (X := (432142937737787/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16273/100000 : ℝ) ^ (4915/1024 : ℝ) ≤ (16413402041246251/100000000000000000000 : ℝ) := by
    have hpowers : (16273/100000 : ℝ)^4915 ≤ (16413402041246251/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16273 : ℕ)^4915*100000000000000000000^1024 ≤ 16413402041246251^1024*100000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16273 100000 16413402041246251 100000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16273/100000 : ℝ)) (X := (16413402041246251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000432142937737787/10000000000000000000 : ℝ) ≤ (10000090031902141/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (10000432142937737787/10000000000000000000 : ℝ)^1024 ≤ (10000090031902141/10000000000000000 : ℝ)^4915 := by
      have hnat : (10000432142937737787 : ℕ)^1024*10000000000000000^4915 ≤ 10000090031902141^4915*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000432142937737787 10000000000000000000 10000090031902141 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000090031902141/10000000000000000 : ℝ)) (X := (10000432142937737787/10000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50009287058364967593/50000000000000000000 : ℝ) ≤ (2500096737015821/2500000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50009287058364967593/50000000000000000000 : ℝ)^1024 ≤ (2500096737015821/2500000000000000 : ℝ)^4915 := by
      have hnat : (50009287058364967593 : ℕ)^1024*2500000000000000^4915 ≤ 2500096737015821^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009287058364967593 50000000000000000000 2500096737015821 2500000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500096737015821/2500000000000000 : ℝ)) (X := (50009287058364967593/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016413402041246251/50000000000000000000 : ℝ) ≤ (10000683864224427/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (50016413402041246251/50000000000000000000 : ℝ)^1024 ≤ (10000683864224427/10000000000000000 : ℝ)^4915 := by
      have hnat : (50016413402041246251 : ℕ)^1024*10000000000000000^4915 ≤ 10000683864224427^4915*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016413402041246251 50000000000000000000 10000683864224427 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683864224427/10000000000000000 : ℝ)) (X := (50016413402041246251/50000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(432142937737787/20000000000000000000 : ℝ) ≤ ((8009167284760828873/8010000000000000000 : ℝ)+2*(42416594449/80100000000000 : ℝ)*(5333/50000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (8009167284760828873/8010000000000000000 : ℝ)+2*(42416594449/80100000000000 : ℝ)*(5333/50000 : ℝ)=(10000090031902141/10000000000000000 : ℝ) by norm_num, show 1+2*(432142937737787/20000000000000000000 : ℝ)=(10000432142937737787/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16413402041246251/100000000000000000000 : ℝ)+(432142937737787/20000000000000000000 : ℝ) ≤ ((8009167284760828873/8010000000000000000 : ℝ)+(42416594449/80100000000000 : ℝ)*((16273/100000 : ℝ)+(5333/50000 : ℝ)))^(4915/1024 : ℝ) := by
    rw [show (8009167284760828873/8010000000000000000 : ℝ)+(42416594449/80100000000000 : ℝ)*((16273/100000 : ℝ)+(5333/50000 : ℝ))=(2500096737015821/2500000000000000 : ℝ) by norm_num, show 1+(16413402041246251/100000000000000000000 : ℝ)+(432142937737787/20000000000000000000 : ℝ)=(50009287058364967593/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16413402041246251/100000000000000000000 : ℝ) ≤ ((8009167284760828873/8010000000000000000 : ℝ)+2*(42416594449/80100000000000 : ℝ)*(16273/100000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (8009167284760828873/8010000000000000000 : ℝ)+2*(42416594449/80100000000000 : ℝ)*(16273/100000 : ℝ)=(10000683864224427/10000000000000000 : ℝ) by norm_num, show 1+2*(16413402041246251/100000000000000000000 : ℝ)=(50016413402041246251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8009167284760828873/8010000000000000000 : ℝ)*(X 1 0+X 2 0)+(42416594449/80100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (5333/50000 : ℝ)) (hi := (16273/100000 : ℝ)) (c := (8009167284760828873/8010000000000000000 : ℝ)) (alpha := (42416594449/80100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8009167284760828873/8010000000000000000 : ℝ)*(X 0 1+X 2 1)+(42416594449/80100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (5333/50000 : ℝ)) (hi := (16273/100000 : ℝ)) (c := (8009167284760828873/8010000000000000000 : ℝ)) (alpha := (42416594449/80100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8009167284760828873/8010000000000000000 : ℝ)*(X 0 2+X 1 2)+(42416594449/80100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (5333/50000 : ℝ)) (hi := (16273/100000 : ℝ)) (c := (8009167284760828873/8010000000000000000 : ℝ)) (alpha := (42416594449/80100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1608560813/10000000000 : ℝ)*X 0 0+(1361844133/2500000000 : ℝ)*X 0 1+(5184043907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347700891/10000000000 : ℝ)*X 1 0+(-436029371/2500000000 : ℝ)*X 1 1+(2592021953/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336925223/2500000000 : ℝ)*X 2 0+(2592021953/5000000000 : ℝ)*X 2 1+(-436029371/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2090373269/5000000000 : ℝ)*X 0 0+(1925079041/5000000000 : ℝ)*X 0 1+(566433207/1250000000 : ℝ)*X 0 2+(2090373269/5000000000 : ℝ)*X 1 0+(1925079041/5000000000 : ℝ)*X 1 1+(566433207/1250000000 : ℝ)*X 1 2+(2090373269/5000000000 : ℝ)*X 2 0+(1925079041/5000000000 : ℝ)*X 2 1+(566433207/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-402156223/2500000000 : ℝ)*X 0 0+(5186034589/10000000000 : ℝ)*X 0 1+(5445364917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659668821/1250000000 : ℝ)*X 1 0+(-1482796501/10000000000 : ℝ)*X 1 1+(1361341221/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659668823/1250000000 : ℝ)*X 2 0+(1361341219/2500000000 : ℝ)*X 2 1+(-148279649/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836182477/2000000000 : ℝ)*X 0 0+(2263157623/5000000000 : ℝ)*X 0 1+(771072539/2000000000 : ℝ)*X 0 2+(836182477/2000000000 : ℝ)*X 1 0+(2263157623/5000000000 : ℝ)*X 1 1+(771072539/2000000000 : ℝ)*X 1 2+(836182477/2000000000 : ℝ)*X 2 0+(2263157623/5000000000 : ℝ)*X 2 1+(771072539/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (505408305042586712451108063/44500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (449208027/25000000000000 : ℝ)*(base19) + (420829183/25000000000000 : ℝ)*(base23) + (61084381/100000000000000 : ℝ)*(lower2) + (138612873/50000000000000 : ℝ)*(upper3) + (39213429/20000000000000 : ℝ)*(upper5) + (2632654126856907/100000000000000 : ℝ)*(major0) + (2632654126856907/100000000000000 : ℝ)*(major1) + (2632654126856907/100000000000000 : ℝ)*(major2) + (1898750862218027/50000000000000 : ℝ)*(sp0) + (37975224187521/1000000000000 : ℝ)*(sp1) + (1898761266133739/50000000000000 : ℝ)*(sp2) + (1467774239876399/100000000000000 : ℝ)*(sp3) + (5622787039/25000000000000 : ℝ)*(sp4) + (1883934039/20000000000000 : ℝ)*(sp7) + (733891829773297/50000000000000 : ℝ)*(f.failure) + (3797524215584209/100000000000000 : ℝ)*(f.sum) + (599620886773/111250000000000000000000000 : ℝ)*base65 + (340438045976736021/89000000000000000000000000000000 : ℝ)*base68 + (297786116112263979/89000000000000000000000000000000 : ℝ)*base69 + (684638096230263979/89000000000000000000000000000000 : ℝ)*base71 + (2038928562133/445000000000000000000000000 : ℝ)*base74 + (863093061382263979/89000000000000000000000000000000 : ℝ)*base75 + (630786930666263979/89000000000000000000000000000000 : ℝ)*base77 + (594447290560736021/89000000000000000000000000000000 : ℝ)*base80 + (966134701481/222500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (5407827/1000000000000000000000 : ℝ)*base90 + (5407827/1000000000000000000000 : ℝ)*base92 + (5407827/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (189004538609284189176261639/22250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1235483717/100000000000000 : ℝ)*(base19) + (1367817907/100000000000000 : ℝ)*(base23) + (76296173/20000000000000 : ℝ)*(lower1) + (84255929/50000000000000 : ℝ)*(upper3) + (2178103/4000000000000 : ℝ)*(lower4) + (176614951/100000000000000 : ℝ)*(upper5) + (1336620804051229/50000000000000 : ℝ)*(major0) + (1336620804051229/50000000000000 : ℝ)*(major1) + (1336620804051229/50000000000000 : ℝ)*(major2) + (1309888891/100000000000000 : ℝ)*(sp2) + (1928035267510929/50000000000000 : ℝ)*(sp4) + (3856069299538141/100000000000000 : ℝ)*(sp5) + (3856067857315061/100000000000000 : ℝ)*(sp6) + (1490412398030179/100000000000000 : ℝ)*(sp7) + (1490412398030179/100000000000000 : ℝ)*(f.failure) + (1928035267510929/50000000000000 : ℝ)*(f.sum) + (12496694148253/4005000000000000000000000000 : ℝ)*base66 + (2747399896921565083/400500000000000000000000000000000 : ℝ)*base68 + (3229350701319065083/400500000000000000000000000000000 : ℝ)*base70 + (12621216647474934917/400500000000000000000000000000000 : ℝ)*base71 + (547643661677/4005000000000000000000000000 : ℝ)*base73 + (10772656013051934917/400500000000000000000000000000000 : ℝ)*base75 + (1844011236879065083/400500000000000000000000000000000 : ℝ)*base78 + (4470270524581565083/400500000000000000000000000000000 : ℝ)*base80 + (40505215859713/4005000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (18449111/2000000000000000000000 : ℝ)*base89 + (18449111/2000000000000000000000 : ℝ)*base91 + (18449111/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1650_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16273/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5333/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1650_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1650_s5_0 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-804282043/5000000000 : ℝ)*x 0 + (1089472449/2000000000 : ℝ)*x 1 + (207362239/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804282043/5000000000 : ℝ)^4919 ≤ (2429126603/24414062500 : ℝ)^3895 := by
    have hnat : (804282043 : ℕ)^4919*24414062500^3895 ≤ 2429126603^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804282043 5000000000 2429126603 24414062500 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089472449/2000000000 : ℝ)^4919 ≤ (11608318813411/25000000000000 : ℝ)^3895 := by
    have hnat : (1089472449 : ℕ)^4919*25000000000000^3895 ≤ 11608318813411^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089472449 2000000000 11608318813411 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207362239/400000000 : ℝ)^4919 ≤ (43617022167911/100000000000000 : ℝ)^3895 := by
    have hnat : (207362239 : ℕ)^4919*100000000000000^3895 ≤ 43617022167911^3895*400000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207362239 400000000 43617022167911 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-804282043/5000000000 : ℝ), (1089472449/2000000000 : ℝ), (207362239/400000000 : ℝ)] ![(2429126603/24414062500 : ℝ), (11608318813411/25000000000000 : ℝ), (43617022167911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-804282043/5000000000 : ℝ)|^4919 ≤ (2429126603/24414062500 : ℝ)^3895
        have hw : |(-804282043/5000000000 : ℝ)|=(804282043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089472449/2000000000 : ℝ)|^4919 ≤ (11608318813411/25000000000000 : ℝ)^3895
        have hw : |(1089472449/2000000000 : ℝ)|=(1089472449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207362239/400000000 : ℝ)|^4919 ≤ (43617022167911/100000000000000 : ℝ)^3895
        have hw : |(207362239/400000000 : ℝ)|=(207362239/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s5_1 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347696797/10000000000 : ℝ)*x 0 + (-1744105641/10000000000 : ℝ)*x 1 + (162001779/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347696797/10000000000 : ℝ)^4919 ≤ (11340743181417/25000000000000 : ℝ)^3895 := by
    have hnat : (5347696797 : ℕ)^4919*25000000000000^3895 ≤ 11340743181417^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347696797 10000000000 11340743181417 25000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744105641/10000000000 : ℝ)^4919 ≤ (1101999496637/10000000000000 : ℝ)^3895 := by
    have hnat : (1744105641 : ℕ)^4919*10000000000000^3895 ≤ 1101999496637^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744105641 10000000000 1101999496637 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162001779/312500000 : ℝ)^4919 ≤ (545212903677/1250000000000 : ℝ)^3895 := by
    have hnat : (162001779 : ℕ)^4919*1250000000000^3895 ≤ 545212903677^3895*312500000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162001779 312500000 545212903677 1250000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347696797/10000000000 : ℝ), (-1744105641/10000000000 : ℝ), (162001779/312500000 : ℝ)] ![(11340743181417/25000000000000 : ℝ), (1101999496637/10000000000000 : ℝ), (545212903677/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347696797/10000000000 : ℝ)|^4919 ≤ (11340743181417/25000000000000 : ℝ)^3895
        have hw : |(5347696797/10000000000 : ℝ)|=(5347696797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1744105641/10000000000 : ℝ)|^4919 ≤ (1101999496637/10000000000000 : ℝ)^3895
        have hw : |(-1744105641/10000000000 : ℝ)|=(1744105641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162001779/312500000 : ℝ)|^4919 ≤ (545212903677/1250000000000 : ℝ)^3895
        have hw : |(162001779/312500000 : ℝ)|=(162001779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s5_2 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334231049/625000000 : ℝ)*x 0 + (5184057409/10000000000 : ℝ)*x 1 + (-872052509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334231049/625000000 : ℝ)^4919 ≤ (45362972586401/100000000000000 : ℝ)^3895 := by
    have hnat : (334231049 : ℕ)^4919*100000000000000^3895 ≤ 45362972586401^3895*625000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334231049 625000000 45362972586401 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184057409/10000000000 : ℝ)^4919 ≤ (436170374051/1000000000000 : ℝ)^3895 := by
    have hnat : (5184057409 : ℕ)^4919*1000000000000^3895 ≤ 436170374051^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184057409 10000000000 436170374051 1000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (872052509/5000000000 : ℝ)^4919 ≤ (2203997999023/20000000000000 : ℝ)^3895 := by
    have hnat : (872052509 : ℕ)^4919*20000000000000^3895 ≤ 2203997999023^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872052509 5000000000 2203997999023 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334231049/625000000 : ℝ), (5184057409/10000000000 : ℝ), (-872052509/5000000000 : ℝ)] ![(45362972586401/100000000000000 : ℝ), (436170374051/1000000000000 : ℝ), (2203997999023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334231049/625000000 : ℝ)|^4919 ≤ (45362972586401/100000000000000 : ℝ)^3895
        have hw : |(334231049/625000000 : ℝ)|=(334231049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184057409/10000000000 : ℝ)|^4919 ≤ (436170374051/1000000000000 : ℝ)^3895
        have hw : |(5184057409/10000000000 : ℝ)|=(5184057409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-872052509/5000000000 : ℝ)|^4919 ≤ (2203997999023/20000000000000 : ℝ)^3895
        have hw : |(-872052509/5000000000 : ℝ)|=(872052509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s5_3 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180748227/10000000000 : ℝ)*x 0 + (770038563/2000000000 : ℝ)*x 1 + (2265715363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180748227/10000000000 : ℝ)^4919 ≤ (6648309862121/20000000000000 : ℝ)^3895 := by
    have hnat : (4180748227 : ℕ)^4919*20000000000000^3895 ≤ 6648309862121^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180748227 10000000000 6648309862121 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (770038563/2000000000 : ℝ)^4919 ≤ (14978742278271/50000000000000 : ℝ)^3895 := by
    have hnat : (770038563 : ℕ)^4919*50000000000000^3895 ≤ 14978742278271^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770038563 2000000000 14978742278271 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265715363/5000000000 : ℝ)^4919 ≤ (3680096612249/10000000000000 : ℝ)^3895 := by
    have hnat : (2265715363 : ℕ)^4919*10000000000000^3895 ≤ 3680096612249^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265715363 5000000000 3680096612249 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180748227/10000000000 : ℝ), (770038563/2000000000 : ℝ), (2265715363/5000000000 : ℝ)] ![(6648309862121/20000000000000 : ℝ), (14978742278271/50000000000000 : ℝ), (3680096612249/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180748227/10000000000 : ℝ)|^4919 ≤ (6648309862121/20000000000000 : ℝ)^3895
        have hw : |(4180748227/10000000000 : ℝ)|=(4180748227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(770038563/2000000000 : ℝ)|^4919 ≤ (14978742278271/50000000000000 : ℝ)^3895
        have hw : |(770038563/2000000000 : ℝ)|=(770038563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265715363/5000000000 : ℝ)|^4919 ≤ (3680096612249/10000000000000 : ℝ)^3895
        have hw : |(2265715363/5000000000 : ℝ)|=(2265715363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s5_4 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-321725671/2000000000 : ℝ)*x 0 + (1296511793/2500000000 : ℝ)*x 1 + (5445349981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321725671/2000000000 : ℝ)^4919 ≤ (995020461351/10000000000000 : ℝ)^3895 := by
    have hnat : (321725671 : ℕ)^4919*10000000000000^3895 ≤ 995020461351^3895*2000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321725671 2000000000 995020461351 10000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296511793/2500000000 : ℝ)^4919 ≤ (43638181007429/100000000000000 : ℝ)^3895 := by
    have hnat : (1296511793 : ℕ)^4919*100000000000000^3895 ≤ 43638181007429^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296511793 2500000000 43638181007429 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445349981/10000000000 : ℝ)^4919 ≤ (5801451795503/12500000000000 : ℝ)^3895 := by
    have hnat : (5445349981 : ℕ)^4919*12500000000000^3895 ≤ 5801451795503^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445349981 10000000000 5801451795503 12500000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-321725671/2000000000 : ℝ), (1296511793/2500000000 : ℝ), (5445349981/10000000000 : ℝ)] ![(995020461351/10000000000000 : ℝ), (43638181007429/100000000000000 : ℝ), (5801451795503/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-321725671/2000000000 : ℝ)|^4919 ≤ (995020461351/10000000000000 : ℝ)^3895
        have hw : |(-321725671/2000000000 : ℝ)|=(321725671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296511793/2500000000 : ℝ)|^4919 ≤ (43638181007429/100000000000000 : ℝ)^3895
        have hw : |(1296511793/2500000000 : ℝ)|=(1296511793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445349981/10000000000 : ℝ)|^4919 ≤ (5801451795503/12500000000000 : ℝ)^3895
        have hw : |(5445349981/10000000000 : ℝ)|=(5445349981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s5_5 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277353877/10000000000 : ℝ)*x 0 + (-370703091/2500000000 : ℝ)*x 1 + (2722675167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277353877/10000000000 : ℝ)^4919 ≤ (8922141683311/20000000000000 : ℝ)^3895 := by
    have hnat : (5277353877 : ℕ)^4919*20000000000000^3895 ≤ 8922141683311^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277353877 10000000000 8922141683311 20000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370703091/2500000000 : ℝ)^4919 ≤ (8977673409591/100000000000000 : ℝ)^3895 := by
    have hnat : (370703091 : ℕ)^4919*100000000000000^3895 ≤ 8977673409591^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370703091 2500000000 8977673409591 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722675167/5000000000 : ℝ)^4919 ≤ (23205809081843/50000000000000 : ℝ)^3895 := by
    have hnat : (2722675167 : ℕ)^4919*50000000000000^3895 ≤ 23205809081843^3895*5000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722675167 5000000000 23205809081843 50000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277353877/10000000000 : ℝ), (-370703091/2500000000 : ℝ), (2722675167/5000000000 : ℝ)] ![(8922141683311/20000000000000 : ℝ), (8977673409591/100000000000000 : ℝ), (23205809081843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277353877/10000000000 : ℝ)|^4919 ≤ (8922141683311/20000000000000 : ℝ)^3895
        have hw : |(5277353877/10000000000 : ℝ)|=(5277353877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370703091/2500000000 : ℝ)|^4919 ≤ (8977673409591/100000000000000 : ℝ)^3895
        have hw : |(-370703091/2500000000 : ℝ)|=(370703091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722675167/5000000000 : ℝ)|^4919 ≤ (23205809081843/50000000000000 : ℝ)^3895
        have hw : |(2722675167/5000000000 : ℝ)|=(2722675167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1650_s5_6 (p : ℝ) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180914431/10000000000 : ℝ)*x 0 + (1131569989/2500000000 : ℝ)*x 1 + (481924677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180914431/10000000000 : ℝ)^4919 ≤ (33243218249147/100000000000000 : ℝ)^3895 := by
    have hnat : (4180914431 : ℕ)^4919*100000000000000^3895 ≤ 33243218249147^3895*10000000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180914431 10000000000 33243218249147 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131569989/2500000000 : ℝ)^4919 ≤ (36748145869219/100000000000000 : ℝ)^3895 := by
    have hnat : (1131569989 : ℕ)^4919*100000000000000^3895 ≤ 36748145869219^3895*2500000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131569989 2500000000 36748145869219 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (481924677/1250000000 : ℝ)^4919 ≤ (30008635871699/100000000000000 : ℝ)^3895 := by
    have hnat : (481924677 : ℕ)^4919*100000000000000^3895 ≤ 30008635871699^3895*1250000000^4919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481924677 1250000000 30008635871699 100000000000000 4919 3895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4919/1024 : ℝ)) 4919 3895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180914431/10000000000 : ℝ), (1131569989/2500000000 : ℝ), (481924677/1250000000 : ℝ)] ![(33243218249147/100000000000000 : ℝ), (36748145869219/100000000000000 : ℝ), (30008635871699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180914431/10000000000 : ℝ)|^4919 ≤ (33243218249147/100000000000000 : ℝ)^3895
        have hw : |(4180914431/10000000000 : ℝ)|=(4180914431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131569989/2500000000 : ℝ)|^4919 ≤ (36748145869219/100000000000000 : ℝ)^3895
        have hw : |(1131569989/2500000000 : ℝ)|=(1131569989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(481924677/1250000000 : ℝ)|^4919 ≤ (30008635871699/100000000000000 : ℝ)^3895
        have hw : |(481924677/1250000000 : ℝ)|=(481924677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1650_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10671/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4067/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4067/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1067/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4067/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1067/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4067/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1067/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4067/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1067/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4067/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1067/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4067/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1067/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1067/10000 : ℝ) ^ (4915/1024 : ℝ) ≤ (1082303416068343/50000000000000000000 : ℝ) := by
    have hpowers : (1067/10000 : ℝ)^4915 ≤ (1082303416068343/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1067 : ℕ)^4915*50000000000000000000^1024 ≤ 1082303416068343^1024*10000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1067 10000 1082303416068343 50000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1067/10000 : ℝ)) (X := (1082303416068343/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4067/25000 : ℝ) ^ (4915/1024 : ℝ) ≤ (327784201655481/2000000000000000000 : ℝ) := by
    have hpowers : (4067/25000 : ℝ)^4915 ≤ (327784201655481/2000000000000000000 : ℝ)^1024 := by
      have hnat : (4067 : ℕ)^4915*2000000000000000000^1024 ≤ 327784201655481^1024*25000^4915 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4067 25000 327784201655481 2000000000000000000 4915 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4067/25000 : ℝ)) (X := (327784201655481/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001082303416068343/25000000000000000000 : ℝ) ≤ (10000090194075831/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (25001082303416068343/25000000000000000000 : ℝ)^1024 ≤ (10000090194075831/10000000000000000 : ℝ)^4915 := by
      have hnat : (25001082303416068343 : ℕ)^1024*10000000000000000^4915 ≤ 10000090194075831^4915*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001082303416068343 25000000000000000000 10000090194075831 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000090194075831/10000000000000000 : ℝ)) (X := (25001082303416068343/25000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251159613557181921/6250000000000000000 : ℝ) ≤ (10000386525195407/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (6251159613557181921/6250000000000000000 : ℝ)^1024 ≤ (10000386525195407/10000000000000000 : ℝ)^4915 := by
      have hnat : (6251159613557181921 : ℕ)^1024*10000000000000000^4915 ≤ 10000386525195407^4915*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251159613557181921 6250000000000000000 10000386525195407 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000386525195407/10000000000000000 : ℝ)) (X := (6251159613557181921/6250000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000327784201655481/1000000000000000000 : ℝ) ≤ (10000682856314983/10000000000000000 : ℝ) ^ (4915/1024 : ℝ) := by
    have hpowers : (1000327784201655481/1000000000000000000 : ℝ)^1024 ≤ (10000682856314983/10000000000000000 : ℝ)^4915 := by
      have hnat : (1000327784201655481 : ℕ)^1024*10000000000000000^4915 ≤ 10000682856314983^4915*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000327784201655481 1000000000000000000 10000682856314983 10000000000000000 1024 4915 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682856314983/10000000000000000 : ℝ)) (X := (1000327784201655481/1000000000000000000 : ℝ)) (by norm_num) 4915 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1082303416068343/50000000000000000000 : ℝ) ≤ ((27987090600172375049/27990000000000000000 : ℝ)+2*(37041389947/69975000000000 : ℝ)*(1067/10000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (27987090600172375049/27990000000000000000 : ℝ)+2*(37041389947/69975000000000 : ℝ)*(1067/10000 : ℝ)=(10000090194075831/10000000000000000 : ℝ) by norm_num, show 1+2*(1082303416068343/50000000000000000000 : ℝ)=(25001082303416068343/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(327784201655481/2000000000000000000 : ℝ)+(1082303416068343/50000000000000000000 : ℝ) ≤ ((27987090600172375049/27990000000000000000 : ℝ)+(37041389947/69975000000000 : ℝ)*((4067/25000 : ℝ)+(1067/10000 : ℝ)))^(4915/1024 : ℝ) := by
    rw [show (27987090600172375049/27990000000000000000 : ℝ)+(37041389947/69975000000000 : ℝ)*((4067/25000 : ℝ)+(1067/10000 : ℝ))=(10000386525195407/10000000000000000 : ℝ) by norm_num, show 1+(327784201655481/2000000000000000000 : ℝ)+(1082303416068343/50000000000000000000 : ℝ)=(6251159613557181921/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(327784201655481/2000000000000000000 : ℝ) ≤ ((27987090600172375049/27990000000000000000 : ℝ)+2*(37041389947/69975000000000 : ℝ)*(4067/25000 : ℝ))^(4915/1024 : ℝ) := by
    rw [show (27987090600172375049/27990000000000000000 : ℝ)+2*(37041389947/69975000000000 : ℝ)*(4067/25000 : ℝ)=(10000682856314983/10000000000000000 : ℝ) by norm_num, show 1+2*(327784201655481/2000000000000000000 : ℝ)=(1000327784201655481/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27987090600172375049/27990000000000000000 : ℝ)*(X 1 0+X 2 0)+(37041389947/69975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (1067/10000 : ℝ)) (hi := (4067/25000 : ℝ)) (c := (27987090600172375049/27990000000000000000 : ℝ)) (alpha := (37041389947/69975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27987090600172375049/27990000000000000000 : ℝ)*(X 0 1+X 2 1)+(37041389947/69975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (1067/10000 : ℝ)) (hi := (4067/25000 : ℝ)) (c := (27987090600172375049/27990000000000000000 : ℝ)) (alpha := (37041389947/69975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27987090600172375049/27990000000000000000 : ℝ)*(X 0 2+X 1 2)+(37041389947/69975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4915/1024 : ℝ)) (lo := (1067/10000 : ℝ)) (hi := (4067/25000 : ℝ)) (c := (27987090600172375049/27990000000000000000 : ℝ)) (alpha := (37041389947/69975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-804282043/5000000000 : ℝ)*X 0 0+(1089472449/2000000000 : ℝ)*X 0 1+(207362239/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347696797/10000000000 : ℝ)*X 1 0+(-1744105641/10000000000 : ℝ)*X 1 1+(162001779/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334231049/625000000 : ℝ)*X 2 0+(5184057409/10000000000 : ℝ)*X 2 1+(-872052509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4180748227/10000000000 : ℝ)*X 0 0+(770038563/2000000000 : ℝ)*X 0 1+(2265715363/5000000000 : ℝ)*X 0 2+(4180748227/10000000000 : ℝ)*X 1 0+(770038563/2000000000 : ℝ)*X 1 1+(2265715363/5000000000 : ℝ)*X 1 2+(4180748227/10000000000 : ℝ)*X 2 0+(770038563/2000000000 : ℝ)*X 2 1+(2265715363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-321725671/2000000000 : ℝ)*X 0 0+(1296511793/2500000000 : ℝ)*X 0 1+(5445349981/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277353877/10000000000 : ℝ)*X 1 0+(-370703091/2500000000 : ℝ)*X 1 1+(2722675167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4180914431/10000000000 : ℝ)*X 0 0+(1131569989/2500000000 : ℝ)*X 0 1+(481924677/1250000000 : ℝ)*X 0 2+(4180914431/10000000000 : ℝ)*X 1 0+(1131569989/2500000000 : ℝ)*X 1 1+(481924677/1250000000 : ℝ)*X 1 2+(4180914431/10000000000 : ℝ)*X 2 0+(1131569989/2500000000 : ℝ)*X 2 1+(481924677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1650_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122534719090170245831819519/46650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (648288511/100000000000000 : ℝ)*(base19) + (167676763/25000000000000 : ℝ)*(base23) + (1226981/3125000000000 : ℝ)*(lower2) + (24779209/100000000000000 : ℝ)*(upper5) + (263293122464323/10000000000000 : ℝ)*(major0) + (263293122464323/10000000000000 : ℝ)*(major1) + (263293122464323/10000000000000 : ℝ)*(major2) + (3797890423339721/100000000000000 : ℝ)*(sp0) + (3797915575633659/100000000000000 : ℝ)*(sp1) + (3797923541147487/100000000000000 : ℝ)*(sp2) + (2867044758727/195312500000 : ℝ)*(sp3) + (16894257409/50000000000000 : ℝ)*(sp4) + (7987932369/100000000000000 : ℝ)*(sp5) + (11233407621/100000000000000 : ℝ)*(sp6) + (293587629975169/20000000000000 : ℝ)*(f.failure) + (1898962105927269/50000000000000 : ℝ)*(f.sum) + (7671669991751/2799000000000000000000000000 : ℝ)*base65 + (185122296869775203/31100000000000000000000000000000 : ℝ)*base67 + (132725768992175203/31100000000000000000000000000000 : ℝ)*base69 + (221759068495975203/31100000000000000000000000000000 : ℝ)*base71 + (2671588458749/2799000000000000000000000000 : ℝ)*base73 + (160308378740675203/31100000000000000000000000000000 : ℝ)*base75 + (170010317666775203/31100000000000000000000000000000 : ℝ)*base77 + (328466773483575203/31100000000000000000000000000000 : ℝ)*base79 + (888562243979/1399500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (270979/400000000000000000000 : ℝ)*base90 + (270979/400000000000000000000 : ℝ)*base92 + (270979/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1650_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1067/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1650_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1650_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1650_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1650_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1650_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4915/1024 : ℝ) ≤ p) (hpb : p ≤ (4919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35872509/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10601/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4067/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1650_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

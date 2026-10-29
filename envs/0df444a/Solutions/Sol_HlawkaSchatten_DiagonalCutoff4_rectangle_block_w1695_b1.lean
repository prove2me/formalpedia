-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1695_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:40:07.259871+00:00
-- url     : https://prove2.me/submissions/180ae2c7-6a1c-40bc-8a90-2f78194139ea

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
theorem support_rectangle_w1695_s3_0 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1468167809/10000000000 : ℝ)*x 0 + (5479837401/10000000000 : ℝ)*x 1 + (5136147593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1468167809/10000000000 : ℝ)^5183 ≤ (183085947253/2000000000000 : ℝ)^4159 := by
    have hnat : (1468167809 : ℕ)^5183*2000000000000^4159 ≤ 183085947253^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468167809 10000000000 183085947253 2000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479837401/10000000000 : ℝ)^5183 ≤ (11813779955237/25000000000000 : ℝ)^4159 := by
    have hnat : (5479837401 : ℕ)^5183*25000000000000^4159 ≤ 11813779955237^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479837401 10000000000 11813779955237 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136147593/10000000000 : ℝ)^5183 ≤ (43590582801729/100000000000000 : ℝ)^4159 := by
    have hnat : (5136147593 : ℕ)^5183*100000000000000^4159 ≤ 43590582801729^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136147593 10000000000 43590582801729 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1468167809/10000000000 : ℝ), (5479837401/10000000000 : ℝ), (5136147593/10000000000 : ℝ)] ![(183085947253/2000000000000 : ℝ), (11813779955237/25000000000000 : ℝ), (43590582801729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1468167809/10000000000 : ℝ)|^5183 ≤ (183085947253/2000000000000 : ℝ)^4159
        have hw : |(-1468167809/10000000000 : ℝ)|=(1468167809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479837401/10000000000 : ℝ)|^5183 ≤ (11813779955237/25000000000000 : ℝ)^4159
        have hw : |(5479837401/10000000000 : ℝ)|=(5479837401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136147593/10000000000 : ℝ)|^5183 ≤ (43590582801729/100000000000000 : ℝ)^4159
        have hw : |(5136147593/10000000000 : ℝ)|=(5136147593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_1 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668568569/1250000000 : ℝ)*x 0 + (-1646612889/10000000000 : ℝ)*x 1 + (2568073829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668568569/1250000000 : ℝ)^5183 ≤ (45848390024351/100000000000000 : ℝ)^4159 := by
    have hnat : (668568569 : ℕ)^5183*100000000000000^4159 ≤ 45848390024351^4159*1250000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668568569 1250000000 45848390024351 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1646612889/10000000000 : ℝ)^5183 ≤ (1056102646929/10000000000000 : ℝ)^4159 := by
    have hnat : (1646612889 : ℕ)^5183*10000000000000^4159 ≤ 1056102646929^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646612889 10000000000 1056102646929 10000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568073829/5000000000 : ℝ)^5183 ≤ (4359058348921/10000000000000 : ℝ)^4159 := by
    have hnat : (2568073829 : ℕ)^5183*10000000000000^4159 ≤ 4359058348921^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568073829 5000000000 4359058348921 10000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668568569/1250000000 : ℝ), (-1646612889/10000000000 : ℝ), (2568073829/5000000000 : ℝ)] ![(45848390024351/100000000000000 : ℝ), (1056102646929/10000000000000 : ℝ), (4359058348921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668568569/1250000000 : ℝ)|^5183 ≤ (45848390024351/100000000000000 : ℝ)^4159
        have hw : |(668568569/1250000000 : ℝ)|=(668568569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1646612889/10000000000 : ℝ)|^5183 ≤ (1056102646929/10000000000000 : ℝ)^4159
        have hw : |(-1646612889/10000000000 : ℝ)|=(1646612889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568073829/5000000000 : ℝ)|^5183 ≤ (4359058348921/10000000000000 : ℝ)^4159
        have hw : |(2568073829/5000000000 : ℝ)|=(2568073829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_2 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348548749/10000000000 : ℝ)*x 0 + (5136147489/10000000000 : ℝ)*x 1 + (-1646612849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348548749/10000000000 : ℝ)^5183 ≤ (1146209803221/2500000000000 : ℝ)^4159 := by
    have hnat : (5348548749 : ℕ)^5183*2500000000000^4159 ≤ 1146209803221^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348548749 10000000000 1146209803221 2500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136147489/10000000000 : ℝ)^5183 ≤ (43590581701759/100000000000000 : ℝ)^4159 := by
    have hnat : (5136147489 : ℕ)^5183*100000000000000^4159 ≤ 43590581701759^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136147489 10000000000 43590581701759 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1646612849/10000000000 : ℝ)^5183 ≤ (2640256537393/25000000000000 : ℝ)^4159 := by
    have hnat : (1646612849 : ℕ)^5183*25000000000000^4159 ≤ 2640256537393^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646612849 10000000000 2640256537393 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348548749/10000000000 : ℝ), (5136147489/10000000000 : ℝ), (-1646612849/10000000000 : ℝ)] ![(1146209803221/2500000000000 : ℝ), (43590581701759/100000000000000 : ℝ), (2640256537393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348548749/10000000000 : ℝ)|^5183 ≤ (1146209803221/2500000000000 : ℝ)^4159
        have hw : |(5348548749/10000000000 : ℝ)|=(5348548749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136147489/10000000000 : ℝ)|^5183 ≤ (43590581701759/100000000000000 : ℝ)^4159
        have hw : |(5136147489/10000000000 : ℝ)|=(5136147489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1646612849/10000000000 : ℝ)|^5183 ≤ (2640256537393/25000000000000 : ℝ)^4159
        have hw : |(-1646612849/10000000000 : ℝ)|=(1646612849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_3 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1031110737/2500000000 : ℝ)*x 0 + (457714807/1250000000 : ℝ)*x 1 + (4624129989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031110737/2500000000 : ℝ)^5183 ≤ (414546485891/1250000000000 : ℝ)^4159 := by
    have hnat : (1031110737 : ℕ)^5183*1250000000000^4159 ≤ 414546485891^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031110737 2500000000 414546485891 1250000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457714807/1250000000 : ℝ)^5183 ≤ (28592919225823/100000000000000 : ℝ)^4159 := by
    have hnat : (457714807 : ℕ)^5183*100000000000000^4159 ≤ 28592919225823^4159*1250000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457714807 1250000000 28592919225823 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4624129989/10000000000 : ℝ)^5183 ≤ (764867237707/2000000000000 : ℝ)^4159 := by
    have hnat : (4624129989 : ℕ)^5183*2000000000000^4159 ≤ 764867237707^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4624129989 10000000000 764867237707 2000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031110737/2500000000 : ℝ), (457714807/1250000000 : ℝ), (4624129989/10000000000 : ℝ)] ![(414546485891/1250000000000 : ℝ), (28592919225823/100000000000000 : ℝ), (764867237707/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031110737/2500000000 : ℝ)|^5183 ≤ (414546485891/1250000000000 : ℝ)^4159
        have hw : |(1031110737/2500000000 : ℝ)|=(1031110737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457714807/1250000000 : ℝ)|^5183 ≤ (28592919225823/100000000000000 : ℝ)^4159
        have hw : |(457714807/1250000000 : ℝ)|=(457714807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4624129989/10000000000 : ℝ)|^5183 ≤ (764867237707/2000000000000 : ℝ)^4159
        have hw : |(4624129989/10000000000 : ℝ)|=(4624129989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_4 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1468326541/10000000000 : ℝ)*x 0 + (2569952077/5000000000 : ℝ)*x 1 + (5476024841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1468326541/10000000000 : ℝ)^5183 ≤ (366221231407/4000000000000 : ℝ)^4159 := by
    have hnat : (1468326541 : ℕ)^5183*4000000000000^4159 ≤ 366221231407^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468326541 10000000000 366221231407 4000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569952077/5000000000 : ℝ)^5183 ≤ (10907579537161/25000000000000 : ℝ)^4159 := by
    have hnat : (2569952077 : ℕ)^5183*25000000000000^4159 ≤ 10907579537161^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569952077 5000000000 10907579537161 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476024841/10000000000 : ℝ)^5183 ≤ (1888566041883/4000000000000 : ℝ)^4159 := by
    have hnat : (5476024841 : ℕ)^5183*4000000000000^4159 ≤ 1888566041883^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476024841 10000000000 1888566041883 4000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1468326541/10000000000 : ℝ), (2569952077/5000000000 : ℝ), (5476024841/10000000000 : ℝ)] ![(366221231407/4000000000000 : ℝ), (10907579537161/25000000000000 : ℝ), (1888566041883/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1468326541/10000000000 : ℝ)|^5183 ≤ (366221231407/4000000000000 : ℝ)^4159
        have hw : |(-1468326541/10000000000 : ℝ)|=(1468326541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569952077/5000000000 : ℝ)|^5183 ≤ (10907579537161/25000000000000 : ℝ)^4159
        have hw : |(2569952077/5000000000 : ℝ)|=(2569952077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476024841/10000000000 : ℝ)|^5183 ≤ (1888566041883/4000000000000 : ℝ)^4159
        have hw : |(5476024841/10000000000 : ℝ)|=(5476024841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_5 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256623391/10000000000 : ℝ)*x 0 + (-653367619/5000000000 : ℝ)*x 1 + (5476024841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256623391/10000000000 : ℝ)^5183 ≤ (1794738770061/4000000000000 : ℝ)^4159 := by
    have hnat : (5256623391 : ℕ)^5183*4000000000000^4159 ≤ 1794738770061^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256623391 10000000000 1794738770061 4000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653367619/5000000000 : ℝ)^5183 ≤ (989672460993/12500000000000 : ℝ)^4159 := by
    have hnat : (653367619 : ℕ)^5183*12500000000000^4159 ≤ 989672460993^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653367619 5000000000 989672460993 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476024841/10000000000 : ℝ)^5183 ≤ (1888566041883/4000000000000 : ℝ)^4159 := by
    have hnat : (5476024841 : ℕ)^5183*4000000000000^4159 ≤ 1888566041883^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476024841 10000000000 1888566041883 4000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256623391/10000000000 : ℝ), (-653367619/5000000000 : ℝ), (5476024841/10000000000 : ℝ)] ![(1794738770061/4000000000000 : ℝ), (989672460993/12500000000000 : ℝ), (1888566041883/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256623391/10000000000 : ℝ)|^5183 ≤ (1794738770061/4000000000000 : ℝ)^4159
        have hw : |(5256623391/10000000000 : ℝ)|=(5256623391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-653367619/5000000000 : ℝ)|^5183 ≤ (989672460993/12500000000000 : ℝ)^4159
        have hw : |(-653367619/5000000000 : ℝ)|=(653367619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476024841/10000000000 : ℝ)|^5183 ≤ (1888566041883/4000000000000 : ℝ)^4159
        have hw : |(5476024841/10000000000 : ℝ)|=(5476024841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_6 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256623391/10000000000 : ℝ)*x 0 + (2738012421/5000000000 : ℝ)*x 1 + (-1306735237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256623391/10000000000 : ℝ)^5183 ≤ (1794738770061/4000000000000 : ℝ)^4159 := by
    have hnat : (5256623391 : ℕ)^5183*4000000000000^4159 ≤ 1794738770061^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256623391 10000000000 1794738770061 4000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738012421/5000000000 : ℝ)^5183 ≤ (47214151057819/100000000000000 : ℝ)^4159 := by
    have hnat : (2738012421 : ℕ)^5183*100000000000000^4159 ≤ 47214151057819^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738012421 5000000000 47214151057819 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306735237/10000000000 : ℝ)^5183 ≤ (7917379680393/100000000000000 : ℝ)^4159 := by
    have hnat : (1306735237 : ℕ)^5183*100000000000000^4159 ≤ 7917379680393^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306735237 10000000000 7917379680393 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256623391/10000000000 : ℝ), (2738012421/5000000000 : ℝ), (-1306735237/10000000000 : ℝ)] ![(1794738770061/4000000000000 : ℝ), (47214151057819/100000000000000 : ℝ), (7917379680393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256623391/10000000000 : ℝ)|^5183 ≤ (1794738770061/4000000000000 : ℝ)^4159
        have hw : |(5256623391/10000000000 : ℝ)|=(5256623391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738012421/5000000000 : ℝ)|^5183 ≤ (47214151057819/100000000000000 : ℝ)^4159
        have hw : |(2738012421/5000000000 : ℝ)|=(2738012421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306735237/10000000000 : ℝ)|^5183 ≤ (7917379680393/100000000000000 : ℝ)^4159
        have hw : |(-1306735237/10000000000 : ℝ)|=(1306735237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s3_7 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2062443951/5000000000 : ℝ)*x 0 + (2306805191/5000000000 : ℝ)*x 1 + (3672395029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062443951/5000000000 : ℝ)^5183 ≤ (1326727104019/4000000000000 : ℝ)^4159 := by
    have hnat : (2062443951 : ℕ)^5183*4000000000000^4159 ≤ 1326727104019^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062443951 5000000000 1326727104019 4000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306805191/5000000000 : ℝ)^5183 ≤ (7626994032569/20000000000000 : ℝ)^4159 := by
    have hnat : (2306805191 : ℕ)^5183*20000000000000^4159 ≤ 7626994032569^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306805191 5000000000 7626994032569 20000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3672395029/10000000000 : ℝ)^5183 ≤ (28696852224223/100000000000000 : ℝ)^4159 := by
    have hnat : (3672395029 : ℕ)^5183*100000000000000^4159 ≤ 28696852224223^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3672395029 10000000000 28696852224223 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2062443951/5000000000 : ℝ), (2306805191/5000000000 : ℝ), (3672395029/10000000000 : ℝ)] ![(1326727104019/4000000000000 : ℝ), (7626994032569/20000000000000 : ℝ), (28696852224223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2062443951/5000000000 : ℝ)|^5183 ≤ (1326727104019/4000000000000 : ℝ)^4159
        have hw : |(2062443951/5000000000 : ℝ)|=(2062443951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2306805191/5000000000 : ℝ)|^5183 ≤ (7626994032569/20000000000000 : ℝ)^4159
        have hw : |(2306805191/5000000000 : ℝ)|=(2306805191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3672395029/10000000000 : ℝ)|^5183 ≤ (28696852224223/100000000000000 : ℝ)^4159
        have hw : |(3672395029/10000000000 : ℝ)|=(3672395029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1695_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9879/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (43/250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9863/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9863/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9863/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9863/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9863/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9863/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9863/100000 : ℝ) ^ (5175/1024 : ℝ) ≤ (824161736650467/100000000000000000000 : ℝ) := by
    have hpowers : (9863/100000 : ℝ)^5175 ≤ (824161736650467/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9863 : ℕ)^5175*100000000000000000000^1024 ≤ 824161736650467^1024*100000^5175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9863 100000 824161736650467 100000000000000000000 5175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9863/100000 : ℝ)) (X := (824161736650467/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17219/100000 : ℝ) ^ (5175/1024 : ℝ) ≤ (13772250063888793/100000000000000000000 : ℝ) := by
    have hpowers : (17219/100000 : ℝ)^5175 ≤ (13772250063888793/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17219 : ℕ)^5175*100000000000000000000^1024 ≤ 13772250063888793^1024*100000^5175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17219 100000 13772250063888793 100000000000000000000 5175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17219/100000 : ℝ)) (X := (13772250063888793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000824161736650467/50000000000000000000 : ℝ) ≤ (400001304635423/400000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (50000824161736650467/50000000000000000000 : ℝ)^1024 ≤ (400001304635423/400000000000000 : ℝ)^5175 := by
      have hnat : (50000824161736650467 : ℕ)^1024*400000000000000^5175 ≤ 400001304635423^5175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000824161736650467 50000000000000000000 400001304635423 400000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001304635423/400000000000000 : ℝ)) (X := (50000824161736650467/50000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000729820590026963/5000000000000000000 : ℝ) ≤ (2500072202177621/2500000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (5000729820590026963/5000000000000000000 : ℝ)^1024 ≤ (2500072202177621/2500000000000000 : ℝ)^5175 := by
      have hnat : (5000729820590026963 : ℕ)^1024*2500000000000000^5175 ≤ 2500072202177621^5175*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000729820590026963 5000000000000000000 2500072202177621 2500000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500072202177621/2500000000000000 : ℝ)) (X := (5000729820590026963/5000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013772250063888793/50000000000000000000 : ℝ) ≤ (10000545001535393/10000000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (50013772250063888793/50000000000000000000 : ℝ)^1024 ≤ (10000545001535393/10000000000000000 : ℝ)^5175 := by
      have hnat : (50013772250063888793 : ℕ)^1024*10000000000000000^5175 ≤ 10000545001535393^5175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013772250063888793 50000000000000000000 10000545001535393 10000000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000545001535393/10000000000000000 : ℝ)) (X := (50013772250063888793/50000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(824161736650467/100000000000000000000 : ℝ) ≤ ((12259197710465022461/12260000000000000000 : ℝ)+2*(85397608303/245200000000000 : ℝ)*(9863/100000 : ℝ))^(5175/1024 : ℝ) := by
    rw [show (12259197710465022461/12260000000000000000 : ℝ)+2*(85397608303/245200000000000 : ℝ)*(9863/100000 : ℝ)=(400001304635423/400000000000000 : ℝ) by norm_num, show 1+2*(824161736650467/100000000000000000000 : ℝ)=(50000824161736650467/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13772250063888793/100000000000000000000 : ℝ)+(824161736650467/100000000000000000000 : ℝ) ≤ ((12259197710465022461/12260000000000000000 : ℝ)+(85397608303/245200000000000 : ℝ)*((17219/100000 : ℝ)+(9863/100000 : ℝ)))^(5175/1024 : ℝ) := by
    rw [show (12259197710465022461/12260000000000000000 : ℝ)+(85397608303/245200000000000 : ℝ)*((17219/100000 : ℝ)+(9863/100000 : ℝ))=(2500072202177621/2500000000000000 : ℝ) by norm_num, show 1+(13772250063888793/100000000000000000000 : ℝ)+(824161736650467/100000000000000000000 : ℝ)=(5000729820590026963/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13772250063888793/100000000000000000000 : ℝ) ≤ ((12259197710465022461/12260000000000000000 : ℝ)+2*(85397608303/245200000000000 : ℝ)*(17219/100000 : ℝ))^(5175/1024 : ℝ) := by
    rw [show (12259197710465022461/12260000000000000000 : ℝ)+2*(85397608303/245200000000000 : ℝ)*(17219/100000 : ℝ)=(10000545001535393/10000000000000000 : ℝ) by norm_num, show 1+2*(13772250063888793/100000000000000000000 : ℝ)=(50013772250063888793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12259197710465022461/12260000000000000000 : ℝ)*(X 1 0+X 2 0)+(85397608303/245200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (9863/100000 : ℝ)) (hi := (17219/100000 : ℝ)) (c := (12259197710465022461/12260000000000000000 : ℝ)) (alpha := (85397608303/245200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12259197710465022461/12260000000000000000 : ℝ)*(X 0 1+X 2 1)+(85397608303/245200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (9863/100000 : ℝ)) (hi := (17219/100000 : ℝ)) (c := (12259197710465022461/12260000000000000000 : ℝ)) (alpha := (85397608303/245200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12259197710465022461/12260000000000000000 : ℝ)*(X 0 2+X 1 2)+(85397608303/245200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (9863/100000 : ℝ)) (hi := (17219/100000 : ℝ)) (c := (12259197710465022461/12260000000000000000 : ℝ)) (alpha := (85397608303/245200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1468167809/10000000000 : ℝ)*X 0 0+(5479837401/10000000000 : ℝ)*X 0 1+(5136147593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668568569/1250000000 : ℝ)*X 1 0+(-1646612889/10000000000 : ℝ)*X 1 1+(2568073829/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348548749/10000000000 : ℝ)*X 2 0+(5136147489/10000000000 : ℝ)*X 2 1+(-1646612849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1031110737/2500000000 : ℝ)*X 0 0+(457714807/1250000000 : ℝ)*X 0 1+(4624129989/10000000000 : ℝ)*X 0 2+(1031110737/2500000000 : ℝ)*X 1 0+(457714807/1250000000 : ℝ)*X 1 1+(4624129989/10000000000 : ℝ)*X 1 2+(1031110737/2500000000 : ℝ)*X 2 0+(457714807/1250000000 : ℝ)*X 2 1+(4624129989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1468326541/10000000000 : ℝ)*X 0 0+(2569952077/5000000000 : ℝ)*X 0 1+(5476024841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256623391/10000000000 : ℝ)*X 1 0+(-653367619/5000000000 : ℝ)*X 1 1+(5476024841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256623391/10000000000 : ℝ)*X 2 0+(2738012421/5000000000 : ℝ)*X 2 1+(-1306735237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2062443951/5000000000 : ℝ)*X 0 0+(2306805191/5000000000 : ℝ)*X 0 1+(3672395029/10000000000 : ℝ)*X 0 2+(2062443951/5000000000 : ℝ)*X 1 0+(2306805191/5000000000 : ℝ)*X 1 1+(3672395029/10000000000 : ℝ)*X 1 2+(2062443951/5000000000 : ℝ)*X 2 0+(2306805191/5000000000 : ℝ)*X 2 1+(3672395029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1442469469650045306235743087/122600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1403521429/100000000000000 : ℝ)*(base19) + (1493580697/100000000000000 : ℝ)*(base23) + (2287741/25000000000000 : ℝ)*(lower2) + (30957833/12500000000000 : ℝ)*(upper3) + (137120117/50000000000000 : ℝ)*(upper5) + (394869302387363/20000000000000 : ℝ)*(major0) + (394869302387363/20000000000000 : ℝ)*(major1) + (394869302387363/20000000000000 : ℝ)*(major2) + (181850782687519/6250000000000 : ℝ)*(sp0) + (181851529647461/6250000000000 : ℝ)*(sp1) + (727406096075027/25000000000000 : ℝ)*(sp2) + (1039061591910307/100000000000000 : ℝ)*(sp3) + (26709761/200000000000 : ℝ)*(sp4) + (5161893963/100000000000000 : ℝ)*(sp7) + (103906675380427/10000000000000 : ℝ)*(f.failure) + (727406469470201/25000000000000 : ℝ)*(f.sum) + (7040951351163/2452000000000000000000000000 : ℝ)*base66 + (2989904741575389657/245200000000000000000000000000000 : ℝ)*base68 + (1824164740487389657/245200000000000000000000000000000 : ℝ)*base70 + (2814686648805789657/245200000000000000000000000000000 : ℝ)*base72 + (9252695485499/2452000000000000000000000000 : ℝ)*base74 + (3044861710834589657/245200000000000000000000000000000 : ℝ)*base76 + (1895564585373789657/245200000000000000000000000000000 : ℝ)*base78 + (3973024801416989657/245200000000000000000000000000000 : ℝ)*base80 + (2532906764827/2452000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5879093/500000000000000000000 : ℝ)*base89 + (5879093/500000000000000000000 : ℝ)*base91 + (5879093/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1402126510413963188076438351/153250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (258096297/20000000000000 : ℝ)*(base19) + (1391176367/100000000000000 : ℝ)*(base23) + (194089489/50000000000000 : ℝ)*(lower1) + (195631637/100000000000000 : ℝ)*(upper3) + (22474327/50000000000000 : ℝ)*(lower4) + (47652689/25000000000000 : ℝ)*(upper5) + (1009390459021503/50000000000000 : ℝ)*(major0) + (1009390459021503/50000000000000 : ℝ)*(major1) + (1009390459021503/50000000000000 : ℝ)*(major2) + (868406233/100000000000000 : ℝ)*(sp2) + (743777416351599/25000000000000 : ℝ)*(sp4) + (2975108374924911/100000000000000 : ℝ)*(sp5) + (595021481164759/20000000000000 : ℝ)*(sp6) + (16600810401621/1562500000000 : ℝ)*(sp7) + (16600810401621/1562500000000 : ℝ)*(f.failure) + (743777416351599/25000000000000 : ℝ)*(f.sum) + (32622667876649/6130000000000000000000000000 : ℝ)*base65 + (3417612921251428883/613000000000000000000000000000000 : ℝ)*base67 + (1952890847791428883/613000000000000000000000000000000 : ℝ)*base69 + (14959569794790428883/613000000000000000000000000000000 : ℝ)*base71 + (3792005668709/6130000000000000000000000000 : ℝ)*base73 + (17227530425703571117/613000000000000000000000000000000 : ℝ)*base76 + (4829040972097428883/613000000000000000000000000000000 : ℝ)*base77 + (6451322125992428883/613000000000000000000000000000000 : ℝ)*base79 + (31645009550689/6130000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (502161/78125000000000000000 : ℝ)*base90 + (502161/78125000000000000000 : ℝ)*base92 + (502161/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1695_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9879/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (43/250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1695_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1695_s4_0 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1468178367/10000000000 : ℝ)*x 0 + (1369949351/2500000000 : ℝ)*x 1 + (1284045119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1468178367/10000000000 : ℝ)^5183 ≤ (286074356321/3125000000000 : ℝ)^4159 := by
    have hnat : (1468178367 : ℕ)^5183*3125000000000^4159 ≤ 286074356321^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468178367 10000000000 286074356321 3125000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369949351/2500000000 : ℝ)^5183 ≤ (23627344993599/50000000000000 : ℝ)^4159 := by
    have hnat : (1369949351 : ℕ)^5183*50000000000000^4159 ≤ 23627344993599^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369949351 2500000000 23627344993599 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284045119/2500000000 : ℝ)^5183 ≤ (43590930593453/100000000000000 : ℝ)^4159 := by
    have hnat : (1284045119 : ℕ)^5183*100000000000000^4159 ≤ 43590930593453^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284045119 2500000000 43590930593453 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1468178367/10000000000 : ℝ), (1369949351/2500000000 : ℝ), (1284045119/2500000000 : ℝ)] ![(286074356321/3125000000000 : ℝ), (23627344993599/50000000000000 : ℝ), (43590930593453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1468178367/10000000000 : ℝ)|^5183 ≤ (286074356321/3125000000000 : ℝ)^4159
        have hw : |(-1468178367/10000000000 : ℝ)|=(1468178367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369949351/2500000000 : ℝ)|^5183 ≤ (23627344993599/50000000000000 : ℝ)^4159
        have hw : |(1369949351/2500000000 : ℝ)|=(1369949351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284045119/2500000000 : ℝ)|^5183 ≤ (43590930593453/100000000000000 : ℝ)^4159
        have hw : |(1284045119/2500000000 : ℝ)|=(1284045119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_1 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348538759/10000000000 : ℝ)*x 0 + (-823292333/5000000000 : ℝ)*x 1 + (2568089439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348538759/10000000000 : ℝ)^5183 ≤ (45848285408837/100000000000000 : ℝ)^4159 := by
    have hnat : (5348538759 : ℕ)^5183*100000000000000^4159 ≤ 45848285408837^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348538759 10000000000 45848285408837 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823292333/5000000000 : ℝ)^5183 ≤ (2640200221209/25000000000000 : ℝ)^4159 := by
    have hnat : (823292333 : ℕ)^5183*25000000000000^4159 ≤ 2640200221209^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823292333 5000000000 2640200221209 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568089439/5000000000 : ℝ)^5183 ≤ (21795456845983/50000000000000 : ℝ)^4159 := by
    have hnat : (2568089439 : ℕ)^5183*50000000000000^4159 ≤ 21795456845983^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568089439 5000000000 21795456845983 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348538759/10000000000 : ℝ), (-823292333/5000000000 : ℝ), (2568089439/5000000000 : ℝ)] ![(45848285408837/100000000000000 : ℝ), (2640200221209/25000000000000 : ℝ), (21795456845983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348538759/10000000000 : ℝ)|^5183 ≤ (45848285408837/100000000000000 : ℝ)^4159
        have hw : |(5348538759/10000000000 : ℝ)|=(5348538759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-823292333/5000000000 : ℝ)|^5183 ≤ (2640200221209/25000000000000 : ℝ)^4159
        have hw : |(-823292333/5000000000 : ℝ)|=(823292333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568089439/5000000000 : ℝ)|^5183 ≤ (21795456845983/50000000000000 : ℝ)^4159
        have hw : |(2568089439/5000000000 : ℝ)|=(2568089439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_2 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337134257/2500000000 : ℝ)*x 0 + (205447201/400000000 : ℝ)*x 1 + (-1646585461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337134257/2500000000 : ℝ)^5183 ≤ (22924133458559/50000000000000 : ℝ)^4159 := by
    have hnat : (1337134257 : ℕ)^5183*50000000000000^4159 ≤ 22924133458559^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337134257 2500000000 22924133458559 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205447201/400000000 : ℝ)^5183 ≤ (5448865727923/12500000000000 : ℝ)^4159 := by
    have hnat : (205447201 : ℕ)^5183*12500000000000^4159 ≤ 5448865727923^4159*400000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205447201 400000000 5448865727923 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1646585461/10000000000 : ℝ)^5183 ≤ (5280403619601/50000000000000 : ℝ)^4159 := by
    have hnat : (1646585461 : ℕ)^5183*50000000000000^4159 ≤ 5280403619601^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646585461 10000000000 5280403619601 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337134257/2500000000 : ℝ), (205447201/400000000 : ℝ), (-1646585461/10000000000 : ℝ)] ![(22924133458559/50000000000000 : ℝ), (5448865727923/12500000000000 : ℝ), (5280403619601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337134257/2500000000 : ℝ)|^5183 ≤ (22924133458559/50000000000000 : ℝ)^4159
        have hw : |(1337134257/2500000000 : ℝ)|=(1337134257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205447201/400000000 : ℝ)|^5183 ≤ (5448865727923/12500000000000 : ℝ)^4159
        have hw : |(205447201/400000000 : ℝ)|=(205447201/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1646585461/10000000000 : ℝ)|^5183 ≤ (5280403619601/50000000000000 : ℝ)^4159
        have hw : |(-1646585461/10000000000 : ℝ)|=(1646585461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_3 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4124449737/10000000000 : ℝ)*x 0 + (3661819347/10000000000 : ℝ)*x 1 + (462402813/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124449737/10000000000 : ℝ)^5183 ≤ (33163786900597/100000000000000 : ℝ)^4159 := by
    have hnat : (4124449737 : ℕ)^5183*100000000000000^4159 ≤ 33163786900597^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124449737 10000000000 33163786900597 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3661819347/10000000000 : ℝ)^5183 ≤ (14296950509191/50000000000000 : ℝ)^4159 := by
    have hnat : (3661819347 : ℕ)^5183*50000000000000^4159 ≤ 14296950509191^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661819347 10000000000 14296950509191 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (462402813/1000000000 : ℝ)^5183 ≤ (38242312061227/100000000000000 : ℝ)^4159 := by
    have hnat : (462402813 : ℕ)^5183*100000000000000^4159 ≤ 38242312061227^4159*1000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462402813 1000000000 38242312061227 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124449737/10000000000 : ℝ), (3661819347/10000000000 : ℝ), (462402813/1000000000 : ℝ)] ![(33163786900597/100000000000000 : ℝ), (14296950509191/50000000000000 : ℝ), (38242312061227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124449737/10000000000 : ℝ)|^5183 ≤ (33163786900597/100000000000000 : ℝ)^4159
        have hw : |(4124449737/10000000000 : ℝ)|=(4124449737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3661819347/10000000000 : ℝ)|^5183 ≤ (14296950509191/50000000000000 : ℝ)^4159
        have hw : |(3661819347/10000000000 : ℝ)|=(3661819347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(462402813/1000000000 : ℝ)|^5183 ≤ (38242312061227/100000000000000 : ℝ)^4159
        have hw : |(462402813/1000000000 : ℝ)|=(462402813/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_4 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-183542121/1250000000 : ℝ)*x 0 + (1027987001/2000000000 : ℝ)*x 1 + (5475986927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183542121/1250000000 : ℝ)^5183 ≤ (9155611809033/100000000000000 : ℝ)^4159 := by
    have hnat : (183542121 : ℕ)^5183*100000000000000^4159 ≤ 9155611809033^4159*1250000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183542121 1250000000 9155611809033 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027987001/2000000000 : ℝ)^5183 ≤ (43630644507359/100000000000000 : ℝ)^4159 := by
    have hnat : (1027987001 : ℕ)^5183*100000000000000^4159 ≤ 43630644507359^4159*2000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027987001 2000000000 43630644507359 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475986927/10000000000 : ℝ)^5183 ≤ (5901717958549/12500000000000 : ℝ)^4159 := by
    have hnat : (5475986927 : ℕ)^5183*12500000000000^4159 ≤ 5901717958549^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475986927 10000000000 5901717958549 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183542121/1250000000 : ℝ), (1027987001/2000000000 : ℝ), (5475986927/10000000000 : ℝ)] ![(9155611809033/100000000000000 : ℝ), (43630644507359/100000000000000 : ℝ), (5901717958549/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183542121/1250000000 : ℝ)|^5183 ≤ (9155611809033/100000000000000 : ℝ)^4159
        have hw : |(-183542121/1250000000 : ℝ)|=(183542121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027987001/2000000000 : ℝ)|^5183 ≤ (43630644507359/100000000000000 : ℝ)^4159
        have hw : |(1027987001/2000000000 : ℝ)|=(1027987001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475986927/10000000000 : ℝ)|^5183 ≤ (5901717958549/12500000000000 : ℝ)^4159
        have hw : |(5475986927/10000000000 : ℝ)|=(5475986927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_5 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256631787/10000000000 : ℝ)*x 0 + (-653388681/5000000000 : ℝ)*x 1 + (5475986927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256631787/10000000000 : ℝ)^5183 ≤ (44868558561341/100000000000000 : ℝ)^4159 := by
    have hnat : (5256631787 : ℕ)^5183*100000000000000^4159 ≤ 44868558561341^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256631787 10000000000 44868558561341 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653388681/5000000000 : ℝ)^5183 ≤ (3958848877059/50000000000000 : ℝ)^4159 := by
    have hnat : (653388681 : ℕ)^5183*50000000000000^4159 ≤ 3958848877059^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653388681 5000000000 3958848877059 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475986927/10000000000 : ℝ)^5183 ≤ (5901717958549/12500000000000 : ℝ)^4159 := by
    have hnat : (5475986927 : ℕ)^5183*12500000000000^4159 ≤ 5901717958549^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475986927 10000000000 5901717958549 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256631787/10000000000 : ℝ), (-653388681/5000000000 : ℝ), (5475986927/10000000000 : ℝ)] ![(44868558561341/100000000000000 : ℝ), (3958848877059/50000000000000 : ℝ), (5901717958549/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256631787/10000000000 : ℝ)|^5183 ≤ (44868558561341/100000000000000 : ℝ)^4159
        have hw : |(5256631787/10000000000 : ℝ)|=(5256631787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-653388681/5000000000 : ℝ)|^5183 ≤ (3958848877059/50000000000000 : ℝ)^4159
        have hw : |(-653388681/5000000000 : ℝ)|=(653388681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475986927/10000000000 : ℝ)|^5183 ≤ (5901717958549/12500000000000 : ℝ)^4159
        have hw : |(5475986927/10000000000 : ℝ)|=(5475986927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_6 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256631773/10000000000 : ℝ)*x 0 + (5475986947/10000000000 : ℝ)*x 1 + (-1306777353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256631773/10000000000 : ℝ)^5183 ≤ (2243427920621/5000000000000 : ℝ)^4159 := by
    have hnat : (5256631773 : ℕ)^5183*5000000000000^4159 ≤ 2243427920621^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256631773 10000000000 2243427920621 5000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475986947/10000000000 : ℝ)^5183 ≤ (5901717985411/12500000000000 : ℝ)^4159 := by
    have hnat : (5475986947 : ℕ)^5183*12500000000000^4159 ≤ 5901717985411^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475986947 10000000000 5901717985411 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306777353/10000000000 : ℝ)^5183 ≤ (3958848843081/50000000000000 : ℝ)^4159 := by
    have hnat : (1306777353 : ℕ)^5183*50000000000000^4159 ≤ 3958848843081^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306777353 10000000000 3958848843081 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256631773/10000000000 : ℝ), (5475986947/10000000000 : ℝ), (-1306777353/10000000000 : ℝ)] ![(2243427920621/5000000000000 : ℝ), (5901717985411/12500000000000 : ℝ), (3958848843081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256631773/10000000000 : ℝ)|^5183 ≤ (2243427920621/5000000000000 : ℝ)^4159
        have hw : |(5256631773/10000000000 : ℝ)|=(5256631773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475986947/10000000000 : ℝ)|^5183 ≤ (5901717985411/12500000000000 : ℝ)^4159
        have hw : |(5475986947/10000000000 : ℝ)|=(5475986947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306777353/10000000000 : ℝ)|^5183 ≤ (3958848843081/50000000000000 : ℝ)^4159
        have hw : |(-1306777353/10000000000 : ℝ)|=(1306777353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_s4_7 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4124894703/10000000000 : ℝ)*x 0 + (2306756697/5000000000 : ℝ)*x 1 + (1836245311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4124894703/10000000000 : ℝ)^5183 ≤ (4146030718981/12500000000000 : ℝ)^4159 := by
    have hnat : (4124894703 : ℕ)^5183*12500000000000^4159 ≤ 4146030718981^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124894703 10000000000 4146030718981 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306756697/5000000000 : ℝ)^5183 ≤ (4766746387829/12500000000000 : ℝ)^4159 := by
    have hnat : (2306756697 : ℕ)^5183*12500000000000^4159 ≤ 4766746387829^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306756697 5000000000 4766746387829 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1836245311/5000000000 : ℝ)^5183 ≤ (14348891563839/50000000000000 : ℝ)^4159 := by
    have hnat : (1836245311 : ℕ)^5183*50000000000000^4159 ≤ 14348891563839^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836245311 5000000000 14348891563839 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4124894703/10000000000 : ℝ), (2306756697/5000000000 : ℝ), (1836245311/5000000000 : ℝ)] ![(4146030718981/12500000000000 : ℝ), (4766746387829/12500000000000 : ℝ), (14348891563839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4124894703/10000000000 : ℝ)|^5183 ≤ (4146030718981/12500000000000 : ℝ)^4159
        have hw : |(4124894703/10000000000 : ℝ)|=(4124894703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2306756697/5000000000 : ℝ)|^5183 ≤ (4766746387829/12500000000000 : ℝ)^4159
        have hw : |(2306756697/5000000000 : ℝ)|=(2306756697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1836245311/5000000000 : ℝ)|^5183 ≤ (14348891563839/50000000000000 : ℝ)^4159
        have hw : |(1836245311/5000000000 : ℝ)|=(1836245311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1695_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (43/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9879/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (247/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17199/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (43/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9879/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (43/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9879/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (43/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9879/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (43/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9879/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (43/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9879/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (43/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9879/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9879/100000 : ℝ) ^ (5175/1024 : ℝ) ≤ (103867584544201/12500000000000000000 : ℝ) := by
    have hpowers : (9879/100000 : ℝ)^5175 ≤ (103867584544201/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9879 : ℕ)^5175*12500000000000000000^1024 ≤ 103867584544201^1024*100000^5175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9879 100000 103867584544201 12500000000000000000 5175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9879/100000 : ℝ)) (X := (103867584544201/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (43/250 : ℝ) ^ (5175/1024 : ℝ) ≤ (6847810838928347/50000000000000000000 : ℝ) := by
    have hpowers : (43/250 : ℝ)^5175 ≤ (6847810838928347/50000000000000000000 : ℝ)^1024 := by
      have hnat : (43 : ℕ)^5175*50000000000000000000^1024 ≤ 6847810838928347^1024*250^5175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43 250 6847810838928347 50000000000000000000 5175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43/250 : ℝ)) (X := (6847810838928347/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250103867584544201/6250000000000000000 : ℝ) ≤ (5000016442078867/5000000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (6250103867584544201/6250000000000000000 : ℝ)^1024 ≤ (5000016442078867/5000000000000000 : ℝ)^5175 := by
      have hnat : (6250103867584544201 : ℕ)^1024*5000000000000000^5175 ≤ 5000016442078867^5175*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250103867584544201 6250000000000000000 5000016442078867 5000000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000016442078867/5000000000000000 : ℝ)) (X := (6250103867584544201/6250000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007263281177105151/50000000000000000000 : ℝ) ≤ (5000143713365099/5000000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (50007263281177105151/50000000000000000000 : ℝ)^1024 ≤ (5000143713365099/5000000000000000 : ℝ)^5175 := by
      have hnat : (50007263281177105151 : ℕ)^1024*5000000000000000^5175 ≤ 5000143713365099^5175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007263281177105151 50000000000000000000 5000143713365099 5000000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000143713365099/5000000000000000 : ℝ)) (X := (50007263281177105151/50000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006847810838928347/25000000000000000000 : ℝ) ≤ (5000270984651331/5000000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (25006847810838928347/25000000000000000000 : ℝ)^1024 ≤ (5000270984651331/5000000000000000 : ℝ)^5175 := by
      have hnat : (25006847810838928347 : ℕ)^1024*5000000000000000^5175 ≤ 5000270984651331^5175*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006847810838928347 25000000000000000000 5000270984651331 5000000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000270984651331/5000000000000000 : ℝ)) (X := (25006847810838928347/25000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(103867584544201/12500000000000000000 : ℝ) ≤ ((36602605746386013451/36605000000000000000 : ℝ)+2*(15908910779/45756250000000 : ℝ)*(9879/100000 : ℝ))^(5175/1024 : ℝ) := by
    rw [show (36602605746386013451/36605000000000000000 : ℝ)+2*(15908910779/45756250000000 : ℝ)*(9879/100000 : ℝ)=(5000016442078867/5000000000000000 : ℝ) by norm_num, show 1+2*(103867584544201/12500000000000000000 : ℝ)=(6250103867584544201/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6847810838928347/50000000000000000000 : ℝ)+(103867584544201/12500000000000000000 : ℝ) ≤ ((36602605746386013451/36605000000000000000 : ℝ)+(15908910779/45756250000000 : ℝ)*((43/250 : ℝ)+(9879/100000 : ℝ)))^(5175/1024 : ℝ) := by
    rw [show (36602605746386013451/36605000000000000000 : ℝ)+(15908910779/45756250000000 : ℝ)*((43/250 : ℝ)+(9879/100000 : ℝ))=(5000143713365099/5000000000000000 : ℝ) by norm_num, show 1+(6847810838928347/50000000000000000000 : ℝ)+(103867584544201/12500000000000000000 : ℝ)=(50007263281177105151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6847810838928347/50000000000000000000 : ℝ) ≤ ((36602605746386013451/36605000000000000000 : ℝ)+2*(15908910779/45756250000000 : ℝ)*(43/250 : ℝ))^(5175/1024 : ℝ) := by
    rw [show (36602605746386013451/36605000000000000000 : ℝ)+2*(15908910779/45756250000000 : ℝ)*(43/250 : ℝ)=(5000270984651331/5000000000000000 : ℝ) by norm_num, show 1+2*(6847810838928347/50000000000000000000 : ℝ)=(25006847810838928347/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36602605746386013451/36605000000000000000 : ℝ)*(X 1 0+X 2 0)+(15908910779/45756250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (9879/100000 : ℝ)) (hi := (43/250 : ℝ)) (c := (36602605746386013451/36605000000000000000 : ℝ)) (alpha := (15908910779/45756250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36602605746386013451/36605000000000000000 : ℝ)*(X 0 1+X 2 1)+(15908910779/45756250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (9879/100000 : ℝ)) (hi := (43/250 : ℝ)) (c := (36602605746386013451/36605000000000000000 : ℝ)) (alpha := (15908910779/45756250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36602605746386013451/36605000000000000000 : ℝ)*(X 0 2+X 1 2)+(15908910779/45756250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (9879/100000 : ℝ)) (hi := (43/250 : ℝ)) (c := (36602605746386013451/36605000000000000000 : ℝ)) (alpha := (15908910779/45756250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1468178367/10000000000 : ℝ)*X 0 0+(1369949351/2500000000 : ℝ)*X 0 1+(1284045119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348538759/10000000000 : ℝ)*X 1 0+(-823292333/5000000000 : ℝ)*X 1 1+(2568089439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337134257/2500000000 : ℝ)*X 2 0+(205447201/400000000 : ℝ)*X 2 1+(-1646585461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4124449737/10000000000 : ℝ)*X 0 0+(3661819347/10000000000 : ℝ)*X 0 1+(462402813/1000000000 : ℝ)*X 0 2+(4124449737/10000000000 : ℝ)*X 1 0+(3661819347/10000000000 : ℝ)*X 1 1+(462402813/1000000000 : ℝ)*X 1 2+(4124449737/10000000000 : ℝ)*X 2 0+(3661819347/10000000000 : ℝ)*X 2 1+(462402813/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-183542121/1250000000 : ℝ)*X 0 0+(1027987001/2000000000 : ℝ)*X 0 1+(5475986927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256631787/10000000000 : ℝ)*X 1 0+(-653388681/5000000000 : ℝ)*X 1 1+(5475986927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256631773/10000000000 : ℝ)*X 2 0+(5475986947/10000000000 : ℝ)*X 2 1+(-1306777353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4124894703/10000000000 : ℝ)*X 0 0+(2306756697/5000000000 : ℝ)*X 0 1+(1836245311/5000000000 : ℝ)*X 0 2+(4124894703/10000000000 : ℝ)*X 1 0+(2306756697/5000000000 : ℝ)*X 1 1+(1836245311/5000000000 : ℝ)*X 1 2+(4124894703/10000000000 : ℝ)*X 2 0+(2306756697/5000000000 : ℝ)*X 2 1+(1836245311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (302722207245157282235103/36605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1498262443/100000000000000 : ℝ)*(base19) + (552524581/100000000000000 : ℝ)*(base23) + (48261899/100000000000000 : ℝ)*(upper2) + (4119909/1562500000000 : ℝ)*(upper3) + (8327497/10000000000000 : ℝ)*(upper5) + (1974752633240153/100000000000000 : ℝ)*(major0) + (1974752633240153/100000000000000 : ℝ)*(major1) + (1974752633240153/100000000000000 : ℝ)*(major2) + (1455112250956431/50000000000000 : ℝ)*(sp0) + (145511150182521/5000000000000 : ℝ)*(sp1) + (1455109236347221/50000000000000 : ℝ)*(sp2) + (259819516863827/25000000000000 : ℝ)*(sp3) + (5476693839/100000000000000 : ℝ)*(sp6) + (302680813/12500000000000 : ℝ)*(sp7) + (1039280488901811/100000000000000 : ℝ)*(f.failure) + (1455112250956431/50000000000000 : ℝ)*(f.sum) + (17529438149589/18302500000000000000000000000 : ℝ)*base66 + (9874987952229101997/3660500000000000000000000000000000 : ℝ)*base68 + (7660076728800898003/3660500000000000000000000000000000 : ℝ)*base69 + (6109879603503101997/3660500000000000000000000000000000 : ℝ)*base72 + (65268130984467/9151250000000000000000000000 : ℝ)*base74 + (20314000344103101997/3660500000000000000000000000000000 : ℝ)*base76 + (11493771855045398003/3660500000000000000000000000000000 : ℝ)*base77 + (20190783806503398003/3660500000000000000000000000000000 : ℝ)*base79 + (47215310594403/36605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19470451/5000000000000000000000 : ℝ)*base90 + (19470451/5000000000000000000000 : ℝ)*base92 + (19470451/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1303108143846763504958795157/183025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1005703293/100000000000000 : ℝ)*(base19) + (1074497681/100000000000000 : ℝ)*(base23) + (60820977/20000000000000 : ℝ)*(lower1) + (150876597/100000000000000 : ℝ)*(upper3) + (8494633/25000000000000 : ℝ)*(lower4) + (148977709/100000000000000 : ℝ)*(upper5) + (201919578341331/10000000000000 : ℝ)*(major0) + (201919578341331/10000000000000 : ℝ)*(major1) + (201919578341331/10000000000000 : ℝ)*(major2) + (690945523/100000000000000 : ℝ)*(sp2) + (2975721126835893/100000000000000 : ℝ)*(sp4) + (14878600605663/500000000000 : ℝ)*(sp5) + (185982460087043/6250000000000 : ℝ)*(sp6) + (42506808106513/4000000000000 : ℝ)*(sp7) + (42506808106513/4000000000000 : ℝ)*(f.failure) + (2975721126835893/100000000000000 : ℝ)*(f.sum) + (17365477297703/7321000000000000000000000000 : ℝ)*base66 + (727161807398693281/366050000000000000000000000000000 : ℝ)*base67 + (3149978874890393281/366050000000000000000000000000000 : ℝ)*base69 + (278179751144306719/366050000000000000000000000000000 : ℝ)*base72 + (20933895149841/3660500000000000000000000000 : ℝ)*base74 + (6034636358953056719/366050000000000000000000000000000 : ℝ)*base76 + (2736225428504293281/366050000000000000000000000000000 : ℝ)*base77 + (1640863917605393281/366050000000000000000000000000000 : ℝ)*base79 + (615894221263/292840000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (408367/200000000000000000000 : ℝ)*base89 + (408367/200000000000000000000 : ℝ)*base91 + (408367/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1695_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (43/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9879/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (247/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17199/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1695_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1695_box_0 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1137472507/10000000000 : ℝ)*x 0 + (271265221/500000000 : ℝ)*x 1 + (2712652259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1137472507/10000000000 : ℝ)^5183 ≤ (3330207246409/50000000000000 : ℝ)^4159 := by
    have hnat : (1137472507 : ℕ)^5183*50000000000000^4159 ≤ 3330207246409^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137472507 10000000000 3330207246409 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271265221/500000000 : ℝ)^5183 ≤ (23334896109637/50000000000000 : ℝ)^4159 := by
    have hnat : (271265221 : ℕ)^5183*50000000000000^4159 ≤ 23334896109637^4159*500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271265221 500000000 23334896109637 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712652259/5000000000 : ℝ)^5183 ≤ (1458431039683/3125000000000 : ℝ)^4159 := by
    have hnat : (2712652259 : ℕ)^5183*3125000000000^4159 ≤ 1458431039683^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712652259 5000000000 1458431039683 3125000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1137472507/10000000000 : ℝ), (271265221/500000000 : ℝ), (2712652259/5000000000 : ℝ)] ![(3330207246409/50000000000000 : ℝ), (23334896109637/50000000000000 : ℝ), (1458431039683/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1137472507/10000000000 : ℝ)|^5183 ≤ (3330207246409/50000000000000 : ℝ)^4159
        have hw : |(-1137472507/10000000000 : ℝ)|=(1137472507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271265221/500000000 : ℝ)|^5183 ≤ (23334896109637/50000000000000 : ℝ)^4159
        have hw : |(271265221/500000000 : ℝ)|=(271265221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712652259/5000000000 : ℝ)|^5183 ≤ (1458431039683/3125000000000 : ℝ)^4159
        have hw : |(2712652259/5000000000 : ℝ)|=(2712652259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_1 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612973333/5000000000 : ℝ)*x 0 + (-71040707/500000000 : ℝ)*x 1 + (5425304679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612973333/5000000000 : ℝ)^5183 ≤ (44542390055751/100000000000000 : ℝ)^4159 := by
    have hnat : (2612973333 : ℕ)^5183*100000000000000^4159 ≤ 44542390055751^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612973333 5000000000 44542390055751 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71040707/500000000 : ℝ)^5183 ≤ (8787814936063/100000000000000 : ℝ)^4159 := by
    have hnat : (71040707 : ℕ)^5183*100000000000000^4159 ≤ 8787814936063^4159*500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71040707 500000000 8787814936063 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425304679/10000000000 : ℝ)^5183 ≤ (46669794995813/100000000000000 : ℝ)^4159 := by
    have hnat : (5425304679 : ℕ)^5183*100000000000000^4159 ≤ 46669794995813^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425304679 10000000000 46669794995813 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612973333/5000000000 : ℝ), (-71040707/500000000 : ℝ), (5425304679/10000000000 : ℝ)] ![(44542390055751/100000000000000 : ℝ), (8787814936063/100000000000000 : ℝ), (46669794995813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612973333/5000000000 : ℝ)|^5183 ≤ (44542390055751/100000000000000 : ℝ)^4159
        have hw : |(2612973333/5000000000 : ℝ)|=(2612973333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71040707/500000000 : ℝ)|^5183 ≤ (8787814936063/100000000000000 : ℝ)^4159
        have hw : |(-71040707/500000000 : ℝ)|=(71040707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425304679/10000000000 : ℝ)|^5183 ≤ (46669794995813/100000000000000 : ℝ)^4159
        have hw : |(5425304679/10000000000 : ℝ)|=(5425304679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_2 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612973233/5000000000 : ℝ)*x 0 + (542530493/1000000000 : ℝ)*x 1 + (-710407033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612973233/5000000000 : ℝ)^5183 ≤ (22271193965689/50000000000000 : ℝ)^4159 := by
    have hnat : (2612973233 : ℕ)^5183*50000000000000^4159 ≤ 22271193965689^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612973233 5000000000 22271193965689 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542530493/1000000000 : ℝ)^5183 ≤ (46669797686591/100000000000000 : ℝ)^4159 := by
    have hnat : (542530493 : ℕ)^5183*100000000000000^4159 ≤ 46669797686591^4159*1000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542530493 1000000000 46669797686591 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710407033/5000000000 : ℝ)^5183 ≤ (4393907182839/50000000000000 : ℝ)^4159 := by
    have hnat : (710407033 : ℕ)^5183*50000000000000^4159 ≤ 4393907182839^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710407033 5000000000 4393907182839 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612973233/5000000000 : ℝ), (542530493/1000000000 : ℝ), (-710407033/5000000000 : ℝ)] ![(22271193965689/50000000000000 : ℝ), (46669797686591/100000000000000 : ℝ), (4393907182839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612973233/5000000000 : ℝ)|^5183 ≤ (22271193965689/50000000000000 : ℝ)^4159
        have hw : |(2612973233/5000000000 : ℝ)|=(2612973233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542530493/1000000000 : ℝ)|^5183 ≤ (46669797686591/100000000000000 : ℝ)^4159
        have hw : |(542530493/1000000000 : ℝ)|=(542530493/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-710407033/5000000000 : ℝ)|^5183 ≤ (4393907182839/50000000000000 : ℝ)^4159
        have hw : |(-710407033/5000000000 : ℝ)|=(710407033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_3 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4508081021/10000000000 : ℝ)*x 0 + (158200029/400000000 : ℝ)*x 1 + (3955001017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4508081021/10000000000 : ℝ)^5183 ≤ (37051002496007/100000000000000 : ℝ)^4159 := by
    have hnat : (4508081021 : ℕ)^5183*100000000000000^4159 ≤ 37051002496007^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508081021 10000000000 37051002496007 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158200029/400000000 : ℝ)^5183 ≤ (31474497295777/100000000000000 : ℝ)^4159 := by
    have hnat : (158200029 : ℕ)^5183*100000000000000^4159 ≤ 31474497295777^4159*400000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158200029 400000000 31474497295777 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3955001017/10000000000 : ℝ)^5183 ≤ (15737250095851/50000000000000 : ℝ)^4159 := by
    have hnat : (3955001017 : ℕ)^5183*50000000000000^4159 ≤ 15737250095851^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3955001017 10000000000 15737250095851 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4508081021/10000000000 : ℝ), (158200029/400000000 : ℝ), (3955001017/10000000000 : ℝ)] ![(37051002496007/100000000000000 : ℝ), (31474497295777/100000000000000 : ℝ), (15737250095851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4508081021/10000000000 : ℝ)|^5183 ≤ (37051002496007/100000000000000 : ℝ)^4159
        have hw : |(4508081021/10000000000 : ℝ)|=(4508081021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158200029/400000000 : ℝ)|^5183 ≤ (31474497295777/100000000000000 : ℝ)^4159
        have hw : |(158200029/400000000 : ℝ)|=(158200029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3955001017/10000000000 : ℝ)|^5183 ≤ (15737250095851/50000000000000 : ℝ)^4159
        have hw : |(3955001017/10000000000 : ℝ)|=(3955001017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_4 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-909878749/5000000000 : ℝ)*x 0 + (2588297177/5000000000 : ℝ)*x 1 + (258829723/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (909878749/5000000000 : ℝ)^5183 ≤ (11962424286139/100000000000000 : ℝ)^4159 := by
    have hnat : (909878749 : ℕ)^5183*100000000000000^4159 ≤ 11962424286139^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909878749 5000000000 11962424286139 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588297177/5000000000 : ℝ)^5183 ≤ (220093936439/500000000000 : ℝ)^4159 := by
    have hnat : (2588297177 : ℕ)^5183*500000000000^4159 ≤ 220093936439^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588297177 5000000000 220093936439 500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258829723/500000000 : ℝ)^5183 ≤ (44018788411091/100000000000000 : ℝ)^4159 := by
    have hnat : (258829723 : ℕ)^5183*100000000000000^4159 ≤ 44018788411091^4159*500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258829723 500000000 44018788411091 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-909878749/5000000000 : ℝ), (2588297177/5000000000 : ℝ), (258829723/500000000 : ℝ)] ![(11962424286139/100000000000000 : ℝ), (220093936439/500000000000 : ℝ), (44018788411091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-909878749/5000000000 : ℝ)|^5183 ≤ (11962424286139/100000000000000 : ℝ)^4159
        have hw : |(-909878749/5000000000 : ℝ)|=(909878749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588297177/5000000000 : ℝ)|^5183 ≤ (220093936439/500000000000 : ℝ)^4159
        have hw : |(2588297177/5000000000 : ℝ)|=(2588297177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258829723/500000000 : ℝ)|^5183 ≤ (44018788411091/100000000000000 : ℝ)^4159
        have hw : |(258829723/500000000 : ℝ)|=(258829723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_5 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079046747/2000000000 : ℝ)*x 0 + (-1529534041/10000000000 : ℝ)*x 1 + (2588297221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079046747/2000000000 : ℝ)^5183 ≤ (46347647872877/100000000000000 : ℝ)^4159 := by
    have hnat : (1079046747 : ℕ)^5183*100000000000000^4159 ≤ 46347647872877^4159*2000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079046747 2000000000 46347647872877 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529534041/10000000000 : ℝ)^5183 ≤ (4816781947267/50000000000000 : ℝ)^4159 := by
    have hnat : (1529534041 : ℕ)^5183*50000000000000^4159 ≤ 4816781947267^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529534041 10000000000 4816781947267 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588297221/5000000000 : ℝ)^5183 ≤ (5502348527543/12500000000000 : ℝ)^4159 := by
    have hnat : (2588297221 : ℕ)^5183*12500000000000^4159 ≤ 5502348527543^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588297221 5000000000 5502348527543 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079046747/2000000000 : ℝ), (-1529534041/10000000000 : ℝ), (2588297221/5000000000 : ℝ)] ![(46347647872877/100000000000000 : ℝ), (4816781947267/50000000000000 : ℝ), (5502348527543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079046747/2000000000 : ℝ)|^5183 ≤ (46347647872877/100000000000000 : ℝ)^4159
        have hw : |(1079046747/2000000000 : ℝ)|=(1079046747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1529534041/10000000000 : ℝ)|^5183 ≤ (4816781947267/50000000000000 : ℝ)^4159
        have hw : |(-1529534041/10000000000 : ℝ)|=(1529534041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588297221/5000000000 : ℝ)|^5183 ≤ (5502348527543/12500000000000 : ℝ)^4159
        have hw : |(2588297221/5000000000 : ℝ)|=(2588297221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_6 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53952337/100000000 : ℝ)*x 0 + (5176594443/10000000000 : ℝ)*x 1 + (-764767043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53952337/100000000 : ℝ)^5183 ≤ (23173823749091/50000000000000 : ℝ)^4159 := by
    have hnat : (53952337 : ℕ)^5183*50000000000000^4159 ≤ 23173823749091^4159*100000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53952337 100000000 23173823749091 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176594443/10000000000 : ℝ)^5183 ≤ (44018788230941/100000000000000 : ℝ)^4159 := by
    have hnat : (5176594443 : ℕ)^5183*100000000000000^4159 ≤ 44018788230941^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176594443 10000000000 44018788230941 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (764767043/5000000000 : ℝ)^5183 ≤ (9633564247743/100000000000000 : ℝ)^4159 := by
    have hnat : (764767043 : ℕ)^5183*100000000000000^4159 ≤ 9633564247743^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764767043 5000000000 9633564247743 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53952337/100000000 : ℝ), (5176594443/10000000000 : ℝ), (-764767043/5000000000 : ℝ)] ![(23173823749091/50000000000000 : ℝ), (44018788230941/100000000000000 : ℝ), (9633564247743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53952337/100000000 : ℝ)|^5183 ≤ (23173823749091/50000000000000 : ℝ)^4159
        have hw : |(53952337/100000000 : ℝ)|=(53952337/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176594443/10000000000 : ℝ)|^5183 ≤ (44018788230941/100000000000000 : ℝ)^4159
        have hw : |(5176594443/10000000000 : ℝ)|=(5176594443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-764767043/5000000000 : ℝ)|^5183 ≤ (9633564247743/100000000000000 : ℝ)^4159
        have hw : |(-764767043/5000000000 : ℝ)|=(764767043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_7 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (745193533/2000000000 : ℝ)*x 0 + (869041079/2000000000 : ℝ)*x 1 + (2172602633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745193533/2000000000 : ℝ)^5183 ≤ (3652435615049/12500000000000 : ℝ)^4159 := by
    have hnat : (745193533 : ℕ)^5183*12500000000000^4159 ≤ 3652435615049^4159*2000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745193533 2000000000 3652435615049 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869041079/2000000000 : ℝ)^5183 ≤ (35390258184789/100000000000000 : ℝ)^4159 := by
    have hnat : (869041079 : ℕ)^5183*100000000000000^4159 ≤ 35390258184789^4159*2000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869041079 2000000000 35390258184789 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172602633/5000000000 : ℝ)^5183 ≤ (442378210943/1250000000000 : ℝ)^4159 := by
    have hnat : (2172602633 : ℕ)^5183*1250000000000^4159 ≤ 442378210943^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172602633 5000000000 442378210943 1250000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(745193533/2000000000 : ℝ), (869041079/2000000000 : ℝ), (2172602633/5000000000 : ℝ)] ![(3652435615049/12500000000000 : ℝ), (35390258184789/100000000000000 : ℝ), (442378210943/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(745193533/2000000000 : ℝ)|^5183 ≤ (3652435615049/12500000000000 : ℝ)^4159
        have hw : |(745193533/2000000000 : ℝ)|=(745193533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(869041079/2000000000 : ℝ)|^5183 ≤ (35390258184789/100000000000000 : ℝ)^4159
        have hw : |(869041079/2000000000 : ℝ)|=(869041079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2172602633/5000000000 : ℝ)|^5183 ≤ (442378210943/1250000000000 : ℝ)^4159
        have hw : |(2172602633/5000000000 : ℝ)|=(2172602633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_8 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52289499/312500000 : ℝ)*x 0 + (2496909071/5000000000 : ℝ)*x 1 + (1093734083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52289499/312500000 : ℝ)^5183 ≤ (2693617463713/25000000000000 : ℝ)^4159 := by
    have hnat : (52289499 : ℕ)^5183*25000000000000^4159 ≤ 2693617463713^4159*312500000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52289499 312500000 2693617463713 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2496909071/5000000000 : ℝ)^5183 ≤ (21045193994473/50000000000000 : ℝ)^4159 := by
    have hnat : (2496909071 : ℕ)^5183*50000000000000^4159 ≤ 21045193994473^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496909071 5000000000 21045193994473 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093734083/2000000000 : ℝ)^5183 ≤ (23567571073821/50000000000000 : ℝ)^4159 := by
    have hnat : (1093734083 : ℕ)^5183*50000000000000^4159 ≤ 23567571073821^4159*2000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093734083 2000000000 23567571073821 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52289499/312500000 : ℝ), (2496909071/5000000000 : ℝ), (1093734083/2000000000 : ℝ)] ![(2693617463713/25000000000000 : ℝ), (21045193994473/50000000000000 : ℝ), (23567571073821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52289499/312500000 : ℝ)|^5183 ≤ (2693617463713/25000000000000 : ℝ)^4159
        have hw : |(-52289499/312500000 : ℝ)|=(52289499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2496909071/5000000000 : ℝ)|^5183 ≤ (21045193994473/50000000000000 : ℝ)^4159
        have hw : |(2496909071/5000000000 : ℝ)|=(2496909071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093734083/2000000000 : ℝ)|^5183 ≤ (23567571073821/50000000000000 : ℝ)^4159
        have hw : |(1093734083/2000000000 : ℝ)|=(1093734083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_9 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598221687/5000000000 : ℝ)*x 0 + (-1401036183/10000000000 : ℝ)*x 1 + (5468670327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598221687/5000000000 : ℝ)^5183 ≤ (44229228141377/100000000000000 : ℝ)^4159 := by
    have hnat : (2598221687 : ℕ)^5183*100000000000000^4159 ≤ 44229228141377^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598221687 5000000000 44229228141377 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401036183/10000000000 : ℝ)^5183 ≤ (431781531773/5000000000000 : ℝ)^4159 := by
    have hnat : (1401036183 : ℕ)^5183*5000000000000^4159 ≤ 431781531773^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401036183 10000000000 431781531773 5000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468670327/10000000000 : ℝ)^5183 ≤ (47135141202411/100000000000000 : ℝ)^4159 := by
    have hnat : (5468670327 : ℕ)^5183*100000000000000^4159 ≤ 47135141202411^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468670327 10000000000 47135141202411 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598221687/5000000000 : ℝ), (-1401036183/10000000000 : ℝ), (5468670327/10000000000 : ℝ)] ![(44229228141377/100000000000000 : ℝ), (431781531773/5000000000000 : ℝ), (47135141202411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598221687/5000000000 : ℝ)|^5183 ≤ (44229228141377/100000000000000 : ℝ)^4159
        have hw : |(2598221687/5000000000 : ℝ)|=(2598221687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1401036183/10000000000 : ℝ)|^5183 ≤ (431781531773/5000000000000 : ℝ)^4159
        have hw : |(-1401036183/10000000000 : ℝ)|=(1401036183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468670327/10000000000 : ℝ)|^5183 ≤ (47135141202411/100000000000000 : ℝ)^4159
        have hw : |(5468670327/10000000000 : ℝ)|=(5468670327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_10 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196443233/10000000000 : ℝ)*x 0 + (5468670179/10000000000 : ℝ)*x 1 + (-280207317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196443233/10000000000 : ℝ)^5183 ≤ (2211461332289/5000000000000 : ℝ)^4159 := by
    have hnat : (5196443233 : ℕ)^5183*5000000000000^4159 ≤ 2211461332289^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196443233 10000000000 2211461332289 5000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468670179/10000000000 : ℝ)^5183 ≤ (1472973112897/3125000000000 : ℝ)^4159 := by
    have hnat : (5468670179 : ℕ)^5183*3125000000000^4159 ≤ 1472973112897^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468670179 10000000000 1472973112897 3125000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280207317/2000000000 : ℝ)^5183 ≤ (8635633723359/100000000000000 : ℝ)^4159 := by
    have hnat : (280207317 : ℕ)^5183*100000000000000^4159 ≤ 8635633723359^4159*2000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280207317 2000000000 8635633723359 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196443233/10000000000 : ℝ), (5468670179/10000000000 : ℝ), (-280207317/2000000000 : ℝ)] ![(2211461332289/5000000000000 : ℝ), (1472973112897/3125000000000 : ℝ), (8635633723359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196443233/10000000000 : ℝ)|^5183 ≤ (2211461332289/5000000000000 : ℝ)^4159
        have hw : |(5196443233/10000000000 : ℝ)|=(5196443233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468670179/10000000000 : ℝ)|^5183 ≤ (1472973112897/3125000000000 : ℝ)^4159
        have hw : |(5468670179/10000000000 : ℝ)|=(5468670179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280207317/2000000000 : ℝ)|^5183 ≤ (8635633723359/100000000000000 : ℝ)^4159
        have hw : |(-280207317/2000000000 : ℝ)|=(280207317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_11 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (72491183/156250000 : ℝ)*x 0 + (38867849/100000000 : ℝ)*x 1 + (3886785993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72491183/156250000 : ℝ)^5183 ≤ (38401177128797/100000000000000 : ℝ)^4159 := by
    have hnat : (72491183 : ℕ)^5183*100000000000000^4159 ≤ 38401177128797^4159*156250000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72491183 156250000 38401177128797 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38867849/100000000 : ℝ)^5183 ≤ (7699851507833/25000000000000 : ℝ)^4159 := by
    have hnat : (38867849 : ℕ)^5183*25000000000000^4159 ≤ 7699851507833^4159*100000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38867849 100000000 7699851507833 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3886785993/10000000000 : ℝ)^5183 ≤ (15399708412441/50000000000000 : ℝ)^4159 := by
    have hnat : (3886785993 : ℕ)^5183*50000000000000^4159 ≤ 15399708412441^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3886785993 10000000000 15399708412441 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(72491183/156250000 : ℝ), (38867849/100000000 : ℝ), (3886785993/10000000000 : ℝ)] ![(38401177128797/100000000000000 : ℝ), (7699851507833/25000000000000 : ℝ), (15399708412441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(72491183/156250000 : ℝ)|^5183 ≤ (38401177128797/100000000000000 : ℝ)^4159
        have hw : |(72491183/156250000 : ℝ)|=(72491183/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38867849/100000000 : ℝ)|^5183 ≤ (7699851507833/25000000000000 : ℝ)^4159
        have hw : |(38867849/100000000 : ℝ)|=(38867849/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3886785993/10000000000 : ℝ)|^5183 ≤ (15399708412441/50000000000000 : ℝ)^4159
        have hw : |(3886785993/10000000000 : ℝ)|=(3886785993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_12 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-31974543/250000000 : ℝ)*x 0 + (349944967/625000000 : ℝ)*x 1 + (5151328807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31974543/250000000 : ℝ)^5183 ≤ (963546572413/12500000000000 : ℝ)^4159 := by
    have hnat : (31974543 : ℕ)^5183*12500000000000^4159 ≤ 963546572413^4159*250000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31974543 250000000 963546572413 12500000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349944967/625000000 : ℝ)^5183 ≤ (24270210041729/50000000000000 : ℝ)^4159 := by
    have hnat : (349944967 : ℕ)^5183*50000000000000^4159 ≤ 24270210041729^4159*625000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349944967 625000000 24270210041729 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151328807/10000000000 : ℝ)^5183 ≤ (21875603662797/50000000000000 : ℝ)^4159 := by
    have hnat : (5151328807 : ℕ)^5183*50000000000000^4159 ≤ 21875603662797^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151328807 10000000000 21875603662797 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31974543/250000000 : ℝ), (349944967/625000000 : ℝ), (5151328807/10000000000 : ℝ)] ![(963546572413/12500000000000 : ℝ), (24270210041729/50000000000000 : ℝ), (21875603662797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31974543/250000000 : ℝ)|^5183 ≤ (963546572413/12500000000000 : ℝ)^4159
        have hw : |(-31974543/250000000 : ℝ)|=(31974543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(349944967/625000000 : ℝ)|^5183 ≤ (24270210041729/50000000000000 : ℝ)^4159
        have hw : |(349944967/625000000 : ℝ)|=(349944967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151328807/10000000000 : ℝ)|^5183 ≤ (21875603662797/50000000000000 : ℝ)^4159
        have hw : |(5151328807/10000000000 : ℝ)|=(5151328807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_13 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706229317/5000000000 : ℝ)*x 0 + (-19251399/125000000 : ℝ)*x 1 + (5151329629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706229317/5000000000 : ℝ)^5183 ≤ (23266061310993/50000000000000 : ℝ)^4159 := by
    have hnat : (2706229317 : ℕ)^5183*50000000000000^4159 ≤ 23266061310993^4159*5000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706229317 5000000000 23266061310993 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19251399/125000000 : ℝ)^5183 ≤ (2429165334767/25000000000000 : ℝ)^4159 := by
    have hnat : (19251399 : ℕ)^5183*25000000000000^4159 ≤ 2429165334767^4159*125000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19251399 125000000 2429165334767 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151329629/10000000000 : ℝ)^5183 ≤ (43751216025907/100000000000000 : ℝ)^4159 := by
    have hnat : (5151329629 : ℕ)^5183*100000000000000^4159 ≤ 43751216025907^4159*10000000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151329629 10000000000 43751216025907 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706229317/5000000000 : ℝ), (-19251399/125000000 : ℝ), (5151329629/10000000000 : ℝ)] ![(23266061310993/50000000000000 : ℝ), (2429165334767/25000000000000 : ℝ), (43751216025907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706229317/5000000000 : ℝ)|^5183 ≤ (23266061310993/50000000000000 : ℝ)^4159
        have hw : |(2706229317/5000000000 : ℝ)|=(2706229317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19251399/125000000 : ℝ)|^5183 ≤ (2429165334767/25000000000000 : ℝ)^4159
        have hw : |(-19251399/125000000 : ℝ)|=(19251399/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151329629/10000000000 : ℝ)|^5183 ≤ (43751216025907/100000000000000 : ℝ)^4159
        have hw : |(5151329629/10000000000 : ℝ)|=(5151329629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_14 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353114961/2500000000 : ℝ)*x 0 + (160978997/312500000 : ℝ)*x 1 + (-96257037/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353114961/2500000000 : ℝ)^5183 ≤ (23266067792947/50000000000000 : ℝ)^4159 := by
    have hnat : (1353114961 : ℕ)^5183*50000000000000^4159 ≤ 23266067792947^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353114961 2500000000 23266067792947 50000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160978997/312500000 : ℝ)^5183 ≤ (43751197767951/100000000000000 : ℝ)^4159 := by
    have hnat : (160978997 : ℕ)^5183*100000000000000^4159 ≤ 43751197767951^4159*312500000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160978997 312500000 43751197767951 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96257037/625000000 : ℝ)^5183 ≤ (77733332981/800000000000 : ℝ)^4159 := by
    have hnat : (96257037 : ℕ)^5183*800000000000^4159 ≤ 77733332981^4159*625000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96257037 625000000 77733332981 800000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353114961/2500000000 : ℝ), (160978997/312500000 : ℝ), (-96257037/625000000 : ℝ)] ![(23266067792947/50000000000000 : ℝ), (43751197767951/100000000000000 : ℝ), (77733332981/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353114961/2500000000 : ℝ)|^5183 ≤ (23266067792947/50000000000000 : ℝ)^4159
        have hw : |(1353114961/2500000000 : ℝ)|=(1353114961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160978997/312500000 : ℝ)|^5183 ≤ (43751197767951/100000000000000 : ℝ)^4159
        have hw : |(160978997/312500000 : ℝ)|=(160978997/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96257037/625000000 : ℝ)|^5183 ≤ (77733332981/800000000000 : ℝ)^4159
        have hw : |(-96257037/625000000 : ℝ)|=(96257037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1695_box_15 (p : ℝ) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (910883517/2500000000 : ℝ)*x 0 + (1096184881/2500000000 : ℝ)*x 1 + (109618421/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910883517/2500000000 : ℝ)^5183 ≤ (28416071856497/100000000000000 : ℝ)^4159 := by
    have hnat : (910883517 : ℕ)^5183*100000000000000^4159 ≤ 28416071856497^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910883517 2500000000 28416071856497 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096184881/2500000000 : ℝ)^5183 ≤ (35791977712567/100000000000000 : ℝ)^4159 := by
    have hnat : (1096184881 : ℕ)^5183*100000000000000^4159 ≤ 35791977712567^4159*2500000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096184881 2500000000 35791977712567 100000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109618421/250000000 : ℝ)^5183 ≤ (8947987602293/25000000000000 : ℝ)^4159 := by
    have hnat : (109618421 : ℕ)^5183*25000000000000^4159 ≤ 8947987602293^4159*250000000^5183 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109618421 250000000 8947987602293 25000000000000 5183 4159 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5183/1024 : ℝ)) 5183 4159 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(910883517/2500000000 : ℝ), (1096184881/2500000000 : ℝ), (109618421/250000000 : ℝ)] ![(28416071856497/100000000000000 : ℝ), (35791977712567/100000000000000 : ℝ), (8947987602293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(910883517/2500000000 : ℝ)|^5183 ≤ (28416071856497/100000000000000 : ℝ)^4159
        have hw : |(910883517/2500000000 : ℝ)|=(910883517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1096184881/2500000000 : ℝ)|^5183 ≤ (35791977712567/100000000000000 : ℝ)^4159
        have hw : |(1096184881/2500000000 : ℝ)|=(1096184881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109618421/250000000 : ℝ)|^5183 ≤ (8947987602293/25000000000000 : ℝ)^4159
        have hw : |(109618421/250000000 : ℝ)|=(109618421/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1695_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17199/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (247/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(33307/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58049/100000 : ℝ) ∧ (80979/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45103/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17199/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (247/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17199/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (247/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17199/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (247/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17199/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (247/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17199/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (247/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17199/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (247/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (247/2500 : ℝ) ^ (5175/1024 : ℝ) ≤ (831365840402861/100000000000000000000 : ℝ) := by
    have hpowers : (247/2500 : ℝ)^5175 ≤ (831365840402861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (247 : ℕ)^5175*100000000000000000000^1024 ≤ 831365840402861^1024*2500^5175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        247 2500 831365840402861 100000000000000000000 5175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (247/2500 : ℝ)) (X := (831365840402861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17199/100000 : ℝ) ^ (5175/1024 : ℝ) ≤ (13691598098939373/100000000000000000000 : ℝ) := by
    have hpowers : (17199/100000 : ℝ)^5175 ≤ (13691598098939373/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17199 : ℕ)^5175*100000000000000000000^1024 ≤ 13691598098939373^1024*100000^5175 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17199 100000 13691598098939373 100000000000000000000 5175 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17199/100000 : ℝ)) (X := (13691598098939373/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000831365840402861/50000000000000000000 : ℝ) ≤ (400001316039333/400000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (50000831365840402861/50000000000000000000 : ℝ)^1024 ≤ (400001316039333/400000000000000 : ℝ)^5175 := by
      have hnat : (50000831365840402861 : ℕ)^1024*400000000000000^5175 ≤ 400001316039333^5175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000831365840402861 50000000000000000000 400001316039333 400000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001316039333/400000000000000 : ℝ)) (X := (50000831365840402861/50000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007261481969671117/50000000000000000000 : ℝ) ≤ (400011494221403/400000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (50007261481969671117/50000000000000000000 : ℝ)^1024 ≤ (400011494221403/400000000000000 : ℝ)^5175 := by
      have hnat : (50007261481969671117 : ℕ)^1024*400000000000000^5175 ≤ 400011494221403^5175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007261481969671117 50000000000000000000 400011494221403 400000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400011494221403/400000000000000 : ℝ)) (X := (50007261481969671117/50000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013691598098939373/50000000000000000000 : ℝ) ≤ (400021672403473/400000000000000 : ℝ) ^ (5175/1024 : ℝ) := by
    have hpowers : (50013691598098939373/50000000000000000000 : ℝ)^1024 ≤ (400021672403473/400000000000000 : ℝ)^5175 := by
      have hnat : (50013691598098939373 : ℕ)^1024*400000000000000^5175 ≤ 400021672403473^5175*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013691598098939373 50000000000000000000 400021672403473 400000000000000 1024 5175 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400021672403473/400000000000000 : ℝ)) (X := (50013691598098939373/50000000000000000000 : ℝ)) (by norm_num) 5175 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(831365840402861/100000000000000000000 : ℝ) ≤ ((225185270093398079/225200000000000000 : ℝ)+2*(1017818207/2927600000000 : ℝ)*(247/2500 : ℝ))^(5175/1024 : ℝ) := by
    rw [show (225185270093398079/225200000000000000 : ℝ)+2*(1017818207/2927600000000 : ℝ)*(247/2500 : ℝ)=(400001316039333/400000000000000 : ℝ) by norm_num, show 1+2*(831365840402861/100000000000000000000 : ℝ)=(50000831365840402861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13691598098939373/100000000000000000000 : ℝ)+(831365840402861/100000000000000000000 : ℝ) ≤ ((225185270093398079/225200000000000000 : ℝ)+(1017818207/2927600000000 : ℝ)*((17199/100000 : ℝ)+(247/2500 : ℝ)))^(5175/1024 : ℝ) := by
    rw [show (225185270093398079/225200000000000000 : ℝ)+(1017818207/2927600000000 : ℝ)*((17199/100000 : ℝ)+(247/2500 : ℝ))=(400011494221403/400000000000000 : ℝ) by norm_num, show 1+(13691598098939373/100000000000000000000 : ℝ)+(831365840402861/100000000000000000000 : ℝ)=(50007261481969671117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13691598098939373/100000000000000000000 : ℝ) ≤ ((225185270093398079/225200000000000000 : ℝ)+2*(1017818207/2927600000000 : ℝ)*(17199/100000 : ℝ))^(5175/1024 : ℝ) := by
    rw [show (225185270093398079/225200000000000000 : ℝ)+2*(1017818207/2927600000000 : ℝ)*(17199/100000 : ℝ)=(400021672403473/400000000000000 : ℝ) by norm_num, show 1+2*(13691598098939373/100000000000000000000 : ℝ)=(50013691598098939373/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (225185270093398079/225200000000000000 : ℝ)*(X 1 0+X 2 0)+(1017818207/2927600000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (247/2500 : ℝ)) (hi := (17199/100000 : ℝ)) (c := (225185270093398079/225200000000000000 : ℝ)) (alpha := (1017818207/2927600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (225185270093398079/225200000000000000 : ℝ)*(X 0 1+X 2 1)+(1017818207/2927600000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (247/2500 : ℝ)) (hi := (17199/100000 : ℝ)) (c := (225185270093398079/225200000000000000 : ℝ)) (alpha := (1017818207/2927600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (225185270093398079/225200000000000000 : ℝ)*(X 0 2+X 1 2)+(1017818207/2927600000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5175/1024 : ℝ)) (lo := (247/2500 : ℝ)) (hi := (17199/100000 : ℝ)) (c := (225185270093398079/225200000000000000 : ℝ)) (alpha := (1017818207/2927600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1137472507/10000000000 : ℝ)*X 0 0+(271265221/500000000 : ℝ)*X 0 1+(2712652259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612973333/5000000000 : ℝ)*X 1 0+(-71040707/500000000 : ℝ)*X 1 1+(5425304679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612973233/5000000000 : ℝ)*X 2 0+(542530493/1000000000 : ℝ)*X 2 1+(-710407033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4508081021/10000000000 : ℝ)*X 0 0+(158200029/400000000 : ℝ)*X 0 1+(3955001017/10000000000 : ℝ)*X 0 2+(4508081021/10000000000 : ℝ)*X 1 0+(158200029/400000000 : ℝ)*X 1 1+(3955001017/10000000000 : ℝ)*X 1 2+(4508081021/10000000000 : ℝ)*X 2 0+(158200029/400000000 : ℝ)*X 2 1+(3955001017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-909878749/5000000000 : ℝ)*X 0 0+(2588297177/5000000000 : ℝ)*X 0 1+(258829723/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1079046747/2000000000 : ℝ)*X 1 0+(-1529534041/10000000000 : ℝ)*X 1 1+(2588297221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53952337/100000000 : ℝ)*X 2 0+(5176594443/10000000000 : ℝ)*X 2 1+(-764767043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((745193533/2000000000 : ℝ)*X 0 0+(869041079/2000000000 : ℝ)*X 0 1+(2172602633/5000000000 : ℝ)*X 0 2+(745193533/2000000000 : ℝ)*X 1 0+(869041079/2000000000 : ℝ)*X 1 1+(2172602633/5000000000 : ℝ)*X 1 2+(745193533/2000000000 : ℝ)*X 2 0+(869041079/2000000000 : ℝ)*X 2 1+(2172602633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-52289499/312500000 : ℝ)*X 0 0+(2496909071/5000000000 : ℝ)*X 0 1+(1093734083/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598221687/5000000000 : ℝ)*X 1 0+(-1401036183/10000000000 : ℝ)*X 1 1+(5468670327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196443233/10000000000 : ℝ)*X 2 0+(5468670179/10000000000 : ℝ)*X 2 1+(-280207317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((72491183/156250000 : ℝ)*X 0 0+(38867849/100000000 : ℝ)*X 0 1+(3886785993/10000000000 : ℝ)*X 0 2+(72491183/156250000 : ℝ)*X 1 0+(38867849/100000000 : ℝ)*X 1 1+(3886785993/10000000000 : ℝ)*X 1 2+(72491183/156250000 : ℝ)*X 2 0+(38867849/100000000 : ℝ)*X 2 1+(3886785993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-31974543/250000000 : ℝ)*X 0 0+(349944967/625000000 : ℝ)*X 0 1+(5151328807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2706229317/5000000000 : ℝ)*X 1 0+(-19251399/125000000 : ℝ)*X 1 1+(5151329629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1353114961/2500000000 : ℝ)*X 2 0+(160978997/312500000 : ℝ)*X 2 1+(-96257037/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((910883517/2500000000 : ℝ)*X 0 0+(1096184881/2500000000 : ℝ)*X 0 1+(109618421/250000000 : ℝ)*X 0 2+(910883517/2500000000 : ℝ)*X 1 0+(1096184881/2500000000 : ℝ)*X 1 1+(109618421/250000000 : ℝ)*X 1 2+(910883517/2500000000 : ℝ)*X 2 0+(1096184881/2500000000 : ℝ)*X 2 1+(109618421/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1695_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33307/50000 : ℝ) ≤ (-3750207843995085423972727769841/5630000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11978289/50000000000000 : ℝ)*(upper1) + (4385269/25000000000000 : ℝ)*(upper2) + (1429137/50000000000000 : ℝ)*(upper3) + (7784523/50000000000000 : ℝ)*(upper5) + (659205199723493/50000000000000 : ℝ)*(major0) + (659205199723493/50000000000000 : ℝ)*(major1) + (659205199723493/50000000000000 : ℝ)*(major2) + (73043409/20000000000000 : ℝ)*(sp3) + (196516636832279/10000000000000 : ℝ)*(sp4) + (982579708773327/50000000000000 : ℝ)*(sp5) + (122822850503421/6250000000000 : ℝ)*(sp6) + (693857782606913/100000000000000 : ℝ)*(sp7) + (1390155227/20000000000000 : ℝ)*(sp13) + (760268053/100000000000000 : ℝ)*(sp14) + (346929073911979/50000000000000 : ℝ)*(f.failure) + (196516636832279/10000000000000 : ℝ)*(f.sum) + (3905597642763/731900000000000000000000000 : ℝ)*base66 + (660675908487209311/146380000000000000000000000000000 : ℝ)*base67 + (448723634969930689/146380000000000000000000000000000 : ℝ)*base70 + (522674341056209311/146380000000000000000000000000000 : ℝ)*base71 + (1079290760187/3659500000000000000000000000 : ℝ)*base74 + (2341578134030529311/146380000000000000000000000000000 : ℝ)*base75 + (527059770103550689/146380000000000000000000000000000 : ℝ)*base78 + (778869663673209311/146380000000000000000000000000000 : ℝ)*base79 + (35428811167731/7319000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14087061/2500000000000000000000 : ℝ)*base89 + (14087061/2500000000000000000000 : ℝ)*base91 + (14087061/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58049/100000 : ℝ) ≤ (817073058352189240733659038171/1407500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6077259/6250000000000 : ℝ)*(upper2) + (76727929/100000000000000 : ℝ)*(upper4) + (23696373/100000000000000 : ℝ)*(upper5) + (177360460494861/12500000000000 : ℝ)*(major0) + (177360460494861/12500000000000 : ℝ)*(major1) + (177360460494861/12500000000000 : ℝ)*(major2) + (1035840446673851/50000000000000 : ℝ)*(sp0) + (2071679511743373/100000000000000 : ℝ)*(sp1) + (1035839137827987/50000000000000 : ℝ)*(sp2) + (373367701622451/50000000000000 : ℝ)*(sp3) + (1780506477/100000000000000 : ℝ)*(sp5) + (754148469/25000000000000 : ℝ)*(sp6) + (8606001/4000000000000 : ℝ)*(sp11) + (99725537/25000000000000 : ℝ)*(sp12) + (746735618394927/100000000000000 : ℝ)*(f.failure) + (41433625844997/2000000000000 : ℝ)*(f.sum) + (17314407345827/1829750000000000000000000000 : ℝ)*base65 + (289151925602833753/36595000000000000000000000000000 : ℝ)*base68 + (266738040138408753/36595000000000000000000000000000 : ℝ)*base70 + (9888110699188753/36595000000000000000000000000000 : ℝ)*base72 + (13644468403113/7319000000000000000000000000 : ℝ)*base73 + (259245141759663753/36595000000000000000000000000000 : ℝ)*base76 + (86465456282433753/36595000000000000000000000000000 : ℝ)*base78 + (269709521459073753/36595000000000000000000000000000 : ℝ)*base80 + (14290890782859/7319000000000000000000000000 : ℝ)*base81 + (1384593/5000000000000000000000 : ℝ)*base89 + (1384593/5000000000000000000000 : ℝ)*base91 + (1384593/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80979/100000 : ℝ) ≤ (4559280723288113624267670536949/5630000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (769943/1000000000000 : ℝ)*(upper0) + (66552037/100000000000000 : ℝ)*(upper2) + (8634937/12500000000000 : ℝ)*(lower3) + (122770089/100000000000000 : ℝ)*(lower5) + (723649990057059/50000000000000 : ℝ)*(major0) + (723649990057059/50000000000000 : ℝ)*(major1) + (723649990057059/50000000000000 : ℝ)*(major2) + (333608571/100000000000000 : ℝ)*(sp0) + (12493056983/100000000000000 : ℝ)*(sp1) + (421182987096117/20000000000000 : ℝ)*(sp8) + (1052951422407843/50000000000000 : ℝ)*(sp9) + (2105915337872669/100000000000000 : ℝ)*(sp10) + (380845328574797/50000000000000 : ℝ)*(sp11) + (68783513/100000000000000 : ℝ)*(sp12) + (380845328574797/50000000000000 : ℝ)*(f.failure) + (2105915337872669/100000000000000 : ℝ)*(f.sum) + (267431557767/563000000000000000000000000 : ℝ)*base65 + (75384335756770339/11260000000000000000000000000000 : ℝ)*base68 + (12167990654370339/11260000000000000000000000000000 : ℝ)*base70 + (63244721942210339/11260000000000000000000000000000 : ℝ)*base72 + (476245360373/281500000000000000000000000 : ℝ)*base74 + (59979045520470339/11260000000000000000000000000000 : ℝ)*base76 + (54437888992310339/11260000000000000000000000000000 : ℝ)*base78 + (48479868820270339/11260000000000000000000000000000 : ℝ)*base80 + (1159875688549/563000000000000000000000000 : ℝ)*base81 + (27255923/2500000000000000000000 : ℝ)*base89 + (27255923/2500000000000000000000 : ℝ)*base91 + (27255923/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-45103/50000 : ℝ) ≤ (-132039782096603572931942859655569/146380000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2167197/100000000000000 : ℝ)*(lower0) + (8402453/25000000000000 : ℝ)*(upper1) + (21589167/20000000000000 : ℝ)*(lower2) + (112903611/50000000000000 : ℝ)*(upper3) + (1494941578421351/100000000000000 : ℝ)*(major0) + (1494941578421351/100000000000000 : ℝ)*(major1) + (1494941578421351/100000000000000 : ℝ)*(major2) + (42694819/1250000000000 : ℝ)*(sp5) + (97615078517/100000000000000 : ℝ)*(sp6) + (16117138871/100000000000000 : ℝ)*(sp7) + (2233187304507747/100000000000000 : ℝ)*(sp12) + (2233183888922227/100000000000000 : ℝ)*(sp13) + (223308968942923/10000000000000 : ℝ)*(sp14) + (393373772741799/50000000000000 : ℝ)*(sp15) + (786763662622469/100000000000000 : ℝ)*(f.failure) + (2233187304507747/100000000000000 : ℝ)*(f.sum) + (28890482124591/7319000000000000000000000000 : ℝ)*base66 + (190332681672758523/292760000000000000000000000000000 : ℝ)*base68 + (1192194539449798523/292760000000000000000000000000000 : ℝ)*base70 + (188583068523081477/292760000000000000000000000000000 : ℝ)*base71 + (36487356727753/7319000000000000000000000000 : ℝ)*base74 + (636479335098761477/292760000000000000000000000000000 : ℝ)*base75 + (1262653985666438523/292760000000000000000000000000000 : ℝ)*base78 + (436416598515678523/292760000000000000000000000000000 : ℝ)*base80 + (5104860611177/3659500000000000000000000000 : ℝ)*base81 + (47798971/5000000000000000000000 : ℝ)*base89 + (47798971/5000000000000000000000 : ℝ)*base91 + (47798971/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1695_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17199/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (247/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33307/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58049/100000 : ℝ) else (80979/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45103/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1695_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1695_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33307/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58049/100000 : ℝ) else (80979/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45103/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1695_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1695_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1695_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5175/1024 : ℝ) ≤ p) (hpb : p ≤ (5183/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (95005759/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9863/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33307/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58049/100000 : ℝ) else (80979/100000 : ℝ) ≤ X j i ∧ X j i ≤ (45103/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1695_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

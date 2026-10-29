-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1653_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:16:55.096993+00:00
-- url     : https://prove2.me/submissions/287c13c7-2069-4ede-b3c8-92fccc142133

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
theorem support_rectangle_w1653_s3_0 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-400429581/2500000000 : ℝ)*x 0 + (5446711081/10000000000 : ℝ)*x 1 + (1036808973/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400429581/2500000000 : ℝ)^4931 ≤ (9910902437289/100000000000000 : ℝ)^3907 := by
    have hnat : (400429581 : ℕ)^4931*100000000000000^3907 ≤ 9910902437289^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400429581 2500000000 9910902437289 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446711081/10000000000 : ℝ)^4931 ≤ (23224523997069/50000000000000 : ℝ)^3907 := by
    have hnat : (5446711081 : ℕ)^4931*50000000000000^3907 ≤ 23224523997069^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446711081 10000000000 23224523997069 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036808973/2000000000 : ℝ)^4931 ≤ (43640049554503/100000000000000 : ℝ)^3907 := by
    have hnat : (1036808973 : ℕ)^4931*100000000000000^3907 ≤ 43640049554503^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036808973 2000000000 43640049554503 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400429581/2500000000 : ℝ), (5446711081/10000000000 : ℝ), (1036808973/2000000000 : ℝ)] ![(9910902437289/100000000000000 : ℝ), (23224523997069/50000000000000 : ℝ), (43640049554503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400429581/2500000000 : ℝ)|^4931 ≤ (9910902437289/100000000000000 : ℝ)^3907
        have hw : |(-400429581/2500000000 : ℝ)|=(400429581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446711081/10000000000 : ℝ)|^4931 ≤ (23224523997069/50000000000000 : ℝ)^3907
        have hw : |(5446711081/10000000000 : ℝ)|=(5446711081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036808973/2000000000 : ℝ)|^4931 ≤ (43640049554503/100000000000000 : ℝ)^3907
        have hw : |(1036808973/2000000000 : ℝ)|=(1036808973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_1 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347307997/10000000000 : ℝ)*x 0 + (-54278809/312500000 : ℝ)*x 1 + (5184044863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347307997/10000000000 : ℝ)^4931 ≤ (11345435280323/25000000000000 : ℝ)^3907 := by
    have hnat : (5347307997 : ℕ)^4931*25000000000000^3907 ≤ 11345435280323^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347307997 10000000000 11345435280323 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54278809/312500000 : ℝ)^4931 ≤ (1097820933101/10000000000000 : ℝ)^3907 := by
    have hnat : (54278809 : ℕ)^4931*10000000000000^3907 ≤ 1097820933101^3907*312500000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54278809 312500000 1097820933101 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184044863/10000000000 : ℝ)^4931 ≤ (21820024766627/50000000000000 : ℝ)^3907 := by
    have hnat : (5184044863 : ℕ)^4931*50000000000000^3907 ≤ 21820024766627^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184044863 10000000000 21820024766627 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347307997/10000000000 : ℝ), (-54278809/312500000 : ℝ), (5184044863/10000000000 : ℝ)] ![(11345435280323/25000000000000 : ℝ), (1097820933101/10000000000000 : ℝ), (21820024766627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347307997/10000000000 : ℝ)|^4931 ≤ (11345435280323/25000000000000 : ℝ)^3907
        have hw : |(5347307997/10000000000 : ℝ)|=(5347307997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54278809/312500000 : ℝ)|^4931 ≤ (1097820933101/10000000000000 : ℝ)^3907
        have hw : |(-54278809/312500000 : ℝ)|=(54278809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184044863/10000000000 : ℝ)|^4931 ≤ (21820024766627/50000000000000 : ℝ)^3907
        have hw : |(5184044863/10000000000 : ℝ)|=(5184044863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_2 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347307997/10000000000 : ℝ)*x 0 + (2592022431/5000000000 : ℝ)*x 1 + (-1736921889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347307997/10000000000 : ℝ)^4931 ≤ (11345435280323/25000000000000 : ℝ)^3907 := by
    have hnat : (5347307997 : ℕ)^4931*25000000000000^3907 ≤ 11345435280323^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347307997 10000000000 11345435280323 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592022431/5000000000 : ℝ)^4931 ≤ (4364004952263/10000000000000 : ℝ)^3907 := by
    have hnat : (2592022431 : ℕ)^4931*10000000000000^3907 ≤ 4364004952263^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592022431 5000000000 4364004952263 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736921889/10000000000 : ℝ)^4931 ≤ (10978209338987/100000000000000 : ℝ)^3907 := by
    have hnat : (1736921889 : ℕ)^4931*100000000000000^3907 ≤ 10978209338987^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736921889 10000000000 10978209338987 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347307997/10000000000 : ℝ), (2592022431/5000000000 : ℝ), (-1736921889/10000000000 : ℝ)] ![(11345435280323/25000000000000 : ℝ), (4364004952263/10000000000000 : ℝ), (10978209338987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347307997/10000000000 : ℝ)|^4931 ≤ (11345435280323/25000000000000 : ℝ)^3907
        have hw : |(5347307997/10000000000 : ℝ)|=(5347307997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592022431/5000000000 : ℝ)|^4931 ≤ (4364004952263/10000000000000 : ℝ)^3907
        have hw : |(2592022431/5000000000 : ℝ)|=(2592022431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736921889/10000000000 : ℝ)|^4931 ≤ (10978209338987/100000000000000 : ℝ)^3907
        have hw : |(-1736921889/10000000000 : ℝ)|=(1736921889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_3 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4178424437/10000000000 : ℝ)*x 0 + (3847399907/10000000000 : ℝ)*x 1 + (113238809/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178424437/10000000000 : ℝ)^4931 ≤ (3324163210977/10000000000000 : ℝ)^3907 := by
    have hnat : (4178424437 : ℕ)^4931*10000000000000^3907 ≤ 3324163210977^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178424437 10000000000 3324163210977 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3847399907/10000000000 : ℝ)^4931 ≤ (7488284199461/25000000000000 : ℝ)^3907 := by
    have hnat : (3847399907 : ℕ)^4931*25000000000000^3907 ≤ 7488284199461^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3847399907 10000000000 7488284199461 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113238809/250000000 : ℝ)^4931 ≤ (7361046215463/20000000000000 : ℝ)^3907 := by
    have hnat : (113238809 : ℕ)^4931*20000000000000^3907 ≤ 7361046215463^3907*250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113238809 250000000 7361046215463 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178424437/10000000000 : ℝ), (3847399907/10000000000 : ℝ), (113238809/250000000 : ℝ)] ![(3324163210977/10000000000000 : ℝ), (7488284199461/25000000000000 : ℝ), (7361046215463/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178424437/10000000000 : ℝ)|^4931 ≤ (3324163210977/10000000000000 : ℝ)^3907
        have hw : |(4178424437/10000000000 : ℝ)|=(4178424437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3847399907/10000000000 : ℝ)|^4931 ≤ (7488284199461/25000000000000 : ℝ)^3907
        have hw : |(3847399907/10000000000 : ℝ)|=(3847399907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113238809/250000000 : ℝ)|^4931 ≤ (7361046215463/20000000000000 : ℝ)^3907
        have hw : |(113238809/250000000 : ℝ)|=(113238809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_4 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-200222779/1250000000 : ℝ)*x 0 + (5186036131/10000000000 : ℝ)*x 1 + (5444698877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200222779/1250000000 : ℝ)^4931 ≤ (30973129763/312500000000 : ℝ)^3907 := by
    have hnat : (200222779 : ℕ)^4931*312500000000^3907 ≤ 30973129763^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200222779 1250000000 30973129763 312500000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186036131/10000000000 : ℝ)^4931 ≤ (43661206804209/100000000000000 : ℝ)^3907 := by
    have hnat : (5186036131 : ℕ)^4931*100000000000000^3907 ≤ 43661206804209^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186036131 10000000000 43661206804209 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444698877/10000000000 : ℝ)^4931 ≤ (5803423956839/12500000000000 : ℝ)^3907 := by
    have hnat : (5444698877 : ℕ)^4931*12500000000000^3907 ≤ 5803423956839^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444698877 10000000000 5803423956839 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200222779/1250000000 : ℝ), (5186036131/10000000000 : ℝ), (5444698877/10000000000 : ℝ)] ![(30973129763/312500000000 : ℝ), (43661206804209/100000000000000 : ℝ), (5803423956839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200222779/1250000000 : ℝ)|^4931 ≤ (30973129763/312500000000 : ℝ)^3907
        have hw : |(-200222779/1250000000 : ℝ)|=(200222779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186036131/10000000000 : ℝ)|^4931 ≤ (43661206804209/100000000000000 : ℝ)^3907
        have hw : |(5186036131/10000000000 : ℝ)|=(5186036131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444698877/10000000000 : ℝ)|^4931 ≤ (5803423956839/12500000000000 : ℝ)^3907
        have hw : |(5444698877/10000000000 : ℝ)|=(5444698877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_5 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42216887/80000000 : ℝ)*x 0 + (-738133929/5000000000 : ℝ)*x 1 + (5444698919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42216887/80000000 : ℝ)^4931 ≤ (22315572210439/50000000000000 : ℝ)^3907 := by
    have hnat : (42216887 : ℕ)^4931*50000000000000^3907 ≤ 22315572210439^3907*80000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42216887 80000000 22315572210439 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738133929/5000000000 : ℝ)^4931 ≤ (4470731731479/50000000000000 : ℝ)^3907 := by
    have hnat : (738133929 : ℕ)^4931*50000000000000^3907 ≤ 4470731731479^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738133929 5000000000 4470731731479 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444698919/10000000000 : ℝ)^4931 ≤ (9285478421343/20000000000000 : ℝ)^3907 := by
    have hnat : (5444698919 : ℕ)^4931*20000000000000^3907 ≤ 9285478421343^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444698919 10000000000 9285478421343 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42216887/80000000 : ℝ), (-738133929/5000000000 : ℝ), (5444698919/10000000000 : ℝ)] ![(22315572210439/50000000000000 : ℝ), (4470731731479/50000000000000 : ℝ), (9285478421343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42216887/80000000 : ℝ)|^4931 ≤ (22315572210439/50000000000000 : ℝ)^3907
        have hw : |(42216887/80000000 : ℝ)|=(42216887/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-738133929/5000000000 : ℝ)|^4931 ≤ (4470731731479/50000000000000 : ℝ)^3907
        have hw : |(-738133929/5000000000 : ℝ)|=(738133929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444698919/10000000000 : ℝ)|^4931 ≤ (9285478421343/20000000000000 : ℝ)^3907
        have hw : |(5444698919/10000000000 : ℝ)|=(5444698919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_6 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277111067/10000000000 : ℝ)*x 0 + (5444698719/10000000000 : ℝ)*x 1 + (-46133371/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277111067/10000000000 : ℝ)^4931 ≤ (8926229294063/20000000000000 : ℝ)^3907 := by
    have hnat : (5277111067 : ℕ)^4931*20000000000000^3907 ≤ 8926229294063^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277111067 10000000000 8926229294063 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444698719/10000000000 : ℝ)^4931 ≤ (580342374429/1250000000000 : ℝ)^3907 := by
    have hnat : (5444698719 : ℕ)^4931*1250000000000^3907 ≤ 580342374429^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444698719 10000000000 580342374429 1250000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46133371/312500000 : ℝ)^4931 ≤ (4470731784989/50000000000000 : ℝ)^3907 := by
    have hnat : (46133371 : ℕ)^4931*50000000000000^3907 ≤ 4470731784989^3907*312500000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46133371 312500000 4470731784989 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277111067/10000000000 : ℝ), (5444698719/10000000000 : ℝ), (-46133371/312500000 : ℝ)] ![(8926229294063/20000000000000 : ℝ), (580342374429/1250000000000 : ℝ), (4470731784989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277111067/10000000000 : ℝ)|^4931 ≤ (8926229294063/20000000000000 : ℝ)^3907
        have hw : |(5277111067/10000000000 : ℝ)|=(5277111067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444698719/10000000000 : ℝ)|^4931 ≤ (580342374429/1250000000000 : ℝ)^3907
        have hw : |(5444698719/10000000000 : ℝ)|=(5444698719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46133371/312500000 : ℝ)|^4931 ≤ (4470731784989/50000000000000 : ℝ)^3907
        have hw : |(-46133371/312500000 : ℝ)|=(46133371/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s3_7 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522323799/1250000000 : ℝ)*x 0 + (1131095269/2500000000 : ℝ)*x 1 + (1926312949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522323799/1250000000 : ℝ)^4931 ≤ (16621649206391/50000000000000 : ℝ)^3907 := by
    have hnat : (522323799 : ℕ)^4931*50000000000000^3907 ≤ 16621649206391^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522323799 1250000000 16621649206391 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131095269/2500000000 : ℝ)^4931 ≤ (9188051563021/25000000000000 : ℝ)^3907 := by
    have hnat : (1131095269 : ℕ)^4931*25000000000000^3907 ≤ 9188051563021^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131095269 2500000000 9188051563021 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926312949/5000000000 : ℝ)^4931 ≤ (15002247659013/50000000000000 : ℝ)^3907 := by
    have hnat : (1926312949 : ℕ)^4931*50000000000000^3907 ≤ 15002247659013^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926312949 5000000000 15002247659013 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522323799/1250000000 : ℝ), (1131095269/2500000000 : ℝ), (1926312949/5000000000 : ℝ)] ![(16621649206391/50000000000000 : ℝ), (9188051563021/25000000000000 : ℝ), (15002247659013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522323799/1250000000 : ℝ)|^4931 ≤ (16621649206391/50000000000000 : ℝ)^3907
        have hw : |(522323799/1250000000 : ℝ)|=(522323799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131095269/2500000000 : ℝ)|^4931 ≤ (9188051563021/25000000000000 : ℝ)^3907
        have hw : |(1131095269/2500000000 : ℝ)|=(1131095269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1926312949/5000000000 : ℝ)|^4931 ≤ (15002247659013/50000000000000 : ℝ)^3907
        have hw : |(1926312949/5000000000 : ℝ)|=(1926312949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1653_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (5341/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8133/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (531/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (531/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (531/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (531/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (531/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (531/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (531/5000 : ℝ) ^ (4927/1024 : ℝ) ≤ (515365444794483/25000000000000000000 : ℝ) := by
    have hpowers : (531/5000 : ℝ)^4927 ≤ (515365444794483/25000000000000000000 : ℝ)^1024 := by
      have hnat : (531 : ℕ)^4927*25000000000000000000^1024 ≤ 515365444794483^1024*5000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        531 5000 515365444794483 25000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (531/5000 : ℝ)) (X := (515365444794483/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1021/6250 : ℝ) ^ (4927/1024 : ℝ) ≤ (16369379326873513/100000000000000000000 : ℝ) := by
    have hpowers : (1021/6250 : ℝ)^4927 ≤ (16369379326873513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1021 : ℕ)^4927*100000000000000000000^1024 ≤ 16369379326873513^1024*6250^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1021 6250 16369379326873513 100000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1021/6250 : ℝ)) (X := (16369379326873513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500515365444794483/12500000000000000000 : ℝ) ≤ (5000042843563847/5000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (12500515365444794483/12500000000000000000 : ℝ)^1024 ≤ (5000042843563847/5000000000000000 : ℝ)^4927 := by
      have hnat : (12500515365444794483 : ℕ)^1024*5000000000000000^4927 ≤ 5000042843563847^4927*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500515365444794483 12500000000000000000 5000042843563847 5000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042843563847/5000000000000000 : ℝ)) (X := (12500515365444794483/12500000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20003686168221210289/20000000000000000000 : ℝ) ≤ (5000191514143249/5000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (20003686168221210289/20000000000000000000 : ℝ)^1024 ≤ (5000191514143249/5000000000000000 : ℝ)^4927 := by
      have hnat : (20003686168221210289 : ℕ)^1024*5000000000000000^4927 ≤ 5000191514143249^4927*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20003686168221210289 20000000000000000000 5000191514143249 5000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000191514143249/5000000000000000 : ℝ)) (X := (20003686168221210289/20000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016369379326873513/50000000000000000000 : ℝ) ≤ (5000340184722651/5000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (50016369379326873513/50000000000000000000 : ℝ)^1024 ≤ (5000340184722651/5000000000000000 : ℝ)^4927 := by
      have hnat : (50016369379326873513 : ℕ)^1024*5000000000000000^4927 ≤ 5000340184722651^4927*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016369379326873513 50000000000000000000 5000340184722651 5000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340184722651/5000000000000000 : ℝ)) (X := (50016369379326873513/50000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(515365444794483/25000000000000000000 : ℝ) ≤ ((7144271782676112743/7145000000000000000 : ℝ)+2*(74335289701/142900000000000 : ℝ)*(531/5000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (7144271782676112743/7145000000000000000 : ℝ)+2*(74335289701/142900000000000 : ℝ)*(531/5000 : ℝ)=(5000042843563847/5000000000000000 : ℝ) by norm_num, show 1+2*(515365444794483/25000000000000000000 : ℝ)=(12500515365444794483/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16369379326873513/100000000000000000000 : ℝ)+(515365444794483/25000000000000000000 : ℝ) ≤ ((7144271782676112743/7145000000000000000 : ℝ)+(74335289701/142900000000000 : ℝ)*((1021/6250 : ℝ)+(531/5000 : ℝ)))^(4927/1024 : ℝ) := by
    rw [show (7144271782676112743/7145000000000000000 : ℝ)+(74335289701/142900000000000 : ℝ)*((1021/6250 : ℝ)+(531/5000 : ℝ))=(5000191514143249/5000000000000000 : ℝ) by norm_num, show 1+(16369379326873513/100000000000000000000 : ℝ)+(515365444794483/25000000000000000000 : ℝ)=(20003686168221210289/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16369379326873513/100000000000000000000 : ℝ) ≤ ((7144271782676112743/7145000000000000000 : ℝ)+2*(74335289701/142900000000000 : ℝ)*(1021/6250 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (7144271782676112743/7145000000000000000 : ℝ)+2*(74335289701/142900000000000 : ℝ)*(1021/6250 : ℝ)=(5000340184722651/5000000000000000 : ℝ) by norm_num, show 1+2*(16369379326873513/100000000000000000000 : ℝ)=(50016369379326873513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7144271782676112743/7145000000000000000 : ℝ)*(X 1 0+X 2 0)+(74335289701/142900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (531/5000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (7144271782676112743/7145000000000000000 : ℝ)) (alpha := (74335289701/142900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7144271782676112743/7145000000000000000 : ℝ)*(X 0 1+X 2 1)+(74335289701/142900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (531/5000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (7144271782676112743/7145000000000000000 : ℝ)) (alpha := (74335289701/142900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7144271782676112743/7145000000000000000 : ℝ)*(X 0 2+X 1 2)+(74335289701/142900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (531/5000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (7144271782676112743/7145000000000000000 : ℝ)) (alpha := (74335289701/142900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-400429581/2500000000 : ℝ)*X 0 0+(5446711081/10000000000 : ℝ)*X 0 1+(1036808973/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347307997/10000000000 : ℝ)*X 1 0+(-54278809/312500000 : ℝ)*X 1 1+(5184044863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347307997/10000000000 : ℝ)*X 2 0+(2592022431/5000000000 : ℝ)*X 2 1+(-1736921889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4178424437/10000000000 : ℝ)*X 0 0+(3847399907/10000000000 : ℝ)*X 0 1+(113238809/250000000 : ℝ)*X 0 2+(4178424437/10000000000 : ℝ)*X 1 0+(3847399907/10000000000 : ℝ)*X 1 1+(113238809/250000000 : ℝ)*X 1 2+(4178424437/10000000000 : ℝ)*X 2 0+(3847399907/10000000000 : ℝ)*X 2 1+(113238809/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200222779/1250000000 : ℝ)*X 0 0+(5186036131/10000000000 : ℝ)*X 0 1+(5444698877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((42216887/80000000 : ℝ)*X 1 0+(-738133929/5000000000 : ℝ)*X 1 1+(5444698919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277111067/10000000000 : ℝ)*X 2 0+(5444698719/10000000000 : ℝ)*X 2 1+(-46133371/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522323799/1250000000 : ℝ)*X 0 0+(1131095269/2500000000 : ℝ)*X 0 1+(1926312949/5000000000 : ℝ)*X 0 2+(522323799/1250000000 : ℝ)*X 1 0+(1131095269/2500000000 : ℝ)*X 1 1+(1926312949/5000000000 : ℝ)*X 1 2+(522323799/1250000000 : ℝ)*X 2 0+(1131095269/2500000000 : ℝ)*X 2 1+(1926312949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (146818929529007730605589531/22328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1033759079/100000000000000 : ℝ)*(base19) + (968614331/100000000000000 : ℝ)*(base23) + (17417451/50000000000000 : ℝ)*(lower2) + (160038543/100000000000000 : ℝ)*(upper3) + (112526457/100000000000000 : ℝ)*(upper5) + (164784305922811/6250000000000 : ℝ)*(major0) + (164784305922811/6250000000000 : ℝ)*(major1) + (164784305922811/6250000000000 : ℝ)*(major2) + (1903563232448499/50000000000000 : ℝ)*(sp0) + (3807138362216949/100000000000000 : ℝ)*(sp1) + (118973075855053/3125000000000 : ℝ)*(sp2) + (146595276572611/10000000000000 : ℝ)*(sp3) + (1293107903/10000000000000 : ℝ)*(sp4) + (2704321979/50000000000000 : ℝ)*(sp7) + (1465958174370067/100000000000000 : ℝ)*(f.failure) + (951784848994007/25000000000000 : ℝ)*(f.sum) + (5525783518273/3572500000000000000000000000 : ℝ)*base65 + (283219183478468073/44656250000000000000000000000000 : ℝ)*base67 + (280866514603469427/44656250000000000000000000000000 : ℝ)*base70 + (508600866410436823/44656250000000000000000000000000 : ℝ)*base71 + (3284414362697/3572500000000000000000000000 : ℝ)*base74 + (704204120966063177/44656250000000000000000000000000 : ℝ)*base76 + (214064239110093073/44656250000000000000000000000000 : ℝ)*base77 + (219015187699218073/44656250000000000000000000000000 : ℝ)*base79 + (1888440447031/1786250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (68454341/10000000000000000000000 : ℝ)*base90 + (68454341/10000000000000000000000 : ℝ)*base92 + (68454341/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (444369075013178358786005901/178625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (270504791/100000000000000 : ℝ)*(base19) + (431181649/100000000000000 : ℝ)*(base23) + (3467493/25000000000000 : ℝ)*(upper3) + (10603539/100000000000000 : ℝ)*(lower4) + (29831841/100000000000000 : ℝ)*(upper5) + (2677338223496031/100000000000000 : ℝ)*(major0) + (2677338223496031/100000000000000 : ℝ)*(major1) + (2677338223496031/100000000000000 : ℝ)*(major2) + (4818281733/100000000000000 : ℝ)*(sp1) + (2406261599/50000000000000 : ℝ)*(sp2) + (3866038750678623/100000000000000 : ℝ)*(sp4) + (1933016830946049/50000000000000 : ℝ)*(sp5) + (241627094185861/6250000000000 : ℝ)*(sp6) + (744318806694709/50000000000000 : ℝ)*(sp7) + (744318806694709/50000000000000 : ℝ)*(f.failure) + (3866038750678623/100000000000000 : ℝ)*(f.sum) + (13490227134669/7145000000000000000000000000 : ℝ)*base66 + (105079372318926967/714500000000000000000000000000000 : ℝ)*base68 + (1655182580748073033/714500000000000000000000000000000 : ℝ)*base69 + (1105587271604073033/714500000000000000000000000000000 : ℝ)*base71 + (30154871171369/7145000000000000000000000000 : ℝ)*base74 + (7167819254333073033/714500000000000000000000000000000 : ℝ)*base75 + (162798200422573033/714500000000000000000000000000000 : ℝ)*base77 + (4214663299679573033/714500000000000000000000000000000 : ℝ)*base79 + (10764383555419/7145000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (21206093/5000000000000000000000 : ℝ)*base89 + (21206093/5000000000000000000000 : ℝ)*base91 + (21206093/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1653_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8133/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1653_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1653_s4_0 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40044039/250000000 : ℝ)*x 0 + (2723248171/5000000000 : ℝ)*x 1 + (2592115311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40044039/250000000 : ℝ)^4931 ≤ (154863126351/1562500000000 : ℝ)^3907 := by
    have hnat : (40044039 : ℕ)^4931*1562500000000^3907 ≤ 154863126351^3907*250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40044039 250000000 154863126351 1562500000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723248171/5000000000 : ℝ)^4931 ≤ (46446736766341/100000000000000 : ℝ)^3907 := by
    have hnat : (2723248171 : ℕ)^4931*100000000000000^3907 ≤ 46446736766341^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723248171 5000000000 46446736766341 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592115311/5000000000 : ℝ)^4931 ≤ (43642023137081/100000000000000 : ℝ)^3907 := by
    have hnat : (2592115311 : ℕ)^4931*100000000000000^3907 ≤ 43642023137081^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592115311 5000000000 43642023137081 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40044039/250000000 : ℝ), (2723248171/5000000000 : ℝ), (2592115311/5000000000 : ℝ)] ![(154863126351/1562500000000 : ℝ), (46446736766341/100000000000000 : ℝ), (43642023137081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40044039/250000000 : ℝ)|^4931 ≤ (154863126351/1562500000000 : ℝ)^3907
        have hw : |(-40044039/250000000 : ℝ)|=(40044039/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723248171/5000000000 : ℝ)|^4931 ≤ (46446736766341/100000000000000 : ℝ)^3907
        have hw : |(2723248171/5000000000 : ℝ)|=(2723248171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592115311/5000000000 : ℝ)|^4931 ≤ (43642023137081/100000000000000 : ℝ)^3907
        have hw : |(2592115311/5000000000 : ℝ)|=(2592115311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_1 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069449901/2000000000 : ℝ)*x 0 + (-868376409/5000000000 : ℝ)*x 1 + (5184230771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069449901/2000000000 : ℝ)^4931 ≤ (4431749473/9765625000 : ℝ)^3907 := by
    have hnat : (1069449901 : ℕ)^4931*9765625000^3907 ≤ 4431749473^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069449901 2000000000 4431749473 9765625000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (868376409/5000000000 : ℝ)^4931 ≤ (2744215166707/25000000000000 : ℝ)^3907 := by
    have hnat : (868376409 : ℕ)^4931*25000000000000^3907 ≤ 2744215166707^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868376409 5000000000 2744215166707 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184230771/10000000000 : ℝ)^4931 ≤ (8728404944029/20000000000000 : ℝ)^3907 := by
    have hnat : (5184230771 : ℕ)^4931*20000000000000^3907 ≤ 8728404944029^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184230771 10000000000 8728404944029 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069449901/2000000000 : ℝ), (-868376409/5000000000 : ℝ), (5184230771/10000000000 : ℝ)] ![(4431749473/9765625000 : ℝ), (2744215166707/25000000000000 : ℝ), (8728404944029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069449901/2000000000 : ℝ)|^4931 ≤ (4431749473/9765625000 : ℝ)^3907
        have hw : |(1069449901/2000000000 : ℝ)|=(1069449901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-868376409/5000000000 : ℝ)|^4931 ≤ (2744215166707/25000000000000 : ℝ)^3907
        have hw : |(-868376409/5000000000 : ℝ)|=(868376409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184230771/10000000000 : ℝ)|^4931 ≤ (8728404944029/20000000000000 : ℝ)^3907
        have hw : |(5184230771/10000000000 : ℝ)|=(5184230771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_2 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347249517/10000000000 : ℝ)*x 0 + (2592115337/5000000000 : ℝ)*x 1 + (-173675293/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347249517/10000000000 : ℝ)^4931 ≤ (22690557366027/50000000000000 : ℝ)^3907 := by
    have hnat : (5347249517 : ℕ)^4931*50000000000000^3907 ≤ 22690557366027^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347249517 10000000000 22690557366027 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592115337/5000000000 : ℝ)^4931 ≤ (1091050592239/2500000000000 : ℝ)^3907 := by
    have hnat : (2592115337 : ℕ)^4931*2500000000000^3907 ≤ 1091050592239^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592115337 5000000000 1091050592239 2500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173675293/1000000000 : ℝ)^4931 ≤ (2744215390059/25000000000000 : ℝ)^3907 := by
    have hnat : (173675293 : ℕ)^4931*25000000000000^3907 ≤ 2744215390059^3907*1000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173675293 1000000000 2744215390059 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347249517/10000000000 : ℝ), (2592115337/5000000000 : ℝ), (-173675293/1000000000 : ℝ)] ![(22690557366027/50000000000000 : ℝ), (1091050592239/2500000000000 : ℝ), (2744215390059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347249517/10000000000 : ℝ)|^4931 ≤ (22690557366027/50000000000000 : ℝ)^3907
        have hw : |(5347249517/10000000000 : ℝ)|=(5347249517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592115337/5000000000 : ℝ)|^4931 ≤ (1091050592239/2500000000000 : ℝ)^3907
        have hw : |(2592115337/5000000000 : ℝ)|=(2592115337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173675293/1000000000 : ℝ)|^4931 ≤ (2744215390059/25000000000000 : ℝ)^3907
        have hw : |(-173675293/1000000000 : ℝ)|=(173675293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_3 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1044613037/2500000000 : ℝ)*x 0 + (38479173/100000000 : ℝ)*x 1 + (4529029487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044613037/2500000000 : ℝ)^4931 ≤ (1329676413847/4000000000000 : ℝ)^3907 := by
    have hnat : (1044613037 : ℕ)^4931*4000000000000^3907 ≤ 1329676413847^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044613037 2500000000 1329676413847 4000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38479173/100000000 : ℝ)^4931 ≤ (14979110335891/50000000000000 : ℝ)^3907 := by
    have hnat : (38479173 : ℕ)^4931*50000000000000^3907 ≤ 14979110335891^3907*100000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38479173 100000000 14979110335891 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4529029487/10000000000 : ℝ)^4931 ≤ (36799868969993/100000000000000 : ℝ)^3907 := by
    have hnat : (4529029487 : ℕ)^4931*100000000000000^3907 ≤ 36799868969993^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529029487 10000000000 36799868969993 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044613037/2500000000 : ℝ), (38479173/100000000 : ℝ), (4529029487/10000000000 : ℝ)] ![(1329676413847/4000000000000 : ℝ), (14979110335891/50000000000000 : ℝ), (36799868969993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044613037/2500000000 : ℝ)|^4931 ≤ (1329676413847/4000000000000 : ℝ)^3907
        have hw : |(1044613037/2500000000 : ℝ)|=(1044613037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38479173/100000000 : ℝ)|^4931 ≤ (14979110335891/50000000000000 : ℝ)^3907
        have hw : |(38479173/100000000 : ℝ)|=(38479173/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4529029487/10000000000 : ℝ)|^4931 ≤ (36799868969993/100000000000000 : ℝ)^3907
        have hw : |(4529029487/10000000000 : ℝ)|=(4529029487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_4 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1601825069/10000000000 : ℝ)*x 0 + (2593107967/5000000000 : ℝ)*x 1 + (2722245133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1601825069/10000000000 : ℝ)^4931 ≤ (4955868030427/50000000000000 : ℝ)^3907 := by
    have hnat : (1601825069 : ℕ)^4931*50000000000000^3907 ≤ 4955868030427^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601825069 10000000000 4955868030427 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593107967/5000000000 : ℝ)^4931 ≤ (43663117320281/100000000000000 : ℝ)^3907 := by
    have hnat : (2593107967 : ℕ)^4931*100000000000000^3907 ≤ 43663117320281^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593107967 5000000000 43663117320281 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722245133/5000000000 : ℝ)^4931 ≤ (46425146599453/100000000000000 : ℝ)^3907 := by
    have hnat : (2722245133 : ℕ)^4931*100000000000000^3907 ≤ 46425146599453^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722245133 5000000000 46425146599453 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1601825069/10000000000 : ℝ), (2593107967/5000000000 : ℝ), (2722245133/5000000000 : ℝ)] ![(4955868030427/50000000000000 : ℝ), (43663117320281/100000000000000 : ℝ), (46425146599453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1601825069/10000000000 : ℝ)|^4931 ≤ (4955868030427/50000000000000 : ℝ)^3907
        have hw : |(-1601825069/10000000000 : ℝ)|=(1601825069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593107967/5000000000 : ℝ)|^4931 ≤ (43663117320281/100000000000000 : ℝ)^3907
        have hw : |(2593107967/5000000000 : ℝ)|=(2593107967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722245133/5000000000 : ℝ)|^4931 ≤ (46425146599453/100000000000000 : ℝ)^3907
        have hw : |(2722245133/5000000000 : ℝ)|=(2722245133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_5 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277159623/10000000000 : ℝ)*x 0 + (-738246729/5000000000 : ℝ)*x 1 + (5444490319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277159623/10000000000 : ℝ)^4931 ≤ (8926332953017/20000000000000 : ℝ)^3907 := by
    have hnat : (5277159623 : ℕ)^4931*20000000000000^3907 ≤ 8926332953017^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277159623 10000000000 8926332953017 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738246729/5000000000 : ℝ)^4931 ≤ (1788637608179/20000000000000 : ℝ)^3907 := by
    have hnat : (738246729 : ℕ)^4931*20000000000000^3907 ≤ 1788637608179^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738246729 5000000000 1788637608179 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444490319/10000000000 : ℝ)^4931 ≤ (5803143396229/12500000000000 : ℝ)^3907 := by
    have hnat : (5444490319 : ℕ)^4931*12500000000000^3907 ≤ 5803143396229^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444490319 10000000000 5803143396229 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277159623/10000000000 : ℝ), (-738246729/5000000000 : ℝ), (5444490319/10000000000 : ℝ)] ![(8926332953017/20000000000000 : ℝ), (1788637608179/20000000000000 : ℝ), (5803143396229/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277159623/10000000000 : ℝ)|^4931 ≤ (8926332953017/20000000000000 : ℝ)^3907
        have hw : |(5277159623/10000000000 : ℝ)|=(5277159623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-738246729/5000000000 : ℝ)|^4931 ≤ (1788637608179/20000000000000 : ℝ)^3907
        have hw : |(-738246729/5000000000 : ℝ)|=(738246729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444490319/10000000000 : ℝ)|^4931 ≤ (5803143396229/12500000000000 : ℝ)^3907
        have hw : |(5444490319/10000000000 : ℝ)|=(5444490319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_6 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319289907/2500000000 : ℝ)*x 0 + (2722245169/5000000000 : ℝ)*x 1 + (-59059737/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319289907/2500000000 : ℝ)^4931 ≤ (5578958102307/12500000000000 : ℝ)^3907 := by
    have hnat : (1319289907 : ℕ)^4931*12500000000000^3907 ≤ 5578958102307^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319289907 2500000000 5578958102307 12500000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722245169/5000000000 : ℝ)^4931 ≤ (11606286843577/25000000000000 : ℝ)^3907 := by
    have hnat : (2722245169 : ℕ)^4931*25000000000000^3907 ≤ 11606286843577^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722245169 5000000000 11606286843577 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59059737/400000000 : ℝ)^4931 ≤ (558949236789/6250000000000 : ℝ)^3907 := by
    have hnat : (59059737 : ℕ)^4931*6250000000000^3907 ≤ 558949236789^3907*400000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59059737 400000000 558949236789 6250000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319289907/2500000000 : ℝ), (2722245169/5000000000 : ℝ), (-59059737/400000000 : ℝ)] ![(5578958102307/12500000000000 : ℝ), (11606286843577/25000000000000 : ℝ), (558949236789/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319289907/2500000000 : ℝ)|^4931 ≤ (5578958102307/12500000000000 : ℝ)^3907
        have hw : |(1319289907/2500000000 : ℝ)|=(1319289907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722245169/5000000000 : ℝ)|^4931 ≤ (11606286843577/25000000000000 : ℝ)^3907
        have hw : |(2722245169/5000000000 : ℝ)|=(2722245169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59059737/400000000 : ℝ)|^4931 ≤ (558949236789/6250000000000 : ℝ)^3907
        have hw : |(-59059737/400000000 : ℝ)|=(59059737/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_s4_7 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167144711/400000000 : ℝ)*x 0 + (2261936831/5000000000 : ℝ)*x 1 + (963281789/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167144711/400000000 : ℝ)^4931 ≤ (16621786679357/50000000000000 : ℝ)^3907 := by
    have hnat : (167144711 : ℕ)^4931*50000000000000^3907 ≤ 16621786679357^3907*400000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167144711 400000000 16621786679357 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2261936831/5000000000 : ℝ)^4931 ≤ (36747004233591/100000000000000 : ℝ)^3907 := by
    have hnat : (2261936831 : ℕ)^4931*100000000000000^3907 ≤ 36747004233591^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261936831 5000000000 36747004233591 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963281789/2500000000 : ℝ)^4931 ≤ (3000942240013/10000000000000 : ℝ)^3907 := by
    have hnat : (963281789 : ℕ)^4931*10000000000000^3907 ≤ 3000942240013^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963281789 2500000000 3000942240013 10000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167144711/400000000 : ℝ), (2261936831/5000000000 : ℝ), (963281789/2500000000 : ℝ)] ![(16621786679357/50000000000000 : ℝ), (36747004233591/100000000000000 : ℝ), (3000942240013/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167144711/400000000 : ℝ)|^4931 ≤ (16621786679357/50000000000000 : ℝ)^3907
        have hw : |(167144711/400000000 : ℝ)|=(167144711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2261936831/5000000000 : ℝ)|^4931 ≤ (36747004233591/100000000000000 : ℝ)^3907
        have hw : |(2261936831/5000000000 : ℝ)|=(2261936831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963281789/2500000000 : ℝ)|^4931 ≤ (3000942240013/10000000000000 : ℝ)^3907
        have hw : |(963281789/2500000000 : ℝ)|=(963281789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1653_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8133/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5343/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8131/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8133/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8133/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8133/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8133/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8133/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8133/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5341/50000 : ℝ) ^ (4927/1024 : ℝ) ≤ (530003943215581/25000000000000000000 : ℝ) := by
    have hpowers : (5341/50000 : ℝ)^4927 ≤ (530003943215581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5341 : ℕ)^4927*25000000000000000000^1024 ≤ 530003943215581^1024*50000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5341 50000 530003943215581 25000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5341/50000 : ℝ)) (X := (530003943215581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8133/50000 : ℝ) ^ (4927/1024 : ℝ) ≤ (16034629499431819/100000000000000000000 : ℝ) := by
    have hpowers : (8133/50000 : ℝ)^4927 ≤ (16034629499431819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8133 : ℕ)^4927*100000000000000000000^1024 ≤ 16034629499431819^1024*50000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8133 50000 16034629499431819 100000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8133/50000 : ℝ)) (X := (16034629499431819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500530003943215581/12500000000000000000 : ℝ) ≤ (10000088120953693/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (12500530003943215581/12500000000000000000 : ℝ)^1024 ≤ (10000088120953693/10000000000000000 : ℝ)^4927 := by
      have hnat : (12500530003943215581 : ℕ)^1024*10000000000000000^4927 ≤ 10000088120953693^4927*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500530003943215581 12500000000000000000 10000088120953693 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000088120953693/10000000000000000 : ℝ)) (X := (12500530003943215581/12500000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018154645272294143/100000000000000000000 : ℝ) ≤ (10000377288819141/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (100018154645272294143/100000000000000000000 : ℝ)^1024 ≤ (10000377288819141/10000000000000000 : ℝ)^4927 := by
      have hnat : (100018154645272294143 : ℕ)^1024*10000000000000000^4927 ≤ 10000377288819141^4927*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018154645272294143 100000000000000000000 10000377288819141 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000377288819141/10000000000000000 : ℝ)) (X := (100018154645272294143/100000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016034629499431819/50000000000000000000 : ℝ) ≤ (10000666456684589/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (50016034629499431819/50000000000000000000 : ℝ)^1024 ≤ (10000666456684589/10000000000000000 : ℝ)^4927 := by
      have hnat : (50016034629499431819 : ℕ)^1024*10000000000000000^4927 ≤ 10000666456684589^4927*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016034629499431819 50000000000000000000 10000666456684589 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000666456684589/10000000000000000 : ℝ)) (X := (50016034629499431819/50000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(530003943215581/25000000000000000000 : ℝ) ≤ ((697928928564099883/698000000000000000 : ℝ)+2*(36145983181/69800000000000 : ℝ)*(5341/50000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (697928928564099883/698000000000000000 : ℝ)+2*(36145983181/69800000000000 : ℝ)*(5341/50000 : ℝ)=(10000088120953693/10000000000000000 : ℝ) by norm_num, show 1+2*(530003943215581/25000000000000000000 : ℝ)=(12500530003943215581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16034629499431819/100000000000000000000 : ℝ)+(530003943215581/25000000000000000000 : ℝ) ≤ ((697928928564099883/698000000000000000 : ℝ)+(36145983181/69800000000000 : ℝ)*((8133/50000 : ℝ)+(5341/50000 : ℝ)))^(4927/1024 : ℝ) := by
    rw [show (697928928564099883/698000000000000000 : ℝ)+(36145983181/69800000000000 : ℝ)*((8133/50000 : ℝ)+(5341/50000 : ℝ))=(10000377288819141/10000000000000000 : ℝ) by norm_num, show 1+(16034629499431819/100000000000000000000 : ℝ)+(530003943215581/25000000000000000000 : ℝ)=(100018154645272294143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16034629499431819/100000000000000000000 : ℝ) ≤ ((697928928564099883/698000000000000000 : ℝ)+2*(36145983181/69800000000000 : ℝ)*(8133/50000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (697928928564099883/698000000000000000 : ℝ)+2*(36145983181/69800000000000 : ℝ)*(8133/50000 : ℝ)=(10000666456684589/10000000000000000 : ℝ) by norm_num, show 1+2*(16034629499431819/100000000000000000000 : ℝ)=(50016034629499431819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (697928928564099883/698000000000000000 : ℝ)*(X 1 0+X 2 0)+(36145983181/69800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (5341/50000 : ℝ)) (hi := (8133/50000 : ℝ)) (c := (697928928564099883/698000000000000000 : ℝ)) (alpha := (36145983181/69800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (697928928564099883/698000000000000000 : ℝ)*(X 0 1+X 2 1)+(36145983181/69800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (5341/50000 : ℝ)) (hi := (8133/50000 : ℝ)) (c := (697928928564099883/698000000000000000 : ℝ)) (alpha := (36145983181/69800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (697928928564099883/698000000000000000 : ℝ)*(X 0 2+X 1 2)+(36145983181/69800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (5341/50000 : ℝ)) (hi := (8133/50000 : ℝ)) (c := (697928928564099883/698000000000000000 : ℝ)) (alpha := (36145983181/69800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-40044039/250000000 : ℝ)*X 0 0+(2723248171/5000000000 : ℝ)*X 0 1+(2592115311/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069449901/2000000000 : ℝ)*X 1 0+(-868376409/5000000000 : ℝ)*X 1 1+(5184230771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347249517/10000000000 : ℝ)*X 2 0+(2592115337/5000000000 : ℝ)*X 2 1+(-173675293/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1044613037/2500000000 : ℝ)*X 0 0+(38479173/100000000 : ℝ)*X 0 1+(4529029487/10000000000 : ℝ)*X 0 2+(1044613037/2500000000 : ℝ)*X 1 0+(38479173/100000000 : ℝ)*X 1 1+(4529029487/10000000000 : ℝ)*X 1 2+(1044613037/2500000000 : ℝ)*X 2 0+(38479173/100000000 : ℝ)*X 2 1+(4529029487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1601825069/10000000000 : ℝ)*X 0 0+(2593107967/5000000000 : ℝ)*X 0 1+(2722245133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277159623/10000000000 : ℝ)*X 1 0+(-738246729/5000000000 : ℝ)*X 1 1+(5444490319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319289907/2500000000 : ℝ)*X 2 0+(2722245169/5000000000 : ℝ)*X 2 1+(-59059737/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((167144711/400000000 : ℝ)*X 0 0+(2261936831/5000000000 : ℝ)*X 0 1+(963281789/2500000000 : ℝ)*X 0 2+(167144711/400000000 : ℝ)*X 1 0+(2261936831/5000000000 : ℝ)*X 1 1+(963281789/2500000000 : ℝ)*X 1 2+(167144711/400000000 : ℝ)*X 2 0+(2261936831/5000000000 : ℝ)*X 2 1+(963281789/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22406723519976172764491889/3490000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (555524273/50000000000000 : ℝ)*(base19) + (214885603/20000000000000 : ℝ)*(base23) + (206234909/100000000000000 : ℝ)*(upper3) + (24157461/100000000000000 : ℝ)*(upper4) + (43549629/50000000000000 : ℝ)*(upper5) + (264057891751761/10000000000000 : ℝ)*(major0) + (264057891751761/10000000000000 : ℝ)*(major1) + (264057891751761/10000000000000 : ℝ)*(major2) + (476617985025773/12500000000000 : ℝ)*(sp0) + (3812957586419/100000000000 : ℝ)*(sp1) + (953239405759883/25000000000000 : ℝ)*(sp2) + (146819235446941/10000000000000 : ℝ)*(sp3) + (7408630681/50000000000000 : ℝ)*(sp4) + (1642272359/25000000000000 : ℝ)*(sp7) + (1468198923558847/100000000000000 : ℝ)*(f.failure) + (1906479348733773/50000000000000 : ℝ)*(f.sum) + (1229231218397/349000000000000000000000000 : ℝ)*base66 + (47999067340086037/6980000000000000000000000000000 : ℝ)*base68 + (33131225910926037/6980000000000000000000000000000 : ℝ)*base70 + (2328380554153963/6980000000000000000000000000000 : ℝ)*base71 + (760502953827/349000000000000000000000000 : ℝ)*base74 + (46820623874273963/6980000000000000000000000000000 : ℝ)*base75 + (19214070532966037/6980000000000000000000000000000 : ℝ)*base78 + (45907046393446037/6980000000000000000000000000000 : ℝ)*base80 + (515754345567/349000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (85251719/10000000000000000000000 : ℝ)*base89 + (85251719/10000000000000000000000 : ℝ)*base91 + (85251719/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58536517931652564994603377/6980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (991128423/100000000000000 : ℝ)*(base19) + (59702881/5000000000000 : ℝ)*(base23) + (4799859/1562500000000 : ℝ)*(lower1) + (164839279/100000000000000 : ℝ)*(upper3) + (88610937/100000000000000 : ℝ)*(lower4) + (22131451/12500000000000 : ℝ)*(upper5) + (536271057198927/20000000000000 : ℝ)*(major0) + (536271057198927/20000000000000 : ℝ)*(major1) + (536271057198927/20000000000000 : ℝ)*(major2) + (1180064377/50000000000000 : ℝ)*(sp2) + (38718391359501/1000000000000 : ℝ)*(sp4) + (1935919072410839/50000000000000 : ℝ)*(sp5) + (1935917790881863/50000000000000 : ℝ)*(sp6) + (1490871156495133/100000000000000 : ℝ)*(sp7) + (1490871156495133/100000000000000 : ℝ)*(f.failure) + (38718391359501/1000000000000 : ℝ)*(f.sum) + (65384188637/698000000000000000000000000 : ℝ)*base65 + (291883758470135541/13960000000000000000000000000000 : ℝ)*base67 + (38522630958215541/13960000000000000000000000000000 : ℝ)*base69 + (596772373210944459/13960000000000000000000000000000 : ℝ)*base72 + (1374432690431/698000000000000000000000000 : ℝ)*base73 + (739616266242504459/13960000000000000000000000000000 : ℝ)*base76 + (72055996195135541/13960000000000000000000000000000 : ℝ)*base77 + (76436479341495541/13960000000000000000000000000000 : ℝ)*base79 + (1730673675857/698000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (37125259/10000000000000000000000 : ℝ)*base90 + (37125259/10000000000000000000000 : ℝ)*base92 + (37125259/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1653_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8133/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5343/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1653_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1653_box_0 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-168106293/1250000000 : ℝ)*x 0 + (2703663761/5000000000 : ℝ)*x 1 + (5407328453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168106293/1250000000 : ℝ)^4931 ≤ (7948861160461/100000000000000 : ℝ)^3907 := by
    have hnat : (168106293 : ℕ)^4931*100000000000000^3907 ≤ 7948861160461^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168106293 1250000000 7948861160461 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703663761/5000000000 : ℝ)^4931 ≤ (23012782205553/50000000000000 : ℝ)^3907 := by
    have hnat : (2703663761 : ℕ)^4931*50000000000000^3907 ≤ 23012782205553^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703663761 5000000000 23012782205553 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407328453/10000000000 : ℝ)^4931 ≤ (9205114882487/20000000000000 : ℝ)^3907 := by
    have hnat : (5407328453 : ℕ)^4931*20000000000000^3907 ≤ 9205114882487^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407328453 10000000000 9205114882487 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168106293/1250000000 : ℝ), (2703663761/5000000000 : ℝ), (5407328453/10000000000 : ℝ)] ![(7948861160461/100000000000000 : ℝ), (23012782205553/50000000000000 : ℝ), (9205114882487/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168106293/1250000000 : ℝ)|^4931 ≤ (7948861160461/100000000000000 : ℝ)^3907
        have hw : |(-168106293/1250000000 : ℝ)|=(168106293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703663761/5000000000 : ℝ)|^4931 ≤ (23012782205553/50000000000000 : ℝ)^3907
        have hw : |(2703663761/5000000000 : ℝ)|=(2703663761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407328453/10000000000 : ℝ)|^4931 ≤ (9205114882487/20000000000000 : ℝ)^3907
        have hw : |(5407328453/10000000000 : ℝ)|=(5407328453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_1 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050207219/2000000000 : ℝ)*x 0 + (-1564537949/10000000000 : ℝ)*x 1 + (2703663909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050207219/2000000000 : ℝ)^4931 ≤ (44352998688163/100000000000000 : ℝ)^3907 := by
    have hnat : (1050207219 : ℕ)^4931*100000000000000^3907 ≤ 44352998688163^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050207219 2000000000 44352998688163 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564537949/10000000000 : ℝ)^4931 ≤ (9621433712021/100000000000000 : ℝ)^3907 := by
    have hnat : (1564537949 : ℕ)^4931*100000000000000^3907 ≤ 9621433712021^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564537949 10000000000 9621433712021 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703663909/5000000000 : ℝ)^4931 ≤ (9205113518181/20000000000000 : ℝ)^3907 := by
    have hnat : (2703663909 : ℕ)^4931*20000000000000^3907 ≤ 9205113518181^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703663909 5000000000 9205113518181 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050207219/2000000000 : ℝ), (-1564537949/10000000000 : ℝ), (2703663909/5000000000 : ℝ)] ![(44352998688163/100000000000000 : ℝ), (9621433712021/100000000000000 : ℝ), (9205113518181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050207219/2000000000 : ℝ)|^4931 ≤ (44352998688163/100000000000000 : ℝ)^3907
        have hw : |(1050207219/2000000000 : ℝ)|=(1050207219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1564537949/10000000000 : ℝ)|^4931 ≤ (9621433712021/100000000000000 : ℝ)^3907
        have hw : |(-1564537949/10000000000 : ℝ)|=(1564537949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703663909/5000000000 : ℝ)|^4931 ≤ (9205113518181/20000000000000 : ℝ)^3907
        have hw : |(2703663909/5000000000 : ℝ)|=(2703663909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_2 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625518021/5000000000 : ℝ)*x 0 + (5407328649/10000000000 : ℝ)*x 1 + (-195567109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625518021/5000000000 : ℝ)^4931 ≤ (44352998123167/100000000000000 : ℝ)^3907 := by
    have hnat : (2625518021 : ℕ)^4931*100000000000000^3907 ≤ 44352998123167^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625518021 5000000000 44352998123167 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407328649/10000000000 : ℝ)^4931 ≤ (23012788258989/50000000000000 : ℝ)^3907 := by
    have hnat : (5407328649 : ℕ)^4931*50000000000000^3907 ≤ 23012788258989^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407328649 10000000000 23012788258989 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195567109/1250000000 : ℝ)^4931 ≤ (4810712676447/50000000000000 : ℝ)^3907 := by
    have hnat : (195567109 : ℕ)^4931*50000000000000^3907 ≤ 4810712676447^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195567109 1250000000 4810712676447 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625518021/5000000000 : ℝ), (5407328649/10000000000 : ℝ), (-195567109/1250000000 : ℝ)] ![(44352998123167/100000000000000 : ℝ), (23012788258989/50000000000000 : ℝ), (4810712676447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625518021/5000000000 : ℝ)|^4931 ≤ (44352998123167/100000000000000 : ℝ)^3907
        have hw : |(2625518021/5000000000 : ℝ)|=(2625518021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407328649/10000000000 : ℝ)|^4931 ≤ (23012788258989/50000000000000 : ℝ)^3907
        have hw : |(5407328649/10000000000 : ℝ)|=(5407328649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195567109/1250000000 : ℝ)|^4931 ≤ (4810712676447/50000000000000 : ℝ)^3907
        have hw : |(-195567109/1250000000 : ℝ)|=(195567109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_3 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2227527613/5000000000 : ℝ)*x 0 + (4052124191/10000000000 : ℝ)*x 1 + (4052122757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2227527613/5000000000 : ℝ)^4931 ≤ (36042898381093/100000000000000 : ℝ)^3907 := by
    have hnat : (2227527613 : ℕ)^4931*100000000000000^3907 ≤ 36042898381093^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227527613 5000000000 36042898381093 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4052124191/10000000000 : ℝ)^4931 ≤ (31978557946231/100000000000000 : ℝ)^3907 := by
    have hnat : (4052124191 : ℕ)^4931*100000000000000^3907 ≤ 31978557946231^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052124191 10000000000 31978557946231 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4052122757/10000000000 : ℝ)^4931 ≤ (7994635915829/25000000000000 : ℝ)^3907 := by
    have hnat : (4052122757 : ℕ)^4931*25000000000000^3907 ≤ 7994635915829^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052122757 10000000000 7994635915829 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2227527613/5000000000 : ℝ), (4052124191/10000000000 : ℝ), (4052122757/10000000000 : ℝ)] ![(36042898381093/100000000000000 : ℝ), (31978557946231/100000000000000 : ℝ), (7994635915829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2227527613/5000000000 : ℝ)|^4931 ≤ (36042898381093/100000000000000 : ℝ)^3907
        have hw : |(2227527613/5000000000 : ℝ)|=(2227527613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4052124191/10000000000 : ℝ)|^4931 ≤ (31978557946231/100000000000000 : ℝ)^3907
        have hw : |(4052124191/10000000000 : ℝ)|=(4052124191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4052122757/10000000000 : ℝ)|^4931 ≤ (7994635915829/25000000000000 : ℝ)^3907
        have hw : |(4052122757/10000000000 : ℝ)|=(4052122757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_4 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-467315597/2500000000 : ℝ)*x 0 + (5215816227/10000000000 : ℝ)*x 1 + (1303954141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467315597/2500000000 : ℝ)^4931 ≤ (12044246882689/100000000000000 : ℝ)^3907 := by
    have hnat : (467315597 : ℕ)^4931*100000000000000^3907 ≤ 12044246882689^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467315597 2500000000 12044246882689 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215816227/10000000000 : ℝ)^4931 ≤ (10994468689107/25000000000000 : ℝ)^3907 := by
    have hnat : (5215816227 : ℕ)^4931*25000000000000^3907 ≤ 10994468689107^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215816227 10000000000 10994468689107 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303954141/2500000000 : ℝ)^4931 ≤ (2198893917131/5000000000000 : ℝ)^3907 := by
    have hnat : (1303954141 : ℕ)^4931*5000000000000^3907 ≤ 2198893917131^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303954141 2500000000 2198893917131 5000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467315597/2500000000 : ℝ), (5215816227/10000000000 : ℝ), (1303954141/2500000000 : ℝ)] ![(12044246882689/100000000000000 : ℝ), (10994468689107/25000000000000 : ℝ), (2198893917131/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467315597/2500000000 : ℝ)|^4931 ≤ (12044246882689/100000000000000 : ℝ)^3907
        have hw : |(-467315597/2500000000 : ℝ)|=(467315597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215816227/10000000000 : ℝ)|^4931 ≤ (10994468689107/25000000000000 : ℝ)^3907
        have hw : |(5215816227/10000000000 : ℝ)|=(5215816227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303954141/2500000000 : ℝ)|^4931 ≤ (2198893917131/5000000000000 : ℝ)^3907
        have hw : |(1303954141/2500000000 : ℝ)|=(1303954141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_5 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382433163/10000000000 : ℝ)*x 0 + (-329349193/2000000000 : ℝ)*x 1 + (5215816219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382433163/10000000000 : ℝ)^4931 ≤ (45758296638981/100000000000000 : ℝ)^3907 := by
    have hnat : (5382433163 : ℕ)^4931*100000000000000^3907 ≤ 45758296638981^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382433163 10000000000 45758296638981 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329349193/2000000000 : ℝ)^4931 ≤ (5131914340559/50000000000000 : ℝ)^3907 := by
    have hnat : (329349193 : ℕ)^4931*50000000000000^3907 ≤ 5131914340559^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329349193 2000000000 5131914340559 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215816219/10000000000 : ℝ)^4931 ≤ (687154291739/1562500000000 : ℝ)^3907 := by
    have hnat : (5215816219 : ℕ)^4931*1562500000000^3907 ≤ 687154291739^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215816219 10000000000 687154291739 1562500000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382433163/10000000000 : ℝ), (-329349193/2000000000 : ℝ), (5215816219/10000000000 : ℝ)] ![(45758296638981/100000000000000 : ℝ), (5131914340559/50000000000000 : ℝ), (687154291739/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382433163/10000000000 : ℝ)|^4931 ≤ (45758296638981/100000000000000 : ℝ)^3907
        have hw : |(5382433163/10000000000 : ℝ)|=(5382433163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329349193/2000000000 : ℝ)|^4931 ≤ (5131914340559/50000000000000 : ℝ)^3907
        have hw : |(-329349193/2000000000 : ℝ)|=(329349193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215816219/10000000000 : ℝ)|^4931 ≤ (687154291739/1562500000000 : ℝ)^3907
        have hw : |(5215816219/10000000000 : ℝ)|=(5215816219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_6 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672804113/1250000000 : ℝ)*x 0 + (2607908283/5000000000 : ℝ)*x 1 + (-1646745847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672804113/1250000000 : ℝ)^4931 ≤ (45758293860019/100000000000000 : ℝ)^3907 := by
    have hnat : (672804113 : ℕ)^4931*100000000000000^3907 ≤ 45758293860019^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672804113 1250000000 45758293860019 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607908283/5000000000 : ℝ)^4931 ≤ (43977878363903/100000000000000 : ℝ)^3907 := by
    have hnat : (2607908283 : ℕ)^4931*100000000000000^3907 ≤ 43977878363903^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607908283 5000000000 43977878363903 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1646745847/10000000000 : ℝ)^4931 ≤ (10263827752887/100000000000000 : ℝ)^3907 := by
    have hnat : (1646745847 : ℕ)^4931*100000000000000^3907 ≤ 10263827752887^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1646745847 10000000000 10263827752887 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672804113/1250000000 : ℝ), (2607908283/5000000000 : ℝ), (-1646745847/10000000000 : ℝ)] ![(45758293860019/100000000000000 : ℝ), (43977878363903/100000000000000 : ℝ), (10263827752887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672804113/1250000000 : ℝ)|^4931 ≤ (45758293860019/100000000000000 : ℝ)^3907
        have hw : |(672804113/1250000000 : ℝ)|=(672804113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607908283/5000000000 : ℝ)|^4931 ≤ (43977878363903/100000000000000 : ℝ)^3907
        have hw : |(2607908283/5000000000 : ℝ)|=(2607908283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1646745847/10000000000 : ℝ)|^4931 ≤ (10263827752887/100000000000000 : ℝ)^3907
        have hw : |(-1646745847/10000000000 : ℝ)|=(1646745847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_7 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (486911259/1250000000 : ℝ)*x 0 + (2165841133/5000000000 : ℝ)*x 1 + (2165841199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (486911259/1250000000 : ℝ)^4931 ≤ (15212229876479/50000000000000 : ℝ)^3907 := by
    have hnat : (486911259 : ℕ)^4931*50000000000000^3907 ≤ 15212229876479^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486911259 1250000000 15212229876479 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2165841133/5000000000 : ℝ)^4931 ≤ (1739388472563/5000000000000 : ℝ)^3907 := by
    have hnat : (2165841133 : ℕ)^4931*5000000000000^3907 ≤ 1739388472563^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165841133 5000000000 1739388472563 5000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165841199/5000000000 : ℝ)^4931 ≤ (8696942697299/25000000000000 : ℝ)^3907 := by
    have hnat : (2165841199 : ℕ)^4931*25000000000000^3907 ≤ 8696942697299^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165841199 5000000000 8696942697299 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(486911259/1250000000 : ℝ), (2165841133/5000000000 : ℝ), (2165841199/5000000000 : ℝ)] ![(15212229876479/50000000000000 : ℝ), (1739388472563/5000000000000 : ℝ), (8696942697299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(486911259/1250000000 : ℝ)|^4931 ≤ (15212229876479/50000000000000 : ℝ)^3907
        have hw : |(486911259/1250000000 : ℝ)|=(486911259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2165841133/5000000000 : ℝ)|^4931 ≤ (1739388472563/5000000000000 : ℝ)^3907
        have hw : |(2165841133/5000000000 : ℝ)|=(2165841133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2165841199/5000000000 : ℝ)|^4931 ≤ (8696942697299/25000000000000 : ℝ)^3907
        have hw : |(2165841199/5000000000 : ℝ)|=(2165841199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_8 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1757376507/10000000000 : ℝ)*x 0 + (1269503161/2500000000 : ℝ)*x 1 + (679593323/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757376507/10000000000 : ℝ)^4931 ≤ (11141628119779/100000000000000 : ℝ)^3907 := by
    have hnat : (1757376507 : ℕ)^4931*100000000000000^3907 ≤ 11141628119779^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757376507 10000000000 11141628119779 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269503161/2500000000 : ℝ)^4931 ≤ (42516546200597/100000000000000 : ℝ)^3907 := by
    have hnat : (1269503161 : ℕ)^4931*100000000000000^3907 ≤ 42516546200597^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269503161 2500000000 42516546200597 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679593323/1250000000 : ℝ)^4931 ≤ (46341825656451/100000000000000 : ℝ)^3907 := by
    have hnat : (679593323 : ℕ)^4931*100000000000000^3907 ≤ 46341825656451^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679593323 1250000000 46341825656451 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1757376507/10000000000 : ℝ), (1269503161/2500000000 : ℝ), (679593323/1250000000 : ℝ)] ![(11141628119779/100000000000000 : ℝ), (42516546200597/100000000000000 : ℝ), (46341825656451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1757376507/10000000000 : ℝ)|^4931 ≤ (11141628119779/100000000000000 : ℝ)^3907
        have hw : |(-1757376507/10000000000 : ℝ)|=(1757376507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269503161/2500000000 : ℝ)|^4931 ≤ (42516546200597/100000000000000 : ℝ)^3907
        have hw : |(1269503161/2500000000 : ℝ)|=(1269503161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679593323/1250000000 : ℝ)|^4931 ≤ (46341825656451/100000000000000 : ℝ)^3907
        have hw : |(679593323/1250000000 : ℝ)|=(679593323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_9 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230853357/10000000000 : ℝ)*x 0 + (-775741357/5000000000 : ℝ)*x 1 + (5436747017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230853357/10000000000 : ℝ)^4931 ≤ (44137953045789/100000000000000 : ℝ)^3907 := by
    have hnat : (5230853357 : ℕ)^4931*100000000000000^3907 ≤ 44137953045789^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230853357 10000000000 44137953045789 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775741357/5000000000 : ℝ)^4931 ≤ (4760108313219/50000000000000 : ℝ)^3907 := by
    have hnat : (775741357 : ℕ)^4931*50000000000000^3907 ≤ 4760108313219^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775741357 5000000000 4760108313219 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436747017/10000000000 : ℝ)^4931 ≤ (23170915157301/50000000000000 : ℝ)^3907 := by
    have hnat : (5436747017 : ℕ)^4931*50000000000000^3907 ≤ 23170915157301^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436747017 10000000000 23170915157301 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230853357/10000000000 : ℝ), (-775741357/5000000000 : ℝ), (5436747017/10000000000 : ℝ)] ![(44137953045789/100000000000000 : ℝ), (4760108313219/50000000000000 : ℝ), (23170915157301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230853357/10000000000 : ℝ)|^4931 ≤ (44137953045789/100000000000000 : ℝ)^3907
        have hw : |(5230853357/10000000000 : ℝ)|=(5230853357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-775741357/5000000000 : ℝ)|^4931 ≤ (4760108313219/50000000000000 : ℝ)^3907
        have hw : |(-775741357/5000000000 : ℝ)|=(775741357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436747017/10000000000 : ℝ)|^4931 ≤ (23170915157301/50000000000000 : ℝ)^3907
        have hw : |(5436747017/10000000000 : ℝ)|=(5436747017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_10 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230853503/10000000000 : ℝ)*x 0 + (2718373539/5000000000 : ℝ)*x 1 + (-1551482429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230853503/10000000000 : ℝ)^4931 ≤ (44137954600623/100000000000000 : ℝ)^3907 := by
    have hnat : (5230853503 : ℕ)^4931*100000000000000^3907 ≤ 44137954600623^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230853503 10000000000 44137954600623 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718373539/5000000000 : ℝ)^4931 ≤ (46341830970831/100000000000000 : ℝ)^3907 := by
    have hnat : (2718373539 : ℕ)^4931*100000000000000^3907 ≤ 46341830970831^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718373539 5000000000 46341830970831 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1551482429/10000000000 : ℝ)^4931 ≤ (1904042883853/20000000000000 : ℝ)^3907 := by
    have hnat : (1551482429 : ℕ)^4931*20000000000000^3907 ≤ 1904042883853^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551482429 10000000000 1904042883853 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230853503/10000000000 : ℝ), (2718373539/5000000000 : ℝ), (-1551482429/10000000000 : ℝ)] ![(44137954600623/100000000000000 : ℝ), (46341830970831/100000000000000 : ℝ), (1904042883853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230853503/10000000000 : ℝ)|^4931 ≤ (44137954600623/100000000000000 : ℝ)^3907
        have hw : |(5230853503/10000000000 : ℝ)|=(5230853503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718373539/5000000000 : ℝ)|^4931 ≤ (46341830970831/100000000000000 : ℝ)^3907
        have hw : |(2718373539/5000000000 : ℝ)|=(2718373539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1551482429/10000000000 : ℝ)|^4931 ≤ (1904042883853/20000000000000 : ℝ)^3907
        have hw : |(-1551482429/10000000000 : ℝ)|=(1551482429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_11 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1134666859/2500000000 : ℝ)*x 0 + (2004550503/5000000000 : ℝ)*x 1 + (4009100389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134666859/2500000000 : ℝ)^4931 ≤ (36898733014171/100000000000000 : ℝ)^3907 := by
    have hnat : (1134666859 : ℕ)^4931*100000000000000^3907 ≤ 36898733014171^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134666859 2500000000 36898733014171 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004550503/5000000000 : ℝ)^4931 ≤ (1262025462087/4000000000000 : ℝ)^3907 := by
    have hnat : (2004550503 : ℕ)^4931*4000000000000^3907 ≤ 1262025462087^3907*5000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004550503 5000000000 1262025462087 4000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4009100389/10000000000 : ℝ)^4931 ≤ (15775315211953/50000000000000 : ℝ)^3907 := by
    have hnat : (4009100389 : ℕ)^4931*50000000000000^3907 ≤ 15775315211953^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009100389 10000000000 15775315211953 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1134666859/2500000000 : ℝ), (2004550503/5000000000 : ℝ), (4009100389/10000000000 : ℝ)] ![(36898733014171/100000000000000 : ℝ), (1262025462087/4000000000000 : ℝ), (15775315211953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1134666859/2500000000 : ℝ)|^4931 ≤ (36898733014171/100000000000000 : ℝ)^3907
        have hw : |(1134666859/2500000000 : ℝ)|=(1134666859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004550503/5000000000 : ℝ)|^4931 ≤ (1262025462087/4000000000000 : ℝ)^3907
        have hw : |(2004550503/5000000000 : ℝ)|=(2004550503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4009100389/10000000000 : ℝ)|^4931 ≤ (15775315211953/50000000000000 : ℝ)^3907
        have hw : |(4009100389/10000000000 : ℝ)|=(4009100389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_12 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-181866937/1250000000 : ℝ)*x 0 + (692485997/1250000000 : ℝ)*x 1 + (1299000941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181866937/1250000000 : ℝ)^4931 ≤ (8778703400259/100000000000000 : ℝ)^3907 := by
    have hnat : (181866937 : ℕ)^4931*100000000000000^3907 ≤ 8778703400259^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181866937 1250000000 8778703400259 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692485997/1250000000 : ℝ)^4931 ≤ (23727075724649/50000000000000 : ℝ)^3907 := by
    have hnat : (692485997 : ℕ)^4931*50000000000000^3907 ≤ 23727075724649^3907*1250000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692485997 1250000000 23727075724649 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299000941/2500000000 : ℝ)^4931 ≤ (1367723285653/3125000000000 : ℝ)^3907 := by
    have hnat : (1299000941 : ℕ)^4931*3125000000000^3907 ≤ 1367723285653^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299000941 2500000000 1367723285653 3125000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181866937/1250000000 : ℝ), (692485997/1250000000 : ℝ), (1299000941/2500000000 : ℝ)] ![(8778703400259/100000000000000 : ℝ), (23727075724649/50000000000000 : ℝ), (1367723285653/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181866937/1250000000 : ℝ)|^4931 ≤ (8778703400259/100000000000000 : ℝ)^3907
        have hw : |(-181866937/1250000000 : ℝ)|=(181866937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692485997/1250000000 : ℝ)|^4931 ≤ (23727075724649/50000000000000 : ℝ)^3907
        have hw : |(692485997/1250000000 : ℝ)|=(692485997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299000941/2500000000 : ℝ)|^4931 ≤ (1367723285653/3125000000000 : ℝ)^3907
        have hw : |(1299000941/2500000000 : ℝ)|=(1299000941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_13 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396036119/10000000000 : ℝ)*x 0 + (-51717767/312500000 : ℝ)*x 1 + (5196004053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396036119/10000000000 : ℝ)^4931 ≤ (9180859795409/20000000000000 : ℝ)^3907 := by
    have hnat : (5396036119 : ℕ)^4931*20000000000000^3907 ≤ 9180859795409^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396036119 10000000000 9180859795409 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51717767/312500000 : ℝ)^4931 ≤ (2582138200887/25000000000000 : ℝ)^3907 := by
    have hnat : (51717767 : ℕ)^4931*25000000000000^3907 ≤ 2582138200887^3907*312500000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51717767 312500000 2582138200887 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5196004053/10000000000 : ℝ)^4931 ≤ (10941787053307/25000000000000 : ℝ)^3907 := by
    have hnat : (5196004053 : ℕ)^4931*25000000000000^3907 ≤ 10941787053307^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196004053 10000000000 10941787053307 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396036119/10000000000 : ℝ), (-51717767/312500000 : ℝ), (5196004053/10000000000 : ℝ)] ![(9180859795409/20000000000000 : ℝ), (2582138200887/25000000000000 : ℝ), (10941787053307/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396036119/10000000000 : ℝ)|^4931 ≤ (9180859795409/20000000000000 : ℝ)^3907
        have hw : |(5396036119/10000000000 : ℝ)|=(5396036119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51717767/312500000 : ℝ)|^4931 ≤ (2582138200887/25000000000000 : ℝ)^3907
        have hw : |(-51717767/312500000 : ℝ)|=(51717767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5196004053/10000000000 : ℝ)|^4931 ≤ (10941787053307/25000000000000 : ℝ)^3907
        have hw : |(5196004053/10000000000 : ℝ)|=(5196004053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_14 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215841461/400000000 : ℝ)*x 0 + (1039200689/2000000000 : ℝ)*x 1 + (-1654968809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215841461/400000000 : ℝ)^4931 ≤ (22952151668069/50000000000000 : ℝ)^3907 := by
    have hnat : (215841461 : ℕ)^4931*50000000000000^3907 ≤ 22952151668069^3907*400000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215841461 400000000 22952151668069 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039200689/2000000000 : ℝ)^4931 ≤ (10941785437409/25000000000000 : ℝ)^3907 := by
    have hnat : (1039200689 : ℕ)^4931*25000000000000^3907 ≤ 10941785437409^3907*2000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039200689 2000000000 10941785437409 25000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1654968809/10000000000 : ℝ)^4931 ≤ (516427744543/5000000000000 : ℝ)^3907 := by
    have hnat : (1654968809 : ℕ)^4931*5000000000000^3907 ≤ 516427744543^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1654968809 10000000000 516427744543 5000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215841461/400000000 : ℝ), (1039200689/2000000000 : ℝ), (-1654968809/10000000000 : ℝ)] ![(22952151668069/50000000000000 : ℝ), (10941785437409/25000000000000 : ℝ), (516427744543/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215841461/400000000 : ℝ)|^4931 ≤ (22952151668069/50000000000000 : ℝ)^3907
        have hw : |(215841461/400000000 : ℝ)|=(215841461/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039200689/2000000000 : ℝ)|^4931 ≤ (10941785437409/25000000000000 : ℝ)^3907
        have hw : |(1039200689/2000000000 : ℝ)|=(1039200689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1654968809/10000000000 : ℝ)|^4931 ≤ (516427744543/5000000000000 : ℝ)^3907
        have hw : |(-1654968809/10000000000 : ℝ)|=(1654968809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1653_box_15 (p : ℝ) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3835751919/10000000000 : ℝ)*x 0 + (1090137847/2500000000 : ℝ)*x 1 + (4360550493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3835751919/10000000000 : ℝ)^4931 ≤ (14919365897097/50000000000000 : ℝ)^3907 := by
    have hnat : (3835751919 : ℕ)^4931*50000000000000^3907 ≤ 14919365897097^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3835751919 10000000000 14919365897097 50000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090137847/2500000000 : ℝ)^4931 ≤ (7016127726977/20000000000000 : ℝ)^3907 := by
    have hnat : (1090137847 : ℕ)^4931*20000000000000^3907 ≤ 7016127726977^3907*2500000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090137847 2500000000 7016127726977 20000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4360550493/10000000000 : ℝ)^4931 ≤ (35080629547463/100000000000000 : ℝ)^3907 := by
    have hnat : (4360550493 : ℕ)^4931*100000000000000^3907 ≤ 35080629547463^3907*10000000000^4931 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360550493 10000000000 35080629547463 100000000000000 4931 3907 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4931/1024 : ℝ)) 4931 3907 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3835751919/10000000000 : ℝ), (1090137847/2500000000 : ℝ), (4360550493/10000000000 : ℝ)] ![(14919365897097/50000000000000 : ℝ), (7016127726977/20000000000000 : ℝ), (35080629547463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3835751919/10000000000 : ℝ)|^4931 ≤ (14919365897097/50000000000000 : ℝ)^3907
        have hw : |(3835751919/10000000000 : ℝ)|=(3835751919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090137847/2500000000 : ℝ)|^4931 ≤ (7016127726977/20000000000000 : ℝ)^3907
        have hw : |(1090137847/2500000000 : ℝ)|=(1090137847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4360550493/10000000000 : ℝ)|^4931 ≤ (35080629547463/100000000000000 : ℝ)^3907
        have hw : |(4360550493/10000000000 : ℝ)|=(4360550493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1653_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5343/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1627/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29329/50000 : ℝ) ∧ (81251/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88253/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8131/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5343/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8131/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5343/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8131/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5343/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8131/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5343/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8131/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5343/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8131/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5343/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5343/50000 : ℝ) ^ (4927/1024 : ℝ) ≤ (2123838198464177/100000000000000000000 : ℝ) := by
    have hpowers : (5343/50000 : ℝ)^4927 ≤ (2123838198464177/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5343 : ℕ)^4927*100000000000000000000^1024 ≤ 2123838198464177^1024*50000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5343 50000 2123838198464177 100000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5343/50000 : ℝ)) (X := (2123838198464177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8131/50000 : ℝ) ^ (4927/1024 : ℝ) ≤ (8007833027444621/50000000000000000000 : ℝ) := by
    have hpowers : (8131/50000 : ℝ)^4927 ≤ (8007833027444621/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8131 : ℕ)^4927*50000000000000000000^1024 ≤ 8007833027444621^1024*50000^4927 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8131 50000 8007833027444621 50000000000000000000 4927 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8131/50000 : ℝ)) (X := (8007833027444621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002123838198464177/50000000000000000000 : ℝ) ≤ (2000017655966929/2000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (50002123838198464177/50000000000000000000 : ℝ)^1024 ≤ (2000017655966929/2000000000000000 : ℝ)^4927 := by
      have hnat : (50002123838198464177 : ℕ)^1024*2000000000000000^4927 ≤ 2000017655966929^4927*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002123838198464177 50000000000000000000 2000017655966929 2000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000017655966929/2000000000000000 : ℝ)) (X := (50002123838198464177/50000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018139504253353419/100000000000000000000 : ℝ) ≤ (10000376974181939/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (100018139504253353419/100000000000000000000 : ℝ)^1024 ≤ (10000376974181939/10000000000000000 : ℝ)^4927 := by
      have hnat : (100018139504253353419 : ℕ)^1024*10000000000000000^4927 ≤ 10000376974181939^4927*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018139504253353419 100000000000000000000 10000376974181939 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000376974181939/10000000000000000 : ℝ)) (X := (100018139504253353419/100000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008007833027444621/25000000000000000000 : ℝ) ≤ (10000665668529233/10000000000000000 : ℝ) ^ (4927/1024 : ℝ) := by
    have hpowers : (25008007833027444621/25000000000000000000 : ℝ)^1024 ≤ (10000665668529233/10000000000000000 : ℝ)^4927 := by
      have hnat : (25008007833027444621 : ℕ)^1024*10000000000000000^4927 ≤ 10000665668529233^4927*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008007833027444621 25000000000000000000 10000665668529233 10000000000000000 1024 4927 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665668529233/10000000000000000 : ℝ)) (X := (25008007833027444621/25000000000000000000 : ℝ)) (by norm_num) 4927 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2123838198464177/100000000000000000000 : ℝ) ≤ ((1742322571023987911/1742500000000000000 : ℝ)+2*(144347173647/278800000000000 : ℝ)*(5343/50000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (1742322571023987911/1742500000000000000 : ℝ)+2*(144347173647/278800000000000 : ℝ)*(5343/50000 : ℝ)=(2000017655966929/2000000000000000 : ℝ) by norm_num, show 1+2*(2123838198464177/100000000000000000000 : ℝ)=(50002123838198464177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8007833027444621/50000000000000000000 : ℝ)+(2123838198464177/100000000000000000000 : ℝ) ≤ ((1742322571023987911/1742500000000000000 : ℝ)+(144347173647/278800000000000 : ℝ)*((8131/50000 : ℝ)+(5343/50000 : ℝ)))^(4927/1024 : ℝ) := by
    rw [show (1742322571023987911/1742500000000000000 : ℝ)+(144347173647/278800000000000 : ℝ)*((8131/50000 : ℝ)+(5343/50000 : ℝ))=(10000376974181939/10000000000000000 : ℝ) by norm_num, show 1+(8007833027444621/50000000000000000000 : ℝ)+(2123838198464177/100000000000000000000 : ℝ)=(100018139504253353419/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8007833027444621/50000000000000000000 : ℝ) ≤ ((1742322571023987911/1742500000000000000 : ℝ)+2*(144347173647/278800000000000 : ℝ)*(8131/50000 : ℝ))^(4927/1024 : ℝ) := by
    rw [show (1742322571023987911/1742500000000000000 : ℝ)+2*(144347173647/278800000000000 : ℝ)*(8131/50000 : ℝ)=(10000665668529233/10000000000000000 : ℝ) by norm_num, show 1+2*(8007833027444621/50000000000000000000 : ℝ)=(25008007833027444621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1742322571023987911/1742500000000000000 : ℝ)*(X 1 0+X 2 0)+(144347173647/278800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (5343/50000 : ℝ)) (hi := (8131/50000 : ℝ)) (c := (1742322571023987911/1742500000000000000 : ℝ)) (alpha := (144347173647/278800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1742322571023987911/1742500000000000000 : ℝ)*(X 0 1+X 2 1)+(144347173647/278800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (5343/50000 : ℝ)) (hi := (8131/50000 : ℝ)) (c := (1742322571023987911/1742500000000000000 : ℝ)) (alpha := (144347173647/278800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1742322571023987911/1742500000000000000 : ℝ)*(X 0 2+X 1 2)+(144347173647/278800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4927/1024 : ℝ)) (lo := (5343/50000 : ℝ)) (hi := (8131/50000 : ℝ)) (c := (1742322571023987911/1742500000000000000 : ℝ)) (alpha := (144347173647/278800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-168106293/1250000000 : ℝ)*X 0 0+(2703663761/5000000000 : ℝ)*X 0 1+(5407328453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1050207219/2000000000 : ℝ)*X 1 0+(-1564537949/10000000000 : ℝ)*X 1 1+(2703663909/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625518021/5000000000 : ℝ)*X 2 0+(5407328649/10000000000 : ℝ)*X 2 1+(-195567109/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2227527613/5000000000 : ℝ)*X 0 0+(4052124191/10000000000 : ℝ)*X 0 1+(4052122757/10000000000 : ℝ)*X 0 2+(2227527613/5000000000 : ℝ)*X 1 0+(4052124191/10000000000 : ℝ)*X 1 1+(4052122757/10000000000 : ℝ)*X 1 2+(2227527613/5000000000 : ℝ)*X 2 0+(4052124191/10000000000 : ℝ)*X 2 1+(4052122757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467315597/2500000000 : ℝ)*X 0 0+(5215816227/10000000000 : ℝ)*X 0 1+(1303954141/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5382433163/10000000000 : ℝ)*X 1 0+(-329349193/2000000000 : ℝ)*X 1 1+(5215816219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672804113/1250000000 : ℝ)*X 2 0+(2607908283/5000000000 : ℝ)*X 2 1+(-1646745847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((486911259/1250000000 : ℝ)*X 0 0+(2165841133/5000000000 : ℝ)*X 0 1+(2165841199/5000000000 : ℝ)*X 0 2+(486911259/1250000000 : ℝ)*X 1 0+(2165841133/5000000000 : ℝ)*X 1 1+(2165841199/5000000000 : ℝ)*X 1 2+(486911259/1250000000 : ℝ)*X 2 0+(2165841133/5000000000 : ℝ)*X 2 1+(2165841199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1757376507/10000000000 : ℝ)*X 0 0+(1269503161/2500000000 : ℝ)*X 0 1+(679593323/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230853357/10000000000 : ℝ)*X 1 0+(-775741357/5000000000 : ℝ)*X 1 1+(5436747017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230853503/10000000000 : ℝ)*X 2 0+(2718373539/5000000000 : ℝ)*X 2 1+(-1551482429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1134666859/2500000000 : ℝ)*X 0 0+(2004550503/5000000000 : ℝ)*X 0 1+(4009100389/10000000000 : ℝ)*X 0 2+(1134666859/2500000000 : ℝ)*X 1 0+(2004550503/5000000000 : ℝ)*X 1 1+(4009100389/10000000000 : ℝ)*X 1 2+(1134666859/2500000000 : ℝ)*X 2 0+(2004550503/5000000000 : ℝ)*X 2 1+(4009100389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-181866937/1250000000 : ℝ)*X 0 0+(692485997/1250000000 : ℝ)*X 0 1+(1299000941/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396036119/10000000000 : ℝ)*X 1 0+(-51717767/312500000 : ℝ)*X 1 1+(5196004053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215841461/400000000 : ℝ)*X 2 0+(1039200689/2000000000 : ℝ)*X 2 1+(-1654968809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3835751919/10000000000 : ℝ)*X 0 0+(1090137847/2500000000 : ℝ)*X 0 1+(4360550493/10000000000 : ℝ)*X 0 2+(3835751919/10000000000 : ℝ)*X 1 0+(1090137847/2500000000 : ℝ)*X 1 1+(4360550493/10000000000 : ℝ)*X 1 2+(3835751919/10000000000 : ℝ)*X 2 0+(1090137847/2500000000 : ℝ)*X 2 1+(4360550493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1653_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1627/2500 : ℝ) ≤ (-2267956083580134466885472703/3485000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2437993/100000000000000 : ℝ)*(lower0) + (14185033/100000000000000 : ℝ)*(lower3) + (16071477/100000000000000 : ℝ)*(lower4) + (220580901432579/12500000000000 : ℝ)*(major0) + (220580901432579/12500000000000 : ℝ)*(major1) + (220580901432579/12500000000000 : ℝ)*(major2) + (907824497/25000000000000 : ℝ)*(sp1) + (76744959/12500000000000 : ℝ)*(sp3) + (642453969520593/25000000000000 : ℝ)*(sp4) + (321226841892707/12500000000000 : ℝ)*(sp5) + (1284908164142599/50000000000000 : ℝ)*(sp6) + (981167992340973/100000000000000 : ℝ)*(sp7) + (2488357273/100000000000000 : ℝ)*(sp12) + (2038154447/100000000000000 : ℝ)*(sp14) + (490584303150323/50000000000000 : ℝ)*(f.failure) + (642454591609911/25000000000000 : ℝ)*(f.sum) + (13632785067493/1742500000000000000000000000 : ℝ)*base65 + (213975289150303781/21781250000000000000000000000000 : ℝ)*base68 + (13792891463071219/21781250000000000000000000000000 : ℝ)*base69 + (47822906292258719/21781250000000000000000000000000 : ℝ)*base71 + (1028748759751/871250000000000000000000000 : ℝ)*base74 + (68935099675696219/21781250000000000000000000000000 : ℝ)*base75 + (121385101978460031/21781250000000000000000000000000 : ℝ)*base78 + (256447857382397531/21781250000000000000000000000000 : ℝ)*base80 + (28999868379161/3485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (59609371/5000000000000000000000 : ℝ)*base89 + (59609371/5000000000000000000000 : ℝ)*base91 + (59609371/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29329/50000 : ℝ) ≤ (3194249723372934149208210123039/5445312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (35992791/100000000000000 : ℝ)*(lower0) + (12242117/100000000000000 : ℝ)*(lower3) + (242277013/100000000000000 : ℝ)*(upper4) + (231933910920341/12500000000000 : ℝ)*(major0) + (231933910920341/12500000000000 : ℝ)*(major1) + (231933910920341/12500000000000 : ℝ)*(major2) + (2659719635783653/100000000000000 : ℝ)*(sp0) + (664919377035081/25000000000000 : ℝ)*(sp1) + (21277665302837/800000000000 : ℝ)*(sp2) + (103166701519047/10000000000000 : ℝ)*(sp3) + (12831801091/100000000000000 : ℝ)*(sp6) + (210301613/20000000000000 : ℝ)*(sp7) + (43486515393/100000000000000 : ℝ)*(sp9) + (1358872063/100000000000000 : ℝ)*(sp12) + (128958508337317/12500000000000 : ℝ)*(f.failure) + (664930248663929/25000000000000 : ℝ)*(f.sum) + (4435369808777/1742500000000000000000000000 : ℝ)*base65 + (46078126708021099/21781250000000000000000000000000 : ℝ)*base68 + (28628463781385151/21781250000000000000000000000000 : ℝ)*base69 + (160564701745489849/21781250000000000000000000000000 : ℝ)*base72 + (2645156364373/435625000000000000000000000 : ℝ)*base73 + (190674783564989849/21781250000000000000000000000000 : ℝ)*base76 + (71428713708021099/21781250000000000000000000000000 : ℝ)*base78 + (1868660617947651/21781250000000000000000000000000 : ℝ)*base79 + (24845068070499/3485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10398909/1250000000000000000000 : ℝ)*base89 + (10398909/1250000000000000000000 : ℝ)*base91 + (10398909/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (81251/100000 : ℝ) ≤ (7079207945405361852903711394869/8712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670923/3125000000000 : ℝ)*(lower3) + (108026291/100000000000000 : ℝ)*(upper4) + (1638799/3125000000000 : ℝ)*(lower5) + (48730970467671/2500000000000 : ℝ)*(major0) + (48730970467671/2500000000000 : ℝ)*(major1) + (1949238818706841/100000000000000 : ℝ)*(major2) + (798201357/12500000000000 : ℝ)*(sp0) + (10942338369/20000000000000 : ℝ)*(sp1) + (5504469277/6250000000000 : ℝ)*(sp2) + (15636347987/50000000000000 : ℝ)*(sp3) + (2787582634590067/100000000000000 : ℝ)*(sp8) + (1393767154254539/50000000000000 : ℝ)*(sp9) + (696875237173123/25000000000000 : ℝ)*(sp10) + (1083772856920771/100000000000000 : ℝ)*(sp11) + (216760825923349/20000000000000 : ℝ)*(f.failure) + (1393794510100461/50000000000000 : ℝ)*(f.sum) + (18347898690247/27880000000000000000000000000 : ℝ)*base65 + (156895618433744501/17425000000000000000000000000000 : ℝ)*base68 + (41573765554000849/174250000000000000000000000000000 : ℝ)*base70 + (85204023894169501/17425000000000000000000000000000 : ℝ)*base72 + (65353889411833/27880000000000000000000000000 : ℝ)*base74 + (1281140970675999151/174250000000000000000000000000000 : ℝ)*base75 + (38110306424443469/4356250000000000000000000000000 : ℝ)*base78 + (40930675557493469/4356250000000000000000000000000 : ℝ)*base80 + (922426895831/697000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (1228627/2000000000000000000000 : ℝ)*base90 + (1228627/2000000000000000000000 : ℝ)*base92 + (21228627/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-88253/100000 : ℝ) ≤ (-19221956646785960159922635980089/21781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2031501/5000000000000 : ℝ)*(upper1) + (29884767/100000000000000 : ℝ)*(lower2) + (116847619/100000000000000 : ℝ)*(upper3) + (17258467/50000000000000 : ℝ)*(upper5) + (1993469938149291/100000000000000 : ℝ)*(major0) + (1993469938149291/100000000000000 : ℝ)*(major1) + (1993469938149291/100000000000000 : ℝ)*(major2) + (1974083601/50000000000000 : ℝ)*(sp4) + (64819786441/100000000000000 : ℝ)*(sp6) + (429852767/6250000000000 : ℝ)*(sp7) + (726988836907549/25000000000000 : ℝ)*(sp12) + (2907959295797397/100000000000000 : ℝ)*(sp13) + (726973619002739/25000000000000 : ℝ)*(sp14) + (554195187456601/50000000000000 : ℝ)*(sp15) + (44335890102299/4000000000000 : ℝ)*(f.failure) + (2907959295797397/100000000000000 : ℝ)*(f.sum) + (102225268112077/13940000000000000000000000000 : ℝ)*base65 + (485573437544952351/174250000000000000000000000000000 : ℝ)*base67 + (341418741528047649/174250000000000000000000000000000 : ℝ)*base70 + (164993587010202351/174250000000000000000000000000000 : ℝ)*base71 + (57842285779877/13940000000000000000000000000 : ℝ)*base73 + (678003287673702351/174250000000000000000000000000000 : ℝ)*base75 + (853378611075952351/174250000000000000000000000000000 : ℝ)*base77 + (700246845401952351/174250000000000000000000000000000 : ℝ)*base79 + (62472092234937/13940000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2475523/400000000000000000000 : ℝ)*base89 + (2475523/400000000000000000000 : ℝ)*base91 + (2475523/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1653_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8131/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5343/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1627/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(29329/50000 : ℝ) else (81251/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88253/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1653_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1653_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1627/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(29329/50000 : ℝ) else (81251/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88253/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1653_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1653_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1653_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4927/1024 : ℝ) ≤ p) (hpb : p ≤ (4931/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179851577/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (531/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1627/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(29329/50000 : ℝ) else (81251/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88253/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1653_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

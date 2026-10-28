-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:31:52.757789+00:00
-- url     : https://prove2.me/submissions/29d08af3-20cf-4fb5-b056-c60a16f82421

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
theorem support_rectangle_w1142_s9_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166889097/10000000000 : ℝ)*x 0 + (1348245599/2500000000 : ℝ)*x 1 + (2632894559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166889097/10000000000 : ℝ)^8335 ≤ (13166927805007/100000000000000 : ℝ)^6287 := by
    have hnat : (2166889097 : ℕ)^8335*100000000000000^6287 ≤ 13166927805007^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166889097 10000000000 13166927805007 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348245599/2500000000 : ℝ)^8335 ≤ (882067620557/2000000000000 : ℝ)^6287 := by
    have hnat : (1348245599 : ℕ)^8335*2000000000000^6287 ≤ 882067620557^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348245599 2500000000 882067620557 2000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632894559/5000000000 : ℝ)^8335 ≤ (5341211393061/12500000000000 : ℝ)^6287 := by
    have hnat : (2632894559 : ℕ)^8335*12500000000000^6287 ≤ 5341211393061^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632894559 5000000000 5341211393061 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166889097/10000000000 : ℝ), (1348245599/2500000000 : ℝ), (2632894559/5000000000 : ℝ)] ![(13166927805007/100000000000000 : ℝ), (882067620557/2000000000000 : ℝ), (5341211393061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166889097/10000000000 : ℝ)|^8335 ≤ (13166927805007/100000000000000 : ℝ)^6287
        have hw : |(-2166889097/10000000000 : ℝ)|=(2166889097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348245599/2500000000 : ℝ)|^8335 ≤ (882067620557/2000000000000 : ℝ)^6287
        have hw : |(1348245599/2500000000 : ℝ)|=(1348245599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632894559/5000000000 : ℝ)|^8335 ≤ (5341211393061/12500000000000 : ℝ)^6287
        have hw : |(2632894559/5000000000 : ℝ)|=(2632894559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s9_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334046547/625000000 : ℝ)*x 0 + (164555973/312500000 : ℝ)*x 1 + (-2231401277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334046547/625000000 : ℝ)^8335 ≤ (10895289303051/25000000000000 : ℝ)^6287 := by
    have hnat : (334046547 : ℕ)^8335*25000000000000^6287 ≤ 10895289303051^6287*625000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334046547 625000000 10895289303051 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164555973/312500000 : ℝ)^8335 ≤ (21364856426989/50000000000000 : ℝ)^6287 := by
    have hnat : (164555973 : ℕ)^8335*50000000000000^6287 ≤ 21364856426989^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164555973 312500000 21364856426989 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231401277/10000000000 : ℝ)^8335 ≤ (2737825984829/20000000000000 : ℝ)^6287 := by
    have hnat : (2231401277 : ℕ)^8335*20000000000000^6287 ≤ 2737825984829^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231401277 10000000000 2737825984829 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334046547/625000000 : ℝ), (164555973/312500000 : ℝ), (-2231401277/10000000000 : ℝ)] ![(10895289303051/25000000000000 : ℝ), (21364856426989/50000000000000 : ℝ), (2737825984829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334046547/625000000 : ℝ)|^8335 ≤ (10895289303051/25000000000000 : ℝ)^6287
        have hw : |(334046547/625000000 : ℝ)|=(334046547/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164555973/312500000 : ℝ)|^8335 ≤ (21364856426989/50000000000000 : ℝ)^6287
        have hw : |(164555973/312500000 : ℝ)|=(164555973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231401277/10000000000 : ℝ)|^8335 ≤ (2737825984829/20000000000000 : ℝ)^6287
        have hw : |(-2231401277/10000000000 : ℝ)|=(2231401277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s9_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166892413/10000000000 : ℝ)*x 0 + (5266108943/10000000000 : ℝ)*x 1 + (5392662579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166892413/10000000000 : ℝ)^8335 ≤ (13166954518123/100000000000000 : ℝ)^6287 := by
    have hnat : (2166892413 : ℕ)^8335*100000000000000^6287 ≤ 13166954518123^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166892413 10000000000 13166954518123 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266108943/10000000000 : ℝ)^8335 ≤ (21366565915637/50000000000000 : ℝ)^6287 := by
    have hnat : (5266108943 : ℕ)^8335*50000000000000^6287 ≤ 21366565915637^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266108943 10000000000 21366565915637 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392662579/10000000000 : ℝ)^8335 ≤ (44099913640377/100000000000000 : ℝ)^6287 := by
    have hnat : (5392662579 : ℕ)^8335*100000000000000^6287 ≤ 44099913640377^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392662579 10000000000 44099913640377 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166892413/10000000000 : ℝ), (5266108943/10000000000 : ℝ), (5392662579/10000000000 : ℝ)] ![(13166954518123/100000000000000 : ℝ), (21366565915637/50000000000000 : ℝ), (44099913640377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166892413/10000000000 : ℝ)|^8335 ≤ (13166954518123/100000000000000 : ℝ)^6287
        have hw : |(-2166892413/10000000000 : ℝ)|=(2166892413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266108943/10000000000 : ℝ)|^8335 ≤ (21366565915637/50000000000000 : ℝ)^6287
        have hw : |(5266108943/10000000000 : ℝ)|=(5266108943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392662579/10000000000 : ℝ)|^8335 ≤ (44099913640377/100000000000000 : ℝ)^6287
        have hw : |(5392662579/10000000000 : ℝ)|=(5392662579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s9_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312521371/10000000000 : ℝ)*x 0 + (-2104529379/10000000000 : ℝ)*x 1 + (5392661553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312521371/10000000000 : ℝ)^8335 ≤ (43233158383213/100000000000000 : ℝ)^6287 := by
    have hnat : (5312521371 : ℕ)^8335*100000000000000^6287 ≤ 43233158383213^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312521371 10000000000 43233158383213 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104529379/10000000000 : ℝ)^8335 ≤ (2533387817219/20000000000000 : ℝ)^6287 := by
    have hnat : (2104529379 : ℕ)^8335*20000000000000^6287 ≤ 2533387817219^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104529379 10000000000 2533387817219 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392661553/10000000000 : ℝ)^8335 ≤ (44099902516813/100000000000000 : ℝ)^6287 := by
    have hnat : (5392661553 : ℕ)^8335*100000000000000^6287 ≤ 44099902516813^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392661553 10000000000 44099902516813 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312521371/10000000000 : ℝ), (-2104529379/10000000000 : ℝ), (5392661553/10000000000 : ℝ)] ![(43233158383213/100000000000000 : ℝ), (2533387817219/20000000000000 : ℝ), (44099902516813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312521371/10000000000 : ℝ)|^8335 ≤ (43233158383213/100000000000000 : ℝ)^6287
        have hw : |(5312521371/10000000000 : ℝ)|=(5312521371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2104529379/10000000000 : ℝ)|^8335 ≤ (2533387817219/20000000000000 : ℝ)^6287
        have hw : |(-2104529379/10000000000 : ℝ)|=(2104529379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392661553/10000000000 : ℝ)|^8335 ≤ (44099902516813/100000000000000 : ℝ)^6287
        have hw : |(5392661553/10000000000 : ℝ)|=(5392661553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s9_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062504137/2000000000 : ℝ)*x 0 + (1078532451/2000000000 : ℝ)*x 1 + (-263066169/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062504137/2000000000 : ℝ)^8335 ≤ (43233150982007/100000000000000 : ℝ)^6287 := by
    have hnat : (1062504137 : ℕ)^8335*100000000000000^6287 ≤ 43233150982007^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062504137 2000000000 43233150982007 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078532451/2000000000 : ℝ)^8335 ≤ (44099910127673/100000000000000 : ℝ)^6287 := by
    have hnat : (1078532451 : ℕ)^8335*100000000000000^6287 ≤ 44099910127673^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078532451 2000000000 44099910127673 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263066169/1250000000 : ℝ)^8335 ≤ (12666938870647/100000000000000 : ℝ)^6287 := by
    have hnat : (263066169 : ℕ)^8335*100000000000000^6287 ≤ 12666938870647^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263066169 1250000000 12666938870647 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062504137/2000000000 : ℝ), (1078532451/2000000000 : ℝ), (-263066169/1250000000 : ℝ)] ![(43233150982007/100000000000000 : ℝ), (44099910127673/100000000000000 : ℝ), (12666938870647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062504137/2000000000 : ℝ)|^8335 ≤ (43233150982007/100000000000000 : ℝ)^6287
        have hw : |(1062504137/2000000000 : ℝ)|=(1062504137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078532451/2000000000 : ℝ)|^8335 ≤ (44099910127673/100000000000000 : ℝ)^6287
        have hw : |(1078532451/2000000000 : ℝ)|=(1078532451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263066169/1250000000 : ℝ)|^8335 ≤ (12666938870647/100000000000000 : ℝ)^6287
        have hw : |(-263066169/1250000000 : ℝ)|=(263066169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_s9_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (218234279/500000000 : ℝ)*x 0 + (140387127/312500000 : ℝ)*x 1 + (53007689/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218234279/500000000 : ℝ)^8335 ≤ (832927290983/2500000000000 : ℝ)^6287 := by
    have hnat : (218234279 : ℕ)^8335*2500000000000^6287 ≤ 832927290983^6287*500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218234279 500000000 832927290983 2500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140387127/312500000 : ℝ)^8335 ≤ (34615546674663/100000000000000 : ℝ)^6287 := by
    have hnat : (140387127 : ℕ)^8335*100000000000000^6287 ≤ 34615546674663^6287*312500000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140387127 312500000 34615546674663 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53007689/125000000 : ℝ)^8335 ≤ (16033680837033/50000000000000 : ℝ)^6287 := by
    have hnat : (53007689 : ℕ)^8335*50000000000000^6287 ≤ 16033680837033^6287*125000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53007689 125000000 16033680837033 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218234279/500000000 : ℝ), (140387127/312500000 : ℝ), (53007689/125000000 : ℝ)] ![(832927290983/2500000000000 : ℝ), (34615546674663/100000000000000 : ℝ), (16033680837033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218234279/500000000 : ℝ)|^8335 ≤ (832927290983/2500000000000 : ℝ)^6287
        have hw : |(218234279/500000000 : ℝ)|=(218234279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140387127/312500000 : ℝ)|^8335 ≤ (34615546674663/100000000000000 : ℝ)^6287
        have hw : |(140387127/312500000 : ℝ)|=(140387127/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53007689/125000000 : ℝ)|^8335 ≤ (16033680837033/50000000000000 : ℝ)^6287
        have hw : |(53007689/125000000 : ℝ)|=(53007689/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (439/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5677/50000 : ℝ) ^ (4167/1024 : ℝ) ≤ (7145842279466261/50000000000000000000 : ℝ) := by
    have hpowers : (5677/50000 : ℝ)^4167 ≤ (7145842279466261/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5677 : ℕ)^4167*50000000000000000000^1024 ≤ 7145842279466261^1024*50000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 50000 7145842279466261 50000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/50000 : ℝ)) (X := (7145842279466261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (4167/1024 : ℝ) ≤ (34000307559927639/100000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^4167 ≤ (34000307559927639/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14049 : ℕ)^4167*100000000000000000000^1024 ≤ 34000307559927639^1024*100000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 34000307559927639 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (34000307559927639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007145842279466261/25000000000000000000 : ℝ) ≤ (1250087791622783/1250000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25007145842279466261/25000000000000000000 : ℝ)^1024 ≤ (1250087791622783/1250000000000000 : ℝ)^4167 := by
      have hnat : (25007145842279466261 : ℕ)^1024*1250000000000000^4167 ≤ 1250087791622783^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007145842279466261 25000000000000000000 1250087791622783 1250000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250087791622783/1250000000000000 : ℝ)) (X := (25007145842279466261/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048291992118860161/100000000000000000000 : ℝ) ≤ (10001186512989743/10000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (100048291992118860161/100000000000000000000 : ℝ)^1024 ≤ (10001186512989743/10000000000000000 : ℝ)^4167 := by
      have hnat : (100048291992118860161 : ℕ)^1024*10000000000000000^4167 ≤ 10001186512989743^4167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048291992118860161 100000000000000000000 10001186512989743 10000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001186512989743/10000000000000000 : ℝ)) (X := (100048291992118860161/100000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034000307559927639/50000000000000000000 : ℝ) ≤ (5000835346498611/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50034000307559927639/50000000000000000000 : ℝ)^1024 ≤ (5000835346498611/5000000000000000 : ℝ)^4167 := by
      have hnat : (50034000307559927639 : ℕ)^1024*5000000000000000^4167 ≤ 5000835346498611^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034000307559927639 50000000000000000000 5000835346498611 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000835346498611/5000000000000000 : ℝ)) (X := (50034000307559927639/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7145842279466261/50000000000000000000 : ℝ) ≤ ((137453561366211063/137500000000000000 : ℝ)+2*(69168572497/38500000000000 : ℝ)*(5677/50000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (137453561366211063/137500000000000000 : ℝ)+2*(69168572497/38500000000000 : ℝ)*(5677/50000 : ℝ)=(1250087791622783/1250000000000000 : ℝ) by norm_num, show 1+2*(7145842279466261/50000000000000000000 : ℝ)=(25007145842279466261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34000307559927639/100000000000000000000 : ℝ)+(7145842279466261/50000000000000000000 : ℝ) ≤ ((137453561366211063/137500000000000000 : ℝ)+(69168572497/38500000000000 : ℝ)*((14049/100000 : ℝ)+(5677/50000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (137453561366211063/137500000000000000 : ℝ)+(69168572497/38500000000000 : ℝ)*((14049/100000 : ℝ)+(5677/50000 : ℝ))=(10001186512989743/10000000000000000 : ℝ) by norm_num, show 1+(34000307559927639/100000000000000000000 : ℝ)+(7145842279466261/50000000000000000000 : ℝ)=(100048291992118860161/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34000307559927639/100000000000000000000 : ℝ) ≤ ((137453561366211063/137500000000000000 : ℝ)+2*(69168572497/38500000000000 : ℝ)*(14049/100000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (137453561366211063/137500000000000000 : ℝ)+2*(69168572497/38500000000000 : ℝ)*(14049/100000 : ℝ)=(5000835346498611/5000000000000000 : ℝ) by norm_num, show 1+2*(34000307559927639/100000000000000000000 : ℝ)=(50034000307559927639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (137453561366211063/137500000000000000 : ℝ)*(X 1 0+X 2 0)+(69168572497/38500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (137453561366211063/137500000000000000 : ℝ)) (alpha := (69168572497/38500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (137453561366211063/137500000000000000 : ℝ)*(X 0 1+X 2 1)+(69168572497/38500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (137453561366211063/137500000000000000 : ℝ)) (alpha := (69168572497/38500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (137453561366211063/137500000000000000 : ℝ)*(X 0 2+X 1 2)+(69168572497/38500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (137453561366211063/137500000000000000 : ℝ)) (alpha := (69168572497/38500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2166889097/10000000000 : ℝ)*X 0 0+(1348245599/2500000000 : ℝ)*X 0 1+(2632894559/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334046547/625000000 : ℝ)*X 2 0+(164555973/312500000 : ℝ)*X 2 1+(-2231401277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s9_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2166892413/10000000000 : ℝ)*X 0 0+(5266108943/10000000000 : ℝ)*X 0 1+(5392662579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312521371/10000000000 : ℝ)*X 1 0+(-2104529379/10000000000 : ℝ)*X 1 1+(5392661553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1062504137/2000000000 : ℝ)*X 2 0+(1078532451/2000000000 : ℝ)*X 2 1+(-263066169/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((218234279/500000000 : ℝ)*X 0 0+(140387127/312500000 : ℝ)*X 0 1+(53007689/125000000 : ℝ)*X 0 2+(218234279/500000000 : ℝ)*X 1 0+(140387127/312500000 : ℝ)*X 1 1+(53007689/125000000 : ℝ)*X 1 2+(218234279/500000000 : ℝ)*X 2 0+(140387127/312500000 : ℝ)*X 2 1+(53007689/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (204875371679791546418549421/48125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (432574857/50000000000000 : ℝ)*(base19) + (19066559/10000000000000 : ℝ)*(base23) + (51785999/100000000000000 : ℝ)*(lower2) + (57664857/25000000000000 : ℝ)*(lower4) + (75238691/100000000000000 : ℝ)*(upper5) + (5936832775169309/100000000000000 : ℝ)*(major0) + (5936832775169309/100000000000000 : ℝ)*(major1) + (5936832775169309/100000000000000 : ℝ)*(major2) + (16241582739/50000000000000 : ℝ)*(sp0) + (1511832269/100000000000000 : ℝ)*(sp1) + (7901808813452199/100000000000000 : ℝ)*(sp2) + (7901840431467963/100000000000000 : ℝ)*(sp3) + (3950919797059909/50000000000000 : ℝ)*(sp4) + (496478013976989/12500000000000 : ℝ)*(sp5) + (496478013976989/12500000000000 : ℝ)*(f.failure) + (7901841296617677/100000000000000 : ℝ)*(f.sum) + (11082494393049/962500000000000000000000000 : ℝ)*base65 + (2394957809934866731/96250000000000000000000000000000 : ℝ)*base68 + (1575177671064866731/96250000000000000000000000000000 : ℝ)*base70 + (690925760984866731/96250000000000000000000000000000 : ℝ)*base72 + (2545158091551/962500000000000000000000000 : ℝ)*base74 + (1365650749037366731/96250000000000000000000000000000 : ℝ)*base76 + (575050419191116731/96250000000000000000000000000000 : ℝ)*base78 + (530517946976116731/96250000000000000000000000000000 : ℝ)*base80 + (271920394051/962500000000000000000000000 : ℝ)*base82 + (2501303/312500000000000000000 : ℝ)*base89 + (2501303/312500000000000000000 : ℝ)*base91 + (2501303/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1142_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (439/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1142_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1142_box_0 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2040000579/10000000000 : ℝ)*x 0 + (5376308041/10000000000 : ℝ)*x 1 + (672038523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2040000579/10000000000 : ℝ)^8335 ≤ (1519327155621/12500000000000 : ℝ)^6287 := by
    have hnat : (2040000579 : ℕ)^8335*12500000000000^6287 ≤ 1519327155621^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040000579 10000000000 1519327155621 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376308041/10000000000 : ℝ)^8335 ≤ (43922690596109/100000000000000 : ℝ)^6287 := by
    have hnat : (5376308041 : ℕ)^8335*100000000000000^6287 ≤ 43922690596109^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376308041 10000000000 43922690596109 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672038523/1250000000 : ℝ)^8335 ≤ (5490336518117/12500000000000 : ℝ)^6287 := by
    have hnat : (672038523 : ℕ)^8335*12500000000000^6287 ≤ 5490336518117^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672038523 1250000000 5490336518117 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2040000579/10000000000 : ℝ), (5376308041/10000000000 : ℝ), (672038523/1250000000 : ℝ)] ![(1519327155621/12500000000000 : ℝ), (43922690596109/100000000000000 : ℝ), (5490336518117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2040000579/10000000000 : ℝ)|^8335 ≤ (1519327155621/12500000000000 : ℝ)^6287
        have hw : |(-2040000579/10000000000 : ℝ)|=(2040000579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376308041/10000000000 : ℝ)|^8335 ≤ (43922690596109/100000000000000 : ℝ)^6287
        have hw : |(5376308041/10000000000 : ℝ)|=(5376308041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672038523/1250000000 : ℝ)|^8335 ≤ (5490336518117/12500000000000 : ℝ)^6287
        have hw : |(672038523/1250000000 : ℝ)|=(672038523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_1 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647992509/5000000000 : ℝ)*x 0 + (-1074466237/5000000000 : ℝ)*x 1 + (1344077057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647992509/5000000000 : ℝ)^8335 ≤ (8610967865061/20000000000000 : ℝ)^6287 := by
    have hnat : (2647992509 : ℕ)^8335*20000000000000^6287 ≤ 8610967865061^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647992509 5000000000 8610967865061 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074466237/5000000000 : ℝ)^8335 ≤ (6511234019263/50000000000000 : ℝ)^6287 := by
    have hnat : (1074466237 : ℕ)^8335*50000000000000^6287 ≤ 6511234019263^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074466237 5000000000 6511234019263 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344077057/2500000000 : ℝ)^8335 ≤ (21961346310749/50000000000000 : ℝ)^6287 := by
    have hnat : (1344077057 : ℕ)^8335*50000000000000^6287 ≤ 21961346310749^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344077057 2500000000 21961346310749 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647992509/5000000000 : ℝ), (-1074466237/5000000000 : ℝ), (1344077057/2500000000 : ℝ)] ![(8610967865061/20000000000000 : ℝ), (6511234019263/50000000000000 : ℝ), (21961346310749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647992509/5000000000 : ℝ)|^8335 ≤ (8610967865061/20000000000000 : ℝ)^6287
        have hw : |(2647992509/5000000000 : ℝ)|=(2647992509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1074466237/5000000000 : ℝ)|^8335 ≤ (6511234019263/50000000000000 : ℝ)^6287
        have hw : |(-1074466237/5000000000 : ℝ)|=(1074466237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344077057/2500000000 : ℝ)|^8335 ≤ (21961346310749/50000000000000 : ℝ)^6287
        have hw : |(1344077057/2500000000 : ℝ)|=(1344077057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_2 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059197119/2000000000 : ℝ)*x 0 + (107526159/200000000 : ℝ)*x 1 + (-85957283/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059197119/2000000000 : ℝ)^8335 ≤ (43054845544199/100000000000000 : ℝ)^6287 := by
    have hnat : (1059197119 : ℕ)^8335*100000000000000^6287 ≤ 43054845544199^6287*2000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059197119 2000000000 43054845544199 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107526159/200000000 : ℝ)^8335 ≤ (43922689610491/100000000000000 : ℝ)^6287 := by
    have hnat : (107526159 : ℕ)^8335*100000000000000^6287 ≤ 43922689610491^6287*200000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107526159 200000000 43922689610491 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85957283/400000000 : ℝ)^8335 ≤ (6511232416477/50000000000000 : ℝ)^6287 := by
    have hnat : (85957283 : ℕ)^8335*50000000000000^6287 ≤ 6511232416477^6287*400000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85957283 400000000 6511232416477 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059197119/2000000000 : ℝ), (107526159/200000000 : ℝ), (-85957283/400000000 : ℝ)] ![(43054845544199/100000000000000 : ℝ), (43922689610491/100000000000000 : ℝ), (6511232416477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059197119/2000000000 : ℝ)|^8335 ≤ (43054845544199/100000000000000 : ℝ)^6287
        have hw : |(1059197119/2000000000 : ℝ)|=(1059197119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107526159/200000000 : ℝ)|^8335 ≤ (43922689610491/100000000000000 : ℝ)^6287
        have hw : |(107526159/200000000 : ℝ)|=(107526159/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85957283/400000000 : ℝ)|^8335 ≤ (6511232416477/50000000000000 : ℝ)^6287
        have hw : |(-85957283/400000000 : ℝ)|=(85957283/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_3 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4472217517/10000000000 : ℝ)*x 0 + (2156506393/5000000000 : ℝ)*x 1 + (4313012269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4472217517/10000000000 : ℝ)^8335 ≤ (34409646975687/100000000000000 : ℝ)^6287 := by
    have hnat : (4472217517 : ℕ)^8335*100000000000000^6287 ≤ 34409646975687^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472217517 10000000000 34409646975687 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156506393/5000000000 : ℝ)^8335 ≤ (8198794777237/25000000000000 : ℝ)^6287 := by
    have hnat : (2156506393 : ℕ)^8335*25000000000000^6287 ≤ 8198794777237^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156506393 5000000000 8198794777237 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4313012269/10000000000 : ℝ)^8335 ≤ (16397586948609/50000000000000 : ℝ)^6287 := by
    have hnat : (4313012269 : ℕ)^8335*50000000000000^6287 ≤ 16397586948609^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313012269 10000000000 16397586948609 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4472217517/10000000000 : ℝ), (2156506393/5000000000 : ℝ), (4313012269/10000000000 : ℝ)] ![(34409646975687/100000000000000 : ℝ), (8198794777237/25000000000000 : ℝ), (16397586948609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4472217517/10000000000 : ℝ)|^8335 ≤ (34409646975687/100000000000000 : ℝ)^6287
        have hw : |(4472217517/10000000000 : ℝ)|=(4472217517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156506393/5000000000 : ℝ)|^8335 ≤ (8198794777237/25000000000000 : ℝ)^6287
        have hw : |(2156506393/5000000000 : ℝ)|=(2156506393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4313012269/10000000000 : ℝ)|^8335 ≤ (16397586948609/50000000000000 : ℝ)^6287
        have hw : |(4313012269/10000000000 : ℝ)|=(4313012269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_4 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1147582609/5000000000 : ℝ)*x 0 + (5281141809/10000000000 : ℝ)*x 1 + (2640571041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147582609/5000000000 : ℝ)^8335 ≤ (14210131862591/100000000000000 : ℝ)^6287 := by
    have hnat : (1147582609 : ℕ)^8335*100000000000000^6287 ≤ 14210131862591^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147582609 5000000000 14210131862591 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281141809/10000000000 : ℝ)^8335 ≤ (2144746629677/5000000000000 : ℝ)^6287 := by
    have hnat : (5281141809 : ℕ)^8335*5000000000000^6287 ≤ 2144746629677^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281141809 10000000000 2144746629677 5000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640571041/5000000000 : ℝ)^8335 ≤ (1072373388331/2500000000000 : ℝ)^6287 := by
    have hnat : (2640571041 : ℕ)^8335*2500000000000^6287 ≤ 1072373388331^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640571041 5000000000 1072373388331 2500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1147582609/5000000000 : ℝ), (5281141809/10000000000 : ℝ), (2640571041/5000000000 : ℝ)] ![(14210131862591/100000000000000 : ℝ), (2144746629677/5000000000000 : ℝ), (1072373388331/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1147582609/5000000000 : ℝ)|^8335 ≤ (14210131862591/100000000000000 : ℝ)^6287
        have hw : |(-1147582609/5000000000 : ℝ)|=(1147582609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281141809/10000000000 : ℝ)|^8335 ≤ (2144746629677/5000000000000 : ℝ)^6287
        have hw : |(5281141809/10000000000 : ℝ)|=(5281141809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640571041/5000000000 : ℝ)|^8335 ≤ (1072373388331/2500000000000 : ℝ)^6287
        have hw : |(2640571041/5000000000 : ℝ)|=(2640571041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_5 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363220327/10000000000 : ℝ)*x 0 + (-2186367847/10000000000 : ℝ)*x 1 + (66014271/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363220327/10000000000 : ℝ)^8335 ≤ (10945248582323/25000000000000 : ℝ)^6287 := by
    have hnat : (5363220327 : ℕ)^8335*25000000000000^6287 ≤ 10945248582323^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363220327 10000000000 10945248582323 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186367847/10000000000 : ℝ)^8335 ≤ (13324074452299/100000000000000 : ℝ)^6287 := by
    have hnat : (2186367847 : ℕ)^8335*100000000000000^6287 ≤ 13324074452299^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186367847 10000000000 13324074452299 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66014271/125000000 : ℝ)^8335 ≤ (42894931204451/100000000000000 : ℝ)^6287 := by
    have hnat : (66014271 : ℕ)^8335*100000000000000^6287 ≤ 42894931204451^6287*125000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66014271 125000000 42894931204451 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363220327/10000000000 : ℝ), (-2186367847/10000000000 : ℝ), (66014271/125000000 : ℝ)] ![(10945248582323/25000000000000 : ℝ), (13324074452299/100000000000000 : ℝ), (42894931204451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363220327/10000000000 : ℝ)|^8335 ≤ (10945248582323/25000000000000 : ℝ)^6287
        have hw : |(5363220327/10000000000 : ℝ)|=(5363220327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186367847/10000000000 : ℝ)|^8335 ≤ (13324074452299/100000000000000 : ℝ)^6287
        have hw : |(-2186367847/10000000000 : ℝ)|=(2186367847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(66014271/125000000 : ℝ)|^8335 ≤ (42894931204451/100000000000000 : ℝ)^6287
        have hw : |(66014271/125000000 : ℝ)|=(66014271/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_6 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340805017/2500000000 : ℝ)*x 0 + (2640570839/5000000000 : ℝ)*x 1 + (-2186368197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340805017/2500000000 : ℝ)^8335 ≤ (437809915263/1000000000000 : ℝ)^6287 := by
    have hnat : (1340805017 : ℕ)^8335*1000000000000^6287 ≤ 437809915263^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340805017 2500000000 437809915263 1000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640570839/5000000000 : ℝ)^8335 ≤ (8578986236583/20000000000000 : ℝ)^6287 := by
    have hnat : (2640570839 : ℕ)^8335*20000000000000^6287 ≤ 8578986236583^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640570839 5000000000 8578986236583 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186368197/10000000000 : ℝ)^8335 ≤ (13324077280069/100000000000000 : ℝ)^6287 := by
    have hnat : (2186368197 : ℕ)^8335*100000000000000^6287 ≤ 13324077280069^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186368197 10000000000 13324077280069 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340805017/2500000000 : ℝ), (2640570839/5000000000 : ℝ), (-2186368197/10000000000 : ℝ)] ![(437809915263/1000000000000 : ℝ), (8578986236583/20000000000000 : ℝ), (13324077280069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340805017/2500000000 : ℝ)|^8335 ≤ (437809915263/1000000000000 : ℝ)^6287
        have hw : |(1340805017/2500000000 : ℝ)|=(1340805017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640570839/5000000000 : ℝ)|^8335 ≤ (8578986236583/20000000000000 : ℝ)^6287
        have hw : |(2640570839/5000000000 : ℝ)|=(2640570839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186368197/10000000000 : ℝ)|^8335 ≤ (13324077280069/100000000000000 : ℝ)^6287
        have hw : |(-2186368197/10000000000 : ℝ)|=(2186368197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_7 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4256772519/10000000000 : ℝ)*x 0 + (2210357093/5000000000 : ℝ)*x 1 + (4420714193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256772519/10000000000 : ℝ)^8335 ≤ (32229444562523/100000000000000 : ℝ)^6287 := by
    have hnat : (4256772519 : ℕ)^8335*100000000000000^6287 ≤ 32229444562523^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256772519 10000000000 32229444562523 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210357093/5000000000 : ℝ)^8335 ≤ (33885277676703/100000000000000 : ℝ)^6287 := by
    have hnat : (2210357093 : ℕ)^8335*100000000000000^6287 ≤ 33885277676703^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210357093 5000000000 33885277676703 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420714193/10000000000 : ℝ)^8335 ≤ (16942638873919/50000000000000 : ℝ)^6287 := by
    have hnat : (4420714193 : ℕ)^8335*50000000000000^6287 ≤ 16942638873919^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420714193 10000000000 16942638873919 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256772519/10000000000 : ℝ), (2210357093/5000000000 : ℝ), (4420714193/10000000000 : ℝ)] ![(32229444562523/100000000000000 : ℝ), (33885277676703/100000000000000 : ℝ), (16942638873919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256772519/10000000000 : ℝ)|^8335 ≤ (32229444562523/100000000000000 : ℝ)^6287
        have hw : |(4256772519/10000000000 : ℝ)|=(4256772519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210357093/5000000000 : ℝ)|^8335 ≤ (33885277676703/100000000000000 : ℝ)^6287
        have hw : |(2210357093/5000000000 : ℝ)|=(2210357093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420714193/10000000000 : ℝ)|^8335 ≤ (16942638873919/50000000000000 : ℝ)^6287
        have hw : |(4420714193/10000000000 : ℝ)|=(4420714193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_8 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1120903283/5000000000 : ℝ)*x 0 + (104328387/200000000 : ℝ)*x 1 + (538591653/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120903283/5000000000 : ℝ)^8335 ≤ (1721727775881/12500000000000 : ℝ)^6287 := by
    have hnat : (1120903283 : ℕ)^8335*12500000000000^6287 ≤ 1721727775881^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120903283 5000000000 1721727775881 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104328387/200000000 : ℝ)^8335 ≤ (21099693868011/50000000000000 : ℝ)^6287 := by
    have hnat : (104328387 : ℕ)^8335*50000000000000^6287 ≤ 21099693868011^6287*200000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104328387 200000000 21099693868011 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538591653/1000000000 : ℝ)^8335 ≤ (44026790033601/100000000000000 : ℝ)^6287 := by
    have hnat : (538591653 : ℕ)^8335*100000000000000^6287 ≤ 44026790033601^6287*1000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538591653 1000000000 44026790033601 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1120903283/5000000000 : ℝ), (104328387/200000000 : ℝ), (538591653/1000000000 : ℝ)] ![(1721727775881/12500000000000 : ℝ), (21099693868011/50000000000000 : ℝ), (44026790033601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1120903283/5000000000 : ℝ)|^8335 ≤ (1721727775881/12500000000000 : ℝ)^6287
        have hw : |(-1120903283/5000000000 : ℝ)|=(1120903283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104328387/200000000 : ℝ)|^8335 ≤ (21099693868011/50000000000000 : ℝ)^6287
        have hw : |(104328387/200000000 : ℝ)|=(104328387/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538591653/1000000000 : ℝ)|^8335 ≤ (44026790033601/100000000000000 : ℝ)^6287
        have hw : |(538591653/1000000000 : ℝ)|=(538591653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_9 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644596817/5000000000 : ℝ)*x 0 + (-2145083357/10000000000 : ℝ)*x 1 + (5385916487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644596817/5000000000 : ℝ)^8335 ≤ (8596331443603/20000000000000 : ℝ)^6287 := by
    have hnat : (2644596817 : ℕ)^8335*20000000000000^6287 ≤ 8596331443603^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644596817 5000000000 8596331443603 20000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145083357/10000000000 : ℝ)^8335 ≤ (12991553197523/100000000000000 : ℝ)^6287 := by
    have hnat : (2145083357 : ℕ)^8335*100000000000000^6287 ≤ 12991553197523^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145083357 10000000000 12991553197523 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385916487/10000000000 : ℝ)^8335 ≤ (22013394783799/50000000000000 : ℝ)^6287 := by
    have hnat : (5385916487 : ℕ)^8335*50000000000000^6287 ≤ 22013394783799^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385916487 10000000000 22013394783799 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644596817/5000000000 : ℝ), (-2145083357/10000000000 : ℝ), (5385916487/10000000000 : ℝ)] ![(8596331443603/20000000000000 : ℝ), (12991553197523/100000000000000 : ℝ), (22013394783799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644596817/5000000000 : ℝ)|^8335 ≤ (8596331443603/20000000000000 : ℝ)^6287
        have hw : |(2644596817/5000000000 : ℝ)|=(2644596817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145083357/10000000000 : ℝ)|^8335 ≤ (12991553197523/100000000000000 : ℝ)^6287
        have hw : |(-2145083357/10000000000 : ℝ)|=(2145083357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385916487/10000000000 : ℝ)|^8335 ≤ (22013394783799/50000000000000 : ℝ)^6287
        have hw : |(5385916487/10000000000 : ℝ)|=(5385916487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_10 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322298371/2500000000 : ℝ)*x 0 + (2692958201/5000000000 : ℝ)*x 1 + (-2145083673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322298371/2500000000 : ℝ)^8335 ≤ (21490827800997/50000000000000 : ℝ)^6287 := by
    have hnat : (1322298371 : ℕ)^8335*50000000000000^6287 ≤ 21490827800997^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322298371 2500000000 21490827800997 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692958201/5000000000 : ℝ)^8335 ≤ (44026788646431/100000000000000 : ℝ)^6287 := by
    have hnat : (2692958201 : ℕ)^8335*100000000000000^6287 ≤ 44026788646431^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692958201 5000000000 44026788646431 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145083673/10000000000 : ℝ)^8335 ≤ (1299155573479/10000000000000 : ℝ)^6287 := by
    have hnat : (2145083673 : ℕ)^8335*10000000000000^6287 ≤ 1299155573479^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145083673 10000000000 1299155573479 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322298371/2500000000 : ℝ), (2692958201/5000000000 : ℝ), (-2145083673/10000000000 : ℝ)] ![(21490827800997/50000000000000 : ℝ), (44026788646431/100000000000000 : ℝ), (1299155573479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322298371/2500000000 : ℝ)|^8335 ≤ (21490827800997/50000000000000 : ℝ)^6287
        have hw : |(1322298371/2500000000 : ℝ)|=(1322298371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692958201/5000000000 : ℝ)|^8335 ≤ (44026788646431/100000000000000 : ℝ)^6287
        have hw : |(2692958201/5000000000 : ℝ)|=(2692958201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145083673/10000000000 : ℝ)|^8335 ≤ (1299155573479/10000000000000 : ℝ)^6287
        have hw : |(-2145083673/10000000000 : ℝ)|=(2145083673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_11 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2246848289/5000000000 : ℝ)*x 0 + (4302132463/10000000000 : ℝ)*x 1 + (4302132479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246848289/5000000000 : ℝ)^8335 ≤ (17314457162071/50000000000000 : ℝ)^6287 := by
    have hnat : (2246848289 : ℕ)^8335*50000000000000^6287 ≤ 17314457162071^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246848289 5000000000 17314457162071 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4302132463/10000000000 : ℝ)^8335 ≤ (4085692843511/12500000000000 : ℝ)^6287 := by
    have hnat : (4302132463 : ℕ)^8335*12500000000000^6287 ≤ 4085692843511^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302132463 10000000000 4085692843511 12500000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4302132479/10000000000 : ℝ)^8335 ≤ (16342771454623/50000000000000 : ℝ)^6287 := by
    have hnat : (4302132479 : ℕ)^8335*50000000000000^6287 ≤ 16342771454623^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302132479 10000000000 16342771454623 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246848289/5000000000 : ℝ), (4302132463/10000000000 : ℝ), (4302132479/10000000000 : ℝ)] ![(17314457162071/50000000000000 : ℝ), (4085692843511/12500000000000 : ℝ), (16342771454623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246848289/5000000000 : ℝ)|^8335 ≤ (17314457162071/50000000000000 : ℝ)^6287
        have hw : |(2246848289/5000000000 : ℝ)|=(2246848289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4302132463/10000000000 : ℝ)|^8335 ≤ (4085692843511/12500000000000 : ℝ)^6287
        have hw : |(4302132463/10000000000 : ℝ)|=(4302132463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4302132479/10000000000 : ℝ)|^8335 ≤ (16342771454623/50000000000000 : ℝ)^6287
        have hw : |(4302132479/10000000000 : ℝ)|=(4302132479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_12 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2093678227/10000000000 : ℝ)*x 0 + (1359938237/2500000000 : ℝ)*x 1 + (2636551837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093678227/10000000000 : ℝ)^8335 ≤ (12580424490677/100000000000000 : ℝ)^6287 := by
    have hnat : (2093678227 : ℕ)^8335*100000000000000^6287 ≤ 12580424490677^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093678227 10000000000 12580424490677 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359938237/2500000000 : ℝ)^8335 ≤ (11152794280433/25000000000000 : ℝ)^6287 := by
    have hnat : (1359938237 : ℕ)^8335*25000000000000^6287 ≤ 11152794280433^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359938237 2500000000 11152794280433 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636551837/5000000000 : ℝ)^8335 ≤ (21404199186469/50000000000000 : ℝ)^6287 := by
    have hnat : (2636551837 : ℕ)^8335*50000000000000^6287 ≤ 21404199186469^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636551837 5000000000 21404199186469 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2093678227/10000000000 : ℝ), (1359938237/2500000000 : ℝ), (2636551837/5000000000 : ℝ)] ![(12580424490677/100000000000000 : ℝ), (11152794280433/25000000000000 : ℝ), (21404199186469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2093678227/10000000000 : ℝ)|^8335 ≤ (12580424490677/100000000000000 : ℝ)^6287
        have hw : |(-2093678227/10000000000 : ℝ)|=(2093678227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359938237/2500000000 : ℝ)|^8335 ≤ (11152794280433/25000000000000 : ℝ)^6287
        have hw : |(1359938237/2500000000 : ℝ)|=(1359938237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636551837/5000000000 : ℝ)|^8335 ≤ (21404199186469/50000000000000 : ℝ)^6287
        have hw : |(2636551837/5000000000 : ℝ)|=(2636551837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_13 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342224093/2500000000 : ℝ)*x 0 + (-547368073/2500000000 : ℝ)*x 1 + (659138033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342224093/2500000000 : ℝ)^8335 ≤ (21921216569523/50000000000000 : ℝ)^6287 := by
    have hnat : (1342224093 : ℕ)^8335*50000000000000^6287 ≤ 21921216569523^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342224093 2500000000 21921216569523 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547368073/2500000000 : ℝ)^8335 ≤ (1334916212227/10000000000000 : ℝ)^6287 := by
    have hnat : (547368073 : ℕ)^8335*10000000000000^6287 ≤ 1334916212227^6287*2500000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547368073 2500000000 1334916212227 10000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (659138033/1250000000 : ℝ)^8335 ≤ (42808404722983/100000000000000 : ℝ)^6287 := by
    have hnat : (659138033 : ℕ)^8335*100000000000000^6287 ≤ 42808404722983^6287*1250000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659138033 1250000000 42808404722983 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342224093/2500000000 : ℝ), (-547368073/2500000000 : ℝ), (659138033/1250000000 : ℝ)] ![(21921216569523/50000000000000 : ℝ), (1334916212227/10000000000000 : ℝ), (42808404722983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342224093/2500000000 : ℝ)|^8335 ≤ (21921216569523/50000000000000 : ℝ)^6287
        have hw : |(1342224093/2500000000 : ℝ)|=(1342224093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547368073/2500000000 : ℝ)|^8335 ≤ (1334916212227/10000000000000 : ℝ)^6287
        have hw : |(-547368073/2500000000 : ℝ)|=(547368073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(659138033/1250000000 : ℝ)|^8335 ≤ (42808404722983/100000000000000 : ℝ)^6287
        have hw : |(659138033/1250000000 : ℝ)|=(659138033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_14 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368896653/10000000000 : ℝ)*x 0 + (20598063/39062500 : ℝ)*x 1 + (-1094736049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368896653/10000000000 : ℝ)^8335 ≤ (21921218090589/50000000000000 : ℝ)^6287 := by
    have hnat : (5368896653 : ℕ)^8335*50000000000000^6287 ≤ 21921218090589^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368896653 10000000000 21921218090589 50000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20598063/39062500 : ℝ)^8335 ≤ (10702100814811/25000000000000 : ℝ)^6287 := by
    have hnat : (20598063 : ℕ)^8335*25000000000000^6287 ≤ 10702100814811^6287*39062500^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20598063 39062500 10702100814811 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094736049/5000000000 : ℝ)^8335 ≤ (13349160554153/100000000000000 : ℝ)^6287 := by
    have hnat : (1094736049 : ℕ)^8335*100000000000000^6287 ≤ 13349160554153^6287*5000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094736049 5000000000 13349160554153 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368896653/10000000000 : ℝ), (20598063/39062500 : ℝ), (-1094736049/5000000000 : ℝ)] ![(21921218090589/50000000000000 : ℝ), (10702100814811/25000000000000 : ℝ), (13349160554153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368896653/10000000000 : ℝ)|^8335 ≤ (21921218090589/50000000000000 : ℝ)^6287
        have hw : |(5368896653/10000000000 : ℝ)|=(5368896653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20598063/39062500 : ℝ)|^8335 ≤ (10702100814811/25000000000000 : ℝ)^6287
        have hw : |(20598063/39062500 : ℝ)|=(20598063/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094736049/5000000000 : ℝ)|^8335 ≤ (13349160554153/100000000000000 : ℝ)^6287
        have hw : |(-1094736049/5000000000 : ℝ)|=(1094736049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1142_box_15 (p : ℝ) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4238343081/10000000000 : ℝ)*x 0 + (4429806773/10000000000 : ℝ)*x 1 + (4429806627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238343081/10000000000 : ℝ)^8335 ≤ (32044585834603/100000000000000 : ℝ)^6287 := by
    have hnat : (4238343081 : ℕ)^8335*100000000000000^6287 ≤ 32044585834603^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238343081 10000000000 32044585834603 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429806773/10000000000 : ℝ)^8335 ≤ (8494426954663/25000000000000 : ℝ)^6287 := by
    have hnat : (4429806773 : ℕ)^8335*25000000000000^6287 ≤ 8494426954663^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429806773 10000000000 8494426954663 25000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429806627/10000000000 : ℝ)^8335 ≤ (33977706334001/100000000000000 : ℝ)^6287 := by
    have hnat : (4429806627 : ℕ)^8335*100000000000000^6287 ≤ 33977706334001^6287*10000000000^8335 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429806627 10000000000 33977706334001 100000000000000 8335 6287 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8335/2048 : ℝ)) 8335 6287 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238343081/10000000000 : ℝ), (4429806773/10000000000 : ℝ), (4429806627/10000000000 : ℝ)] ![(32044585834603/100000000000000 : ℝ), (8494426954663/25000000000000 : ℝ), (33977706334001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238343081/10000000000 : ℝ)|^8335 ≤ (32044585834603/100000000000000 : ℝ)^6287
        have hw : |(4238343081/10000000000 : ℝ)|=(4238343081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429806773/10000000000 : ℝ)|^8335 ≤ (8494426954663/25000000000000 : ℝ)^6287
        have hw : |(4429806773/10000000000 : ℝ)|=(4429806773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4429806627/10000000000 : ℝ)|^8335 ≤ (33977706334001/100000000000000 : ℝ)^6287
        have hw : |(4429806627/10000000000 : ℝ)|=(4429806627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1142_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62231/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59299/100000 : ℝ) ∧ (2494/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20781/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (439/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (439/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (439/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5677/50000 : ℝ) ^ (4167/1024 : ℝ) ≤ (7145842279466261/50000000000000000000 : ℝ) := by
    have hpowers : (5677/50000 : ℝ)^4167 ≤ (7145842279466261/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5677 : ℕ)^4167*50000000000000000000^1024 ≤ 7145842279466261^1024*50000^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 50000 7145842279466261 50000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/50000 : ℝ)) (X := (7145842279466261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (439/3125 : ℝ) ^ (4167/1024 : ℝ) ≤ (33990460342309207/100000000000000000000 : ℝ) := by
    have hpowers : (439/3125 : ℝ)^4167 ≤ (33990460342309207/100000000000000000000 : ℝ)^1024 := by
      have hnat : (439 : ℕ)^4167*100000000000000000000^1024 ≤ 33990460342309207^1024*3125^4167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        439 3125 33990460342309207 100000000000000000000 4167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (439/3125 : ℝ)) (X := (33990460342309207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007145842279466261/25000000000000000000 : ℝ) ≤ (1250087791622783/1250000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (25007145842279466261/25000000000000000000 : ℝ)^1024 ≤ (1250087791622783/1250000000000000 : ℝ)^4167 := by
      have hnat : (25007145842279466261 : ℕ)^1024*1250000000000000^4167 ≤ 1250087791622783^4167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007145842279466261 25000000000000000000 1250087791622783 1250000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250087791622783/1250000000000000 : ℝ)) (X := (25007145842279466261/25000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048282144901241729/100000000000000000000 : ℝ) ≤ (5000593135545989/5000000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (100048282144901241729/100000000000000000000 : ℝ)^1024 ≤ (5000593135545989/5000000000000000 : ℝ)^4167 := by
      have hnat : (100048282144901241729 : ℕ)^1024*5000000000000000^4167 ≤ 5000593135545989^4167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048282144901241729 100000000000000000000 5000593135545989 5000000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000593135545989/5000000000000000 : ℝ)) (X := (100048282144901241729/100000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033990460342309207/50000000000000000000 : ℝ) ≤ (2500417552300423/2500000000000000 : ℝ) ^ (4167/1024 : ℝ) := by
    have hpowers : (50033990460342309207/50000000000000000000 : ℝ)^1024 ≤ (2500417552300423/2500000000000000 : ℝ)^4167 := by
      have hnat : (50033990460342309207 : ℕ)^1024*2500000000000000^4167 ≤ 2500417552300423^4167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033990460342309207 50000000000000000000 2500417552300423 2500000000000000 1024 4167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500417552300423/2500000000000000 : ℝ)) (X := (50033990460342309207/50000000000000000000 : ℝ)) (by norm_num) 4167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7145842279466261/50000000000000000000 : ℝ) ≤ ((1122120950769118071/1122500000000000000 : ℝ)+2*(80656351619/44900000000000 : ℝ)*(5677/50000 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (1122120950769118071/1122500000000000000 : ℝ)+2*(80656351619/44900000000000 : ℝ)*(5677/50000 : ℝ)=(1250087791622783/1250000000000000 : ℝ) by norm_num, show 1+2*(7145842279466261/50000000000000000000 : ℝ)=(25007145842279466261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33990460342309207/100000000000000000000 : ℝ)+(7145842279466261/50000000000000000000 : ℝ) ≤ ((1122120950769118071/1122500000000000000 : ℝ)+(80656351619/44900000000000 : ℝ)*((439/3125 : ℝ)+(5677/50000 : ℝ)))^(4167/1024 : ℝ) := by
    rw [show (1122120950769118071/1122500000000000000 : ℝ)+(80656351619/44900000000000 : ℝ)*((439/3125 : ℝ)+(5677/50000 : ℝ))=(5000593135545989/5000000000000000 : ℝ) by norm_num, show 1+(33990460342309207/100000000000000000000 : ℝ)+(7145842279466261/50000000000000000000 : ℝ)=(100048282144901241729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33990460342309207/100000000000000000000 : ℝ) ≤ ((1122120950769118071/1122500000000000000 : ℝ)+2*(80656351619/44900000000000 : ℝ)*(439/3125 : ℝ))^(4167/1024 : ℝ) := by
    rw [show (1122120950769118071/1122500000000000000 : ℝ)+2*(80656351619/44900000000000 : ℝ)*(439/3125 : ℝ)=(2500417552300423/2500000000000000 : ℝ) by norm_num, show 1+2*(33990460342309207/100000000000000000000 : ℝ)=(50033990460342309207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1122120950769118071/1122500000000000000 : ℝ)*(X 1 0+X 2 0)+(80656351619/44900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (1122120950769118071/1122500000000000000 : ℝ)) (alpha := (80656351619/44900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1122120950769118071/1122500000000000000 : ℝ)*(X 0 1+X 2 1)+(80656351619/44900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (1122120950769118071/1122500000000000000 : ℝ)) (alpha := (80656351619/44900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1122120950769118071/1122500000000000000 : ℝ)*(X 0 2+X 1 2)+(80656351619/44900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4167/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (439/3125 : ℝ)) (c := (1122120950769118071/1122500000000000000 : ℝ)) (alpha := (80656351619/44900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2040000579/10000000000 : ℝ)*X 0 0+(5376308041/10000000000 : ℝ)*X 0 1+(672038523/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647992509/5000000000 : ℝ)*X 1 0+(-1074466237/5000000000 : ℝ)*X 1 1+(1344077057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059197119/2000000000 : ℝ)*X 2 0+(107526159/200000000 : ℝ)*X 2 1+(-85957283/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4472217517/10000000000 : ℝ)*X 0 0+(2156506393/5000000000 : ℝ)*X 0 1+(4313012269/10000000000 : ℝ)*X 0 2+(4472217517/10000000000 : ℝ)*X 1 0+(2156506393/5000000000 : ℝ)*X 1 1+(4313012269/10000000000 : ℝ)*X 1 2+(4472217517/10000000000 : ℝ)*X 2 0+(2156506393/5000000000 : ℝ)*X 2 1+(4313012269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1147582609/5000000000 : ℝ)*X 0 0+(5281141809/10000000000 : ℝ)*X 0 1+(2640571041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363220327/10000000000 : ℝ)*X 1 0+(-2186367847/10000000000 : ℝ)*X 1 1+(66014271/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340805017/2500000000 : ℝ)*X 2 0+(2640570839/5000000000 : ℝ)*X 2 1+(-2186368197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256772519/10000000000 : ℝ)*X 0 0+(2210357093/5000000000 : ℝ)*X 0 1+(4420714193/10000000000 : ℝ)*X 0 2+(4256772519/10000000000 : ℝ)*X 1 0+(2210357093/5000000000 : ℝ)*X 1 1+(4420714193/10000000000 : ℝ)*X 1 2+(4256772519/10000000000 : ℝ)*X 2 0+(2210357093/5000000000 : ℝ)*X 2 1+(4420714193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1120903283/5000000000 : ℝ)*X 0 0+(104328387/200000000 : ℝ)*X 0 1+(538591653/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644596817/5000000000 : ℝ)*X 1 0+(-2145083357/10000000000 : ℝ)*X 1 1+(5385916487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322298371/2500000000 : ℝ)*X 2 0+(2692958201/5000000000 : ℝ)*X 2 1+(-2145083673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2246848289/5000000000 : ℝ)*X 0 0+(4302132463/10000000000 : ℝ)*X 0 1+(4302132479/10000000000 : ℝ)*X 0 2+(2246848289/5000000000 : ℝ)*X 1 0+(4302132463/10000000000 : ℝ)*X 1 1+(4302132479/10000000000 : ℝ)*X 1 2+(2246848289/5000000000 : ℝ)*X 2 0+(4302132463/10000000000 : ℝ)*X 2 1+(4302132479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2093678227/10000000000 : ℝ)*X 0 0+(1359938237/2500000000 : ℝ)*X 0 1+(2636551837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1342224093/2500000000 : ℝ)*X 1 0+(-547368073/2500000000 : ℝ)*X 1 1+(659138033/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368896653/10000000000 : ℝ)*X 2 0+(20598063/39062500 : ℝ)*X 2 1+(-1094736049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4238343081/10000000000 : ℝ)*X 0 0+(4429806773/10000000000 : ℝ)*X 0 1+(4429806627/10000000000 : ℝ)*X 0 2+(4238343081/10000000000 : ℝ)*X 1 0+(4429806773/10000000000 : ℝ)*X 1 1+(4429806627/10000000000 : ℝ)*X 1 2+(4238343081/10000000000 : ℝ)*X 2 0+(4429806773/10000000000 : ℝ)*X 2 1+(4429806627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1142_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62231/100000 : ℝ) ≤ (-17462889855357516200523570867147/28062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28605263/12500000000000 : ℝ)*(upper1) + (309947911/100000000000000 : ℝ)*(lower4) + (28841313/20000000000000 : ℝ)*(upper5) + (3920602147173281/100000000000000 : ℝ)*(major0) + (3920602147173281/100000000000000 : ℝ)*(major1) + (3920602147173281/100000000000000 : ℝ)*(major2) + (11961851517/50000000000000 : ℝ)*(sp2) + (2715434577/25000000000000 : ℝ)*(sp3) + (2619504286919973/50000000000000 : ℝ)*(sp4) + (5238985887426489/100000000000000 : ℝ)*(sp5) + (1309746396366691/25000000000000 : ℝ)*(sp6) + (1311463388507857/50000000000000 : ℝ)*(sp7) + (935329851/100000000000000 : ℝ)*(sp12) + (23621743309/100000000000000 : ℝ)*(sp13) + (1311468819377011/50000000000000 : ℝ)*(f.failure) + (5239009509169797/100000000000000 : ℝ)*(f.sum) + (154870369663/1122500000000000000000000000 : ℝ)*base66 + (154248181052564049/112250000000000000000000000000000 : ℝ)*base68 + (115552344233935951/112250000000000000000000000000000 : ℝ)*base69 + (51409636265314049/112250000000000000000000000000000 : ℝ)*base72 + (1401141453/1122500000000000000000000000 : ℝ)*base74 + (774831599903564049/112250000000000000000000000000000 : ℝ)*base76 + (435888148920064049/112250000000000000000000000000000 : ℝ)*base78 + (912267630120064049/112250000000000000000000000000000 : ℝ)*base80 + (4695925651081/2245000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8531697/1250000000000000000000 : ℝ)*base89 + (8531697/1250000000000000000000 : ℝ)*base91 + (8531697/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59299/100000 : ℝ) ≤ (8320670685188706437124351199461/14031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4123041/10000000000000 : ℝ)*(lower1) + (6130077/6250000000000 : ℝ)*(lower2) + (65888869/25000000000000 : ℝ)*(upper4) + (996190484252649/25000000000000 : ℝ)*(major0) + (996190484252649/25000000000000 : ℝ)*(major1) + (996190484252649/25000000000000 : ℝ)*(major2) + (2641944463120853/50000000000000 : ℝ)*(sp0) + (660483776473917/12500000000000 : ℝ)*(sp1) + (5283889548054719/100000000000000 : ℝ)*(sp2) + (666463239804483/25000000000000 : ℝ)*(sp3) + (5893067981/100000000000000 : ℝ)*(sp6) + (2118941183/25000000000000 : ℝ)*(sp7) + (1302976199/20000000000000 : ℝ)*(sp8) + (5045866273/20000000000000 : ℝ)*(sp9) + (333232679372833/12500000000000 : ℝ)*(f.failure) + (5283895441122701/100000000000000 : ℝ)*(f.sum) + (1638567386009/561250000000000000000000000 : ℝ)*base66 + (485193796824954921/28062500000000000000000000000000 : ℝ)*base68 + (178126635060079921/28062500000000000000000000000000 : ℝ)*base70 + (635661310461829921/28062500000000000000000000000000 : ℝ)*base72 + (3949691846849/2245000000000000000000000000 : ℝ)*base73 + (706048434493892421/28062500000000000000000000000000 : ℝ)*base76 + (120727935067767421/28062500000000000000000000000000 : ℝ)*base78 + (299939679351704921/28062500000000000000000000000000 : ℝ)*base80 + (747112932783/1122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3243691/312500000000000000000 : ℝ)*base89 + (3243691/312500000000000000000 : ℝ)*base91 + (3243691/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2494/3125 : ℝ) ≤ (22396885834928813341565739801003/28062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (94298863/100000000000000 : ℝ)*(upper0) + (97091211/100000000000000 : ℝ)*(upper1) + (156062927/100000000000000 : ℝ)*(upper2) + (14058273/10000000000000 : ℝ)*(lower5) + (4452637455986669/100000000000000 : ℝ)*(major0) + (4452637455986669/100000000000000 : ℝ)*(major1) + (4452637455986669/100000000000000 : ℝ)*(major2) + (24871958057/25000000000000 : ℝ)*(sp1) + (33781976269/100000000000000 : ℝ)*(sp3) + (2278073881/100000000000000 : ℝ)*(sp4) + (589979236039929/10000000000000 : ℝ)*(sp8) + (5899695150640943/100000000000000 : ℝ)*(sp9) + (5899794638473171/100000000000000 : ℝ)*(sp10) + (2978842915179507/100000000000000 : ℝ)*(sp11) + (46544948393059/1562500000000 : ℝ)*(f.failure) + (5899794638473171/100000000000000 : ℝ)*(f.sum) + (4561985572767/1122500000000000000000000000 : ℝ)*base66 + (1079259061341770499/112250000000000000000000000000000 : ℝ)*base67 + (1292992854929770499/112250000000000000000000000000000 : ℝ)*base69 + (711956330899520499/112250000000000000000000000000000 : ℝ)*base71 + (5094266932629/2245000000000000000000000000 : ℝ)*base74 + (338614245586979501/112250000000000000000000000000000 : ℝ)*base76 + (460392766324020499/112250000000000000000000000000000 : ℝ)*base77 + (1651330128257520499/112250000000000000000000000000000 : ℝ)*base79 + (294286028187/70156250000000000000000000 : ℝ)*base82 + (7483/9765625000000000000 : ℝ)*base90 + (7483/9765625000000000000 : ℝ)*base92 + (7483/9765625000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-20781/25000 : ℝ) ≤ (-2915761436747315305618858778583/3507812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (81249879/50000000000000 : ℝ)*(lower2) + (90918789/100000000000000 : ℝ)*(upper3) + (166850541/100000000000000 : ℝ)*(upper5) + (70119260851157/1562500000000 : ℝ)*(major0) + (70119260851157/1562500000000 : ℝ)*(major1) + (70119260851157/1562500000000 : ℝ)*(major2) + (22637688753/100000000000000 : ℝ)*(sp4) + (10780168083/100000000000000 : ℝ)*(sp6) + (76469826559/20000000000000 : ℝ)*(sp7) + (21710686203/100000000000000 : ℝ)*(sp8) + (3000319674785721/50000000000000 : ℝ)*(sp12) + (6000683697946397/100000000000000 : ℝ)*(sp13) + (3000336458889157/50000000000000 : ℝ)*(sp14) + (1500953325867769/50000000000000 : ℝ)*(sp15) + (750572250217083/25000000000000 : ℝ)*(f.failure) + (6000683697946397/100000000000000 : ℝ)*(f.sum) + (13651846870553/2245000000000000000000000000 : ℝ)*base66 + (140245168361914287/7015625000000000000000000000000 : ℝ)*base68 + (64404473253820537/7015625000000000000000000000000 : ℝ)*base70 + (39692340129414287/7015625000000000000000000000000 : ℝ)*base72 + (4052685144297/561250000000000000000000000 : ℝ)*base74 + (7307244882508037/7015625000000000000000000000000 : ℝ)*base76 + (30470308096570537/7015625000000000000000000000000 : ℝ)*base78 + (11395594885074331/3507812500000000000000000000000 : ℝ)*base80 + (4945682999299/1122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (238441/625000000000000000000 : ℝ)*base89 + (238441/625000000000000000000 : ℝ)*base91 + (238441/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1142_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (439/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59299/100000 : ℝ) else (2494/3125 : ℝ) ≤ X j i ∧ X j i ≤ (20781/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1142_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1142_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59299/100000 : ℝ) else (2494/3125 : ℝ) ≤ X j i ∧ X j i ≤ (20781/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1142_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1142_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4167/1024 : ℝ) ≤ p) (hpb : p ≤ (8335/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37368427/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59299/100000 : ℝ) else (2494/3125 : ℝ) ≤ X j i ∧ X j i ≤ (20781/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1142_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

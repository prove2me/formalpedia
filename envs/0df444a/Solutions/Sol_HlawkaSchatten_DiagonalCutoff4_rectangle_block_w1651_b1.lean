-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1651_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:13:11.113523+00:00
-- url     : https://prove2.me/submissions/0516f86f-1174-42bf-ac1e-e86ac23c4cc4

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
theorem support_rectangle_w1651_s3_0 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-321249011/2000000000 : ℝ)*x 0 + (2723652867/5000000000 : ℝ)*x 1 + (5183913191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321249011/2000000000 : ℝ)^4923 ≤ (9936490253197/100000000000000 : ℝ)^3899 := by
    have hnat : (321249011 : ℕ)^4923*100000000000000^3899 ≤ 9936490253197^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321249011 2000000000 9936490253197 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723652867/5000000000 : ℝ)^4923 ≤ (46440275064291/100000000000000 : ℝ)^3899 := by
    have hnat : (2723652867 : ℕ)^4923*100000000000000^3899 ≤ 46440275064291^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723652867 5000000000 46440275064291 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183913191/10000000000 : ℝ)^4923 ≤ (43623234661033/100000000000000 : ℝ)^3899 := by
    have hnat : (5183913191 : ℕ)^4923*100000000000000^3899 ≤ 43623234661033^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183913191 10000000000 43623234661033 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-321249011/2000000000 : ℝ), (2723652867/5000000000 : ℝ), (5183913191/10000000000 : ℝ)] ![(9936490253197/100000000000000 : ℝ), (46440275064291/100000000000000 : ℝ), (43623234661033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-321249011/2000000000 : ℝ)|^4923 ≤ (9936490253197/100000000000000 : ℝ)^3899
        have hw : |(-321249011/2000000000 : ℝ)|=(321249011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723652867/5000000000 : ℝ)|^4923 ≤ (46440275064291/100000000000000 : ℝ)^3899
        have hw : |(2723652867/5000000000 : ℝ)|=(2723652867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183913191/10000000000 : ℝ)|^4923 ≤ (43623234661033/100000000000000 : ℝ)^3899
        have hw : |(5183913191/10000000000 : ℝ)|=(5183913191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_1 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673805499/5000000000 : ℝ)*x 0 + (-1741833263/10000000000 : ℝ)*x 1 + (1295978307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673805499/5000000000 : ℝ)^4923 ≤ (22684856164601/50000000000000 : ℝ)^3899 := by
    have hnat : (2673805499 : ℕ)^4923*50000000000000^3899 ≤ 22684856164601^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673805499 5000000000 22684856164601 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741833263/10000000000 : ℝ)^4923 ≤ (11007052601367/100000000000000 : ℝ)^3899 := by
    have hnat : (1741833263 : ℕ)^4923*100000000000000^3899 ≤ 11007052601367^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741833263 10000000000 11007052601367 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295978307/2500000000 : ℝ)^4923 ≤ (8724647010833/20000000000000 : ℝ)^3899 := by
    have hnat : (1295978307 : ℕ)^4923*20000000000000^3899 ≤ 8724647010833^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295978307 2500000000 8724647010833 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673805499/5000000000 : ℝ), (-1741833263/10000000000 : ℝ), (1295978307/2500000000 : ℝ)] ![(22684856164601/50000000000000 : ℝ), (11007052601367/100000000000000 : ℝ), (8724647010833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673805499/5000000000 : ℝ)|^4923 ≤ (22684856164601/50000000000000 : ℝ)^3899
        have hw : |(2673805499/5000000000 : ℝ)|=(2673805499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1741833263/10000000000 : ℝ)|^4923 ≤ (11007052601367/100000000000000 : ℝ)^3899
        have hw : |(-1741833263/10000000000 : ℝ)|=(1741833263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295978307/2500000000 : ℝ)|^4923 ≤ (8724647010833/20000000000000 : ℝ)^3899
        have hw : |(1295978307/2500000000 : ℝ)|=(1295978307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_2 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347610987/10000000000 : ℝ)*x 0 + (2591956613/5000000000 : ℝ)*x 1 + (-5443229/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347610987/10000000000 : ℝ)^4923 ≤ (22684856105683/50000000000000 : ℝ)^3899 := by
    have hnat : (5347610987 : ℕ)^4923*50000000000000^3899 ≤ 22684856105683^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347610987 10000000000 22684856105683 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591956613/5000000000 : ℝ)^4923 ≤ (8724647006583/20000000000000 : ℝ)^3899 := by
    have hnat : (2591956613 : ℕ)^4923*20000000000000^3899 ≤ 8724647006583^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591956613 5000000000 8724647006583 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443229/31250000 : ℝ)^4923 ≤ (687940796063/6250000000000 : ℝ)^3899 := by
    have hnat : (5443229 : ℕ)^4923*6250000000000^3899 ≤ 687940796063^3899*31250000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443229 31250000 687940796063 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347610987/10000000000 : ℝ), (2591956613/5000000000 : ℝ), (-5443229/31250000 : ℝ)] ![(22684856105683/50000000000000 : ℝ), (8724647006583/20000000000000 : ℝ), (687940796063/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347610987/10000000000 : ℝ)|^4923 ≤ (22684856105683/50000000000000 : ℝ)^3899
        have hw : |(5347610987/10000000000 : ℝ)|=(5347610987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591956613/5000000000 : ℝ)|^4923 ≤ (8724647006583/20000000000000 : ℝ)^3899
        have hw : |(2591956613/5000000000 : ℝ)|=(2591956613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5443229/31250000 : ℝ)|^4923 ≤ (687940796063/6250000000000 : ℝ)^3899
        have hw : |(-5443229/31250000 : ℝ)|=(5443229/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_3 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089975821/5000000000 : ℝ)*x 0 + (3848873213/10000000000 : ℝ)*x 1 + (4531194337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089975821/5000000000 : ℝ)^4923 ≤ (16620685130061/50000000000000 : ℝ)^3899 := by
    have hnat : (2089975821 : ℕ)^4923*50000000000000^3899 ≤ 16620685130061^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089975821 5000000000 16620685130061 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3848873213/10000000000 : ℝ)^4923 ≤ (29952230625147/100000000000000 : ℝ)^3899 := by
    have hnat : (3848873213 : ℕ)^4923*100000000000000^3899 ≤ 29952230625147^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848873213 10000000000 29952230625147 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531194337/10000000000 : ℝ)^4923 ≤ (36806399100839/100000000000000 : ℝ)^3899 := by
    have hnat : (4531194337 : ℕ)^4923*100000000000000^3899 ≤ 36806399100839^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531194337 10000000000 36806399100839 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089975821/5000000000 : ℝ), (3848873213/10000000000 : ℝ), (4531194337/10000000000 : ℝ)] ![(16620685130061/50000000000000 : ℝ), (29952230625147/100000000000000 : ℝ), (36806399100839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089975821/5000000000 : ℝ)|^4923 ≤ (16620685130061/50000000000000 : ℝ)^3899
        have hw : |(2089975821/5000000000 : ℝ)|=(2089975821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3848873213/10000000000 : ℝ)|^4923 ≤ (29952230625147/100000000000000 : ℝ)^3899
        have hw : |(3848873213/10000000000 : ℝ)|=(3848873213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531194337/10000000000 : ℝ)|^4923 ≤ (36806399100839/100000000000000 : ℝ)^3899
        have hw : |(4531194337/10000000000 : ℝ)|=(4531194337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_4 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1606309207/10000000000 : ℝ)*x 0 + (1296477021/2500000000 : ℝ)*x 1 + (1361322473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1606309207/10000000000 : ℝ)^4923 ≤ (9936991336909/100000000000000 : ℝ)^3899 := by
    have hnat : (1606309207 : ℕ)^4923*100000000000000^3899 ≤ 9936991336909^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606309207 10000000000 9936991336909 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296477021/2500000000 : ℝ)^4923 ≤ (43644431851189/100000000000000 : ℝ)^3899 := by
    have hnat : (1296477021 : ℕ)^4923*100000000000000^3899 ≤ 43644431851189^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296477021 2500000000 43644431851189 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361322473/2500000000 : ℝ)^4923 ≤ (23209288399483/50000000000000 : ℝ)^3899 := by
    have hnat : (1361322473 : ℕ)^4923*50000000000000^3899 ≤ 23209288399483^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361322473 2500000000 23209288399483 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1606309207/10000000000 : ℝ), (1296477021/2500000000 : ℝ), (1361322473/2500000000 : ℝ)] ![(9936991336909/100000000000000 : ℝ), (43644431851189/100000000000000 : ℝ), (23209288399483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1606309207/10000000000 : ℝ)|^4923 ≤ (9936991336909/100000000000000 : ℝ)^3899
        have hw : |(-1606309207/10000000000 : ℝ)|=(1606309207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296477021/2500000000 : ℝ)|^4923 ≤ (43644431851189/100000000000000 : ℝ)^3899
        have hw : |(1296477021/2500000000 : ℝ)|=(1296477021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361322473/2500000000 : ℝ)|^4923 ≤ (23209288399483/50000000000000 : ℝ)^3899
        have hw : |(1361322473/2500000000 : ℝ)|=(1361322473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_5 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527723599/1000000000 : ℝ)*x 0 + (-1480457009/10000000000 : ℝ)*x 1 + (5445289637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527723599/1000000000 : ℝ)^4923 ≤ (44617141006819/100000000000000 : ℝ)^3899 := by
    have hnat : (527723599 : ℕ)^4923*100000000000000^3899 ≤ 44617141006819^3899*1000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527723599 1000000000 44617141006819 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1480457009/10000000000 : ℝ)^4923 ≤ (560267807399/6250000000000 : ℝ)^3899 := by
    have hnat : (1480457009 : ℕ)^4923*6250000000000^3899 ≤ 560267807399^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480457009 10000000000 560267807399 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445289637/10000000000 : ℝ)^4923 ≤ (5802321756789/12500000000000 : ℝ)^3899 := by
    have hnat : (5445289637 : ℕ)^4923*12500000000000^3899 ≤ 5802321756789^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445289637 10000000000 5802321756789 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527723599/1000000000 : ℝ), (-1480457009/10000000000 : ℝ), (5445289637/10000000000 : ℝ)] ![(44617141006819/100000000000000 : ℝ), (560267807399/6250000000000 : ℝ), (5802321756789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527723599/1000000000 : ℝ)|^4923 ≤ (44617141006819/100000000000000 : ℝ)^3899
        have hw : |(527723599/1000000000 : ℝ)|=(527723599/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1480457009/10000000000 : ℝ)|^4923 ≤ (560267807399/6250000000000 : ℝ)^3899
        have hw : |(-1480457009/10000000000 : ℝ)|=(1480457009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445289637/10000000000 : ℝ)|^4923 ≤ (5802321756789/12500000000000 : ℝ)^3899
        have hw : |(5445289637/10000000000 : ℝ)|=(5445289637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_6 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277236363/10000000000 : ℝ)*x 0 + (2722644613/5000000000 : ℝ)*x 1 + (-370114267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277236363/10000000000 : ℝ)^4923 ≤ (4461714498863/10000000000000 : ℝ)^3899 := by
    have hnat : (5277236363 : ℕ)^4923*10000000000000^3899 ≤ 4461714498863^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277236363 10000000000 4461714498863 10000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722644613/5000000000 : ℝ)^4923 ≤ (2901160601911/6250000000000 : ℝ)^3899 := by
    have hnat : (2722644613 : ℕ)^4923*6250000000000^3899 ≤ 2901160601911^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722644613 5000000000 2901160601911 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (370114267/2500000000 : ℝ)^4923 ≤ (4482142684729/50000000000000 : ℝ)^3899 := by
    have hnat : (370114267 : ℕ)^4923*50000000000000^3899 ≤ 4482142684729^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370114267 2500000000 4482142684729 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277236363/10000000000 : ℝ), (2722644613/5000000000 : ℝ), (-370114267/2500000000 : ℝ)] ![(4461714498863/10000000000000 : ℝ), (2901160601911/6250000000000 : ℝ), (4482142684729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277236363/10000000000 : ℝ)|^4923 ≤ (4461714498863/10000000000000 : ℝ)^3899
        have hw : |(5277236363/10000000000 : ℝ)|=(5277236363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722644613/5000000000 : ℝ)|^4923 ≤ (2901160601911/6250000000000 : ℝ)^3899
        have hw : |(2722644613/5000000000 : ℝ)|=(2722644613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-370114267/2500000000 : ℝ)|^4923 ≤ (4482142684729/50000000000000 : ℝ)^3899
        have hw : |(-370114267/2500000000 : ℝ)|=(370114267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s3_7 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045029441/2500000000 : ℝ)*x 0 + (4526026007/10000000000 : ℝ)*x 1 + (3854096387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045029441/2500000000 : ℝ)^4923 ≤ (33243038327843/100000000000000 : ℝ)^3899 := by
    have hnat : (1045029441 : ℕ)^4923*100000000000000^3899 ≤ 33243038327843^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045029441 2500000000 33243038327843 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526026007/10000000000 : ℝ)^4923 ≤ (9188349880863/25000000000000 : ℝ)^3899 := by
    have hnat : (4526026007 : ℕ)^4923*25000000000000^3899 ≤ 9188349880863^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526026007 10000000000 9188349880863 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3854096387/10000000000 : ℝ)^4923 ≤ (7500890533217/25000000000000 : ℝ)^3899 := by
    have hnat : (3854096387 : ℕ)^4923*25000000000000^3899 ≤ 7500890533217^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3854096387 10000000000 7500890533217 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045029441/2500000000 : ℝ), (4526026007/10000000000 : ℝ), (3854096387/10000000000 : ℝ)] ![(33243038327843/100000000000000 : ℝ), (9188349880863/25000000000000 : ℝ), (7500890533217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045029441/2500000000 : ℝ)|^4923 ≤ (33243038327843/100000000000000 : ℝ)^3899
        have hw : |(1045029441/2500000000 : ℝ)|=(1045029441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526026007/10000000000 : ℝ)|^4923 ≤ (9188349880863/25000000000000 : ℝ)^3899
        have hw : |(4526026007/10000000000 : ℝ)|=(4526026007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3854096387/10000000000 : ℝ)|^4923 ≤ (7500890533217/25000000000000 : ℝ)^3899
        have hw : |(3854096387/10000000000 : ℝ)|=(3854096387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1651_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10671/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16271/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10607/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10607/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10607/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8171/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10607/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10607/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8171/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10607/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10607/100000 : ℝ) ^ (4919/1024 : ℝ) ≤ (2085587260819191/100000000000000000000 : ℝ) := by
    have hpowers : (10607/100000 : ℝ)^4919 ≤ (2085587260819191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10607 : ℕ)^4919*100000000000000000000^1024 ≤ 2085587260819191^1024*100000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10607 100000 2085587260819191 100000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10607/100000 : ℝ)) (X := (2085587260819191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8171/50000 : ℝ) ^ (4919/1024 : ℝ) ≤ (16632043583362961/100000000000000000000 : ℝ) := by
    have hpowers : (8171/50000 : ℝ)^4919 ≤ (16632043583362961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8171 : ℕ)^4919*100000000000000000000^1024 ≤ 16632043583362961^1024*50000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8171 50000 16632043583362961 100000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8171/50000 : ℝ)) (X := (16632043583362961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002085587260819191/50000000000000000000 : ℝ) ≤ (2000017366180829/2000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (50002085587260819191/50000000000000000000 : ℝ)^1024 ≤ (2000017366180829/2000000000000000 : ℝ)^4919 := by
      have hnat : (50002085587260819191 : ℕ)^1024*2000000000000000^4919 ≤ 2000017366180829^4919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002085587260819191 50000000000000000000 2000017366180829 2000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000017366180829/2000000000000000 : ℝ)) (X := (50002085587260819191/50000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502339703855522769/12500000000000000000 : ℝ) ≤ (10000389620527961/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (12502339703855522769/12500000000000000000 : ℝ)^1024 ≤ (10000389620527961/10000000000000000 : ℝ)^4919 := by
      have hnat : (12502339703855522769 : ℕ)^1024*10000000000000000^4919 ≤ 10000389620527961^4919*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502339703855522769 12500000000000000000 10000389620527961 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000389620527961/10000000000000000 : ℝ)) (X := (12502339703855522769/12500000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016632043583362961/50000000000000000000 : ℝ) ≤ (10000692410151777/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (50016632043583362961/50000000000000000000 : ℝ)^1024 ≤ (10000692410151777/10000000000000000 : ℝ)^4919 := by
      have hnat : (50016632043583362961 : ℕ)^1024*10000000000000000^4919 ≤ 10000692410151777^4919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016632043583362961 50000000000000000000 10000692410151777 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000692410151777/10000000000000000 : ℝ)) (X := (50016632043583362961/50000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2085587260819191/100000000000000000000 : ℝ) ≤ ((57344074596155638951/57350000000000000000 : ℝ)+2*(37848702977/71687500000000 : ℝ)*(10607/100000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (57344074596155638951/57350000000000000000 : ℝ)+2*(37848702977/71687500000000 : ℝ)*(10607/100000 : ℝ)=(2000017366180829/2000000000000000 : ℝ) by norm_num, show 1+2*(2085587260819191/100000000000000000000 : ℝ)=(50002085587260819191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16632043583362961/100000000000000000000 : ℝ)+(2085587260819191/100000000000000000000 : ℝ) ≤ ((57344074596155638951/57350000000000000000 : ℝ)+(37848702977/71687500000000 : ℝ)*((8171/50000 : ℝ)+(10607/100000 : ℝ)))^(4919/1024 : ℝ) := by
    rw [show (57344074596155638951/57350000000000000000 : ℝ)+(37848702977/71687500000000 : ℝ)*((8171/50000 : ℝ)+(10607/100000 : ℝ))=(10000389620527961/10000000000000000 : ℝ) by norm_num, show 1+(16632043583362961/100000000000000000000 : ℝ)+(2085587260819191/100000000000000000000 : ℝ)=(12502339703855522769/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16632043583362961/100000000000000000000 : ℝ) ≤ ((57344074596155638951/57350000000000000000 : ℝ)+2*(37848702977/71687500000000 : ℝ)*(8171/50000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (57344074596155638951/57350000000000000000 : ℝ)+2*(37848702977/71687500000000 : ℝ)*(8171/50000 : ℝ)=(10000692410151777/10000000000000000 : ℝ) by norm_num, show 1+2*(16632043583362961/100000000000000000000 : ℝ)=(50016632043583362961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57344074596155638951/57350000000000000000 : ℝ)*(X 1 0+X 2 0)+(37848702977/71687500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (10607/100000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (57344074596155638951/57350000000000000000 : ℝ)) (alpha := (37848702977/71687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57344074596155638951/57350000000000000000 : ℝ)*(X 0 1+X 2 1)+(37848702977/71687500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (10607/100000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (57344074596155638951/57350000000000000000 : ℝ)) (alpha := (37848702977/71687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57344074596155638951/57350000000000000000 : ℝ)*(X 0 2+X 1 2)+(37848702977/71687500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (10607/100000 : ℝ)) (hi := (8171/50000 : ℝ)) (c := (57344074596155638951/57350000000000000000 : ℝ)) (alpha := (37848702977/71687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-321249011/2000000000 : ℝ)*X 0 0+(2723652867/5000000000 : ℝ)*X 0 1+(5183913191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673805499/5000000000 : ℝ)*X 1 0+(-1741833263/10000000000 : ℝ)*X 1 1+(1295978307/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347610987/10000000000 : ℝ)*X 2 0+(2591956613/5000000000 : ℝ)*X 2 1+(-5443229/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089975821/5000000000 : ℝ)*X 0 0+(3848873213/10000000000 : ℝ)*X 0 1+(4531194337/10000000000 : ℝ)*X 0 2+(2089975821/5000000000 : ℝ)*X 1 0+(3848873213/10000000000 : ℝ)*X 1 1+(4531194337/10000000000 : ℝ)*X 1 2+(2089975821/5000000000 : ℝ)*X 2 0+(3848873213/10000000000 : ℝ)*X 2 1+(4531194337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1606309207/10000000000 : ℝ)*X 0 0+(1296477021/2500000000 : ℝ)*X 0 1+(1361322473/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527723599/1000000000 : ℝ)*X 1 0+(-1480457009/10000000000 : ℝ)*X 1 1+(5445289637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277236363/10000000000 : ℝ)*X 2 0+(2722644613/5000000000 : ℝ)*X 2 1+(-370114267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1045029441/2500000000 : ℝ)*X 0 0+(4526026007/10000000000 : ℝ)*X 0 1+(3854096387/10000000000 : ℝ)*X 0 2+(1045029441/2500000000 : ℝ)*X 1 0+(4526026007/10000000000 : ℝ)*X 1 1+(3854096387/10000000000 : ℝ)*X 1 2+(1045029441/2500000000 : ℝ)*X 2 0+(4526026007/10000000000 : ℝ)*X 2 1+(3854096387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1658351110234581849491240007/143375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (982367703/50000000000000 : ℝ)*(base19) + (904127843/50000000000000 : ℝ)*(base23) + (79502937/100000000000000 : ℝ)*(lower2) + (316981887/100000000000000 : ℝ)*(upper3) + (48943847/25000000000000 : ℝ)*(upper5) + (131556770103873/5000000000000 : ℝ)*(major0) + (131556770103873/5000000000000 : ℝ)*(major1) + (131556770103873/5000000000000 : ℝ)*(major2) + (1898320323266459/50000000000000 : ℝ)*(sp0) + (949165823440367/25000000000000 : ℝ)*(sp1) + (3796663450241187/100000000000000 : ℝ)*(sp2) + (11449958192601/781250000000 : ℝ)*(sp3) + (6152990989/25000000000000 : ℝ)*(sp4) + (10511454141/100000000000000 : ℝ)*(sp7) + (1465605160107069/100000000000000 : ℝ)*(f.failure) + (1898332629248437/50000000000000 : ℝ)*(f.sum) + (11555114602871/2867500000000000000000000000 : ℝ)*base65 + (3919461757545692777/286750000000000000000000000000000 : ℝ)*base68 + (946459730051192777/286750000000000000000000000000000 : ℝ)*base70 + (2952213517585442777/286750000000000000000000000000000 : ℝ)*base72 + (16329064414273/5735000000000000000000000000 : ℝ)*base74 + (926629423115692777/286750000000000000000000000000000 : ℝ)*base76 + (2474974490394192777/286750000000000000000000000000000 : ℝ)*base78 + (536117761661192777/286750000000000000000000000000000 : ℝ)*base80 + (5945094194367/5735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12344679/1250000000000000000000 : ℝ)*base89 + (12344679/1250000000000000000000 : ℝ)*base91 + (12344679/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8756363946376335259066681959/716875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (822750717/50000000000000 : ℝ)*(base19) + (2021508703/100000000000000 : ℝ)*(base23) + (28117637/25000000000000 : ℝ)*(upper3) + (36820411/50000000000000 : ℝ)*(lower4) + (81659267/25000000000000 : ℝ)*(upper5) + (1335893850066197/50000000000000 : ℝ)*(major0) + (1335893850066197/50000000000000 : ℝ)*(major1) + (1335893850066197/50000000000000 : ℝ)*(major2) + (644062637/3125000000000 : ℝ)*(sp1) + (3581587649/20000000000000 : ℝ)*(sp2) + (3855325533606011/100000000000000 : ℝ)*(sp4) + (3855303278100193/100000000000000 : ℝ)*(sp5) + (481913200519883/12500000000000 : ℝ)*(sp6) + (297649891900877/20000000000000 : ℝ)*(sp7) + (297649891900877/20000000000000 : ℝ)*(f.failure) + (3855325533606011/100000000000000 : ℝ)*(f.sum) + (132576119176021/28675000000000000000000000000 : ℝ)*base66 + (34473600438474339347/2867500000000000000000000000000000 : ℝ)*base67 + (40200387379384339347/2867500000000000000000000000000000 : ℝ)*base69 + (87335243521839347/2867500000000000000000000000000000 : ℝ)*base71 + (58622231847727/14337500000000000000000000000 : ℝ)*base73 + (19160247551616839347/2867500000000000000000000000000000 : ℝ)*base75 + (17996957234339347/2867500000000000000000000000000000 : ℝ)*base77 + (7163302203450660653/2867500000000000000000000000000000 : ℝ)*base80 + (147757930437479/28675000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1613993/250000000000000000000 : ℝ)*base90 + (1613993/250000000000000000000 : ℝ)*base92 + (1613993/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1651_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1651_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1651_s4_0 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-200786091/1250000000 : ℝ)*x 0 + (5447084591/10000000000 : ℝ)*x 1 + (1296026281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200786091/1250000000 : ℝ)^4923 ≤ (4968415688641/50000000000000 : ℝ)^3899 := by
    have hnat : (200786091 : ℕ)^4923*50000000000000^3899 ≤ 4968415688641^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200786091 1250000000 4968415688641 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447084591/10000000000 : ℝ)^4923 ≤ (46437894606339/100000000000000 : ℝ)^3899 := by
    have hnat : (5447084591 : ℕ)^4923*100000000000000^3899 ≤ 46437894606339^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447084591 10000000000 46437894606339 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296026281/2500000000 : ℝ)^4923 ≤ (10906318498933/25000000000000 : ℝ)^3899 := by
    have hnat : (1296026281 : ℕ)^4923*25000000000000^3899 ≤ 10906318498933^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296026281 2500000000 10906318498933 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200786091/1250000000 : ℝ), (5447084591/10000000000 : ℝ), (1296026281/2500000000 : ℝ)] ![(4968415688641/50000000000000 : ℝ), (46437894606339/100000000000000 : ℝ), (10906318498933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200786091/1250000000 : ℝ)|^4923 ≤ (4968415688641/50000000000000 : ℝ)^3899
        have hw : |(-200786091/1250000000 : ℝ)|=(200786091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447084591/10000000000 : ℝ)|^4923 ≤ (46437894606339/100000000000000 : ℝ)^3899
        have hw : |(5447084591/10000000000 : ℝ)|=(5447084591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296026281/2500000000 : ℝ)|^4923 ≤ (10906318498933/25000000000000 : ℝ)^3899
        have hw : |(1296026281/2500000000 : ℝ)|=(1296026281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_1 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347550043/10000000000 : ℝ)*x 0 + (-34833059/200000000 : ℝ)*x 1 + (1296027521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347550043/10000000000 : ℝ)^4923 ≤ (9073811872359/20000000000000 : ℝ)^3899 := by
    have hnat : (5347550043 : ℕ)^4923*20000000000000^3899 ≤ 9073811872359^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347550043 10000000000 9073811872359 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34833059/200000000 : ℝ)^4923 ≤ (550280696401/5000000000000 : ℝ)^3899 := by
    have hnat : (34833059 : ℕ)^4923*5000000000000^3899 ≤ 550280696401^3899*200000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34833059 200000000 550280696401 5000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296027521/2500000000 : ℝ)^4923 ≤ (21812663348599/50000000000000 : ℝ)^3899 := by
    have hnat : (1296027521 : ℕ)^4923*50000000000000^3899 ≤ 21812663348599^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296027521 2500000000 21812663348599 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347550043/10000000000 : ℝ), (-34833059/200000000 : ℝ), (1296027521/2500000000 : ℝ)] ![(9073811872359/20000000000000 : ℝ), (550280696401/5000000000000 : ℝ), (21812663348599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347550043/10000000000 : ℝ)|^4923 ≤ (9073811872359/20000000000000 : ℝ)^3899
        have hw : |(5347550043/10000000000 : ℝ)|=(5347550043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34833059/200000000 : ℝ)|^4923 ≤ (550280696401/5000000000000 : ℝ)^3899
        have hw : |(-34833059/200000000 : ℝ)|=(34833059/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1296027521/2500000000 : ℝ)|^4923 ≤ (21812663348599/50000000000000 : ℝ)^3899
        have hw : |(1296027521/2500000000 : ℝ)|=(1296027521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_2 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33422211/62500000 : ℝ)*x 0 + (648012829/1250000000 : ℝ)*x 1 + (-1741657883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33422211/62500000 : ℝ)^4923 ≤ (45369099179307/100000000000000 : ℝ)^3899 := by
    have hnat : (33422211 : ℕ)^4923*100000000000000^3899 ≤ 45369099179307^3899*62500000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33422211 62500000 45369099179307 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648012829/1250000000 : ℝ)^4923 ≤ (17450099007/40000000000 : ℝ)^3899 := by
    have hnat : (648012829 : ℕ)^4923*40000000000^3899 ≤ 17450099007^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648012829 1250000000 17450099007 40000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1741657883/10000000000 : ℝ)^4923 ≤ (110056532867/1000000000000 : ℝ)^3899 := by
    have hnat : (1741657883 : ℕ)^4923*1000000000000^3899 ≤ 110056532867^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741657883 10000000000 110056532867 1000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33422211/62500000 : ℝ), (648012829/1250000000 : ℝ), (-1741657883/10000000000 : ℝ)] ![(45369099179307/100000000000000 : ℝ), (17450099007/40000000000 : ℝ), (110056532867/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33422211/62500000 : ℝ)|^4923 ≤ (45369099179307/100000000000000 : ℝ)^3899
        have hw : |(33422211/62500000 : ℝ)|=(33422211/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648012829/1250000000 : ℝ)|^4923 ≤ (17450099007/40000000000 : ℝ)^3899
        have hw : |(648012829/1250000000 : ℝ)|=(648012829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1741657883/10000000000 : ℝ)|^4923 ≤ (110056532867/1000000000000 : ℝ)^3899
        have hw : |(-1741657883/10000000000 : ℝ)|=(1741657883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_3 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835994991/2000000000 : ℝ)*x 0 + (3849408303/10000000000 : ℝ)*x 1 + (566332357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835994991/2000000000 : ℝ)^4923 ≤ (16620802175029/50000000000000 : ℝ)^3899 := by
    have hnat : (835994991 : ℕ)^4923*50000000000000^3899 ≤ 16620802175029^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835994991 2000000000 16620802175029 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3849408303/10000000000 : ℝ)^4923 ≤ (14978744229931/50000000000000 : ℝ)^3899 := by
    have hnat : (3849408303 : ℕ)^4923*50000000000000^3899 ≤ 14978744229931^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3849408303 10000000000 14978744229931 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566332357/1250000000 : ℝ)^4923 ≤ (36800907176207/100000000000000 : ℝ)^3899 := by
    have hnat : (566332357 : ℕ)^4923*100000000000000^3899 ≤ 36800907176207^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566332357 1250000000 36800907176207 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835994991/2000000000 : ℝ), (3849408303/10000000000 : ℝ), (566332357/1250000000 : ℝ)] ![(16620802175029/50000000000000 : ℝ), (14978744229931/50000000000000 : ℝ), (36800907176207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835994991/2000000000 : ℝ)|^4923 ≤ (16620802175029/50000000000000 : ℝ)^3899
        have hw : |(835994991/2000000000 : ℝ)|=(835994991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3849408303/10000000000 : ℝ)|^4923 ≤ (14978744229931/50000000000000 : ℝ)^3899
        have hw : |(3849408303/10000000000 : ℝ)|=(3849408303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566332357/1250000000 : ℝ)|^4923 ≤ (36800907176207/100000000000000 : ℝ)^3899
        have hw : |(566332357/1250000000 : ℝ)|=(566332357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_4 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1606352573/10000000000 : ℝ)*x 0 + (5186094983/10000000000 : ℝ)*x 1 + (5445073901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1606352573/10000000000 : ℝ)^4923 ≤ (4968665033301/50000000000000 : ℝ)^3899 := by
    have hnat : (1606352573 : ℕ)^4923*50000000000000^3899 ≤ 4968665033301^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1606352573 10000000000 4968665033301 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186094983/10000000000 : ℝ)^4923 ≤ (21823208949417/50000000000000 : ℝ)^3899 := by
    have hnat : (5186094983 : ℕ)^4923*50000000000000^3899 ≤ 21823208949417^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186094983 10000000000 21823208949417 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445073901/10000000000 : ℝ)^4923 ≤ (9283250404919/20000000000000 : ℝ)^3899 := by
    have hnat : (5445073901 : ℕ)^4923*20000000000000^3899 ≤ 9283250404919^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445073901 10000000000 9283250404919 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1606352573/10000000000 : ℝ), (5186094983/10000000000 : ℝ), (5445073901/10000000000 : ℝ)] ![(4968665033301/50000000000000 : ℝ), (21823208949417/50000000000000 : ℝ), (9283250404919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1606352573/10000000000 : ℝ)|^4923 ≤ (4968665033301/50000000000000 : ℝ)^3899
        have hw : |(-1606352573/10000000000 : ℝ)|=(1606352573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186094983/10000000000 : ℝ)|^4923 ≤ (21823208949417/50000000000000 : ℝ)^3899
        have hw : |(5186094983/10000000000 : ℝ)|=(5186094983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445073901/10000000000 : ℝ)|^4923 ≤ (9283250404919/20000000000000 : ℝ)^3899
        have hw : |(5445073901/10000000000 : ℝ)|=(5445073901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_5 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638643531/5000000000 : ℝ)*x 0 + (-370172353/2500000000 : ℝ)*x 1 + (5445073901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638643531/5000000000 : ℝ)^4923 ≤ (44617686206057/100000000000000 : ℝ)^3899 := by
    have hnat : (2638643531 : ℕ)^4923*100000000000000^3899 ≤ 44617686206057^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638643531 5000000000 44617686206057 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370172353/2500000000 : ℝ)^4923 ≤ (112075771919/1250000000000 : ℝ)^3899 := by
    have hnat : (370172353 : ℕ)^4923*1250000000000^3899 ≤ 112075771919^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370172353 2500000000 112075771919 1250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445073901/10000000000 : ℝ)^4923 ≤ (9283250404919/20000000000000 : ℝ)^3899 := by
    have hnat : (5445073901 : ℕ)^4923*20000000000000^3899 ≤ 9283250404919^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445073901 10000000000 9283250404919 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638643531/5000000000 : ℝ), (-370172353/2500000000 : ℝ), (5445073901/10000000000 : ℝ)] ![(44617686206057/100000000000000 : ℝ), (112075771919/1250000000000 : ℝ), (9283250404919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638643531/5000000000 : ℝ)|^4923 ≤ (44617686206057/100000000000000 : ℝ)^3899
        have hw : |(2638643531/5000000000 : ℝ)|=(2638643531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-370172353/2500000000 : ℝ)|^4923 ≤ (112075771919/1250000000000 : ℝ)^3899
        have hw : |(-370172353/2500000000 : ℝ)|=(370172353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445073901/10000000000 : ℝ)|^4923 ≤ (9283250404919/20000000000000 : ℝ)^3899
        have hw : |(5445073901/10000000000 : ℝ)|=(5445073901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_6 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638643531/5000000000 : ℝ)*x 0 + (5445073901/10000000000 : ℝ)*x 1 + (-1480689413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638643531/5000000000 : ℝ)^4923 ≤ (44617686206057/100000000000000 : ℝ)^3899 := by
    have hnat : (2638643531 : ℕ)^4923*100000000000000^3899 ≤ 44617686206057^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638643531 5000000000 44617686206057 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445073901/10000000000 : ℝ)^4923 ≤ (9283250404919/20000000000000 : ℝ)^3899 := by
    have hnat : (5445073901 : ℕ)^4923*20000000000000^3899 ≤ 9283250404919^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445073901 10000000000 9283250404919 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1480689413/10000000000 : ℝ)^4923 ≤ (4483030880583/50000000000000 : ℝ)^3899 := by
    have hnat : (1480689413 : ℕ)^4923*50000000000000^3899 ≤ 4483030880583^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1480689413 10000000000 4483030880583 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638643531/5000000000 : ℝ), (5445073901/10000000000 : ℝ), (-1480689413/10000000000 : ℝ)] ![(44617686206057/100000000000000 : ℝ), (9283250404919/20000000000000 : ℝ), (4483030880583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638643531/5000000000 : ℝ)|^4923 ≤ (44617686206057/100000000000000 : ℝ)^3899
        have hw : |(2638643531/5000000000 : ℝ)|=(2638643531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445073901/10000000000 : ℝ)|^4923 ≤ (9283250404919/20000000000000 : ℝ)^3899
        have hw : |(5445073901/10000000000 : ℝ)|=(5445073901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1480689413/10000000000 : ℝ)|^4923 ≤ (4483030880583/50000000000000 : ℝ)^3899
        have hw : |(-1480689413/10000000000 : ℝ)|=(1480689413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_7 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4180145997/10000000000 : ℝ)*x 0 + (4525501877/10000000000 : ℝ)*x 1 + (3854614253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180145997/10000000000 : ℝ)^4923 ≤ (4155415227921/12500000000000 : ℝ)^3899 := by
    have hnat : (4180145997 : ℕ)^4923*12500000000000^3899 ≤ 4155415227921^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180145997 10000000000 4155415227921 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525501877/10000000000 : ℝ)^4923 ≤ (9187006406159/25000000000000 : ℝ)^3899 := by
    have hnat : (4525501877 : ℕ)^4923*25000000000000^3899 ≤ 9187006406159^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525501877 10000000000 9187006406159 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3854614253/10000000000 : ℝ)^4923 ≤ (15004326266427/50000000000000 : ℝ)^3899 := by
    have hnat : (3854614253 : ℕ)^4923*50000000000000^3899 ≤ 15004326266427^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3854614253 10000000000 15004326266427 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180145997/10000000000 : ℝ), (4525501877/10000000000 : ℝ), (3854614253/10000000000 : ℝ)] ![(4155415227921/12500000000000 : ℝ), (9187006406159/25000000000000 : ℝ), (15004326266427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180145997/10000000000 : ℝ)|^4923 ≤ (4155415227921/12500000000000 : ℝ)^3899
        have hw : |(4180145997/10000000000 : ℝ)|=(4180145997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525501877/10000000000 : ℝ)|^4923 ≤ (9187006406159/25000000000000 : ℝ)^3899
        have hw : |(4525501877/10000000000 : ℝ)|=(4525501877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3854614253/10000000000 : ℝ)|^4923 ≤ (15004326266427/50000000000000 : ℝ)^3899
        have hw : |(3854614253/10000000000 : ℝ)|=(3854614253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_8 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9616233/2500000000 : ℝ)*x 0 + (288560049/500000000 : ℝ)*x 1 + (2885756593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9616233/2500000000 : ℝ)^4923 ≤ (44647495183/50000000000000 : ℝ)^3899 := by
    have hnat : (9616233 : ℕ)^4923*50000000000000^3899 ≤ 44647495183^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9616233 2500000000 44647495183 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288560049/500000000 : ℝ)^4923 ≤ (49953646449761/100000000000000 : ℝ)^3899 := by
    have hnat : (288560049 : ℕ)^4923*100000000000000^3899 ≤ 49953646449761^3899*500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288560049 500000000 49953646449761 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2885756593/5000000000 : ℝ)^4923 ≤ (49957058551153/100000000000000 : ℝ)^3899 := by
    have hnat : (2885756593 : ℕ)^4923*100000000000000^3899 ≤ 49957058551153^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885756593 5000000000 49957058551153 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9616233/2500000000 : ℝ), (288560049/500000000 : ℝ), (2885756593/5000000000 : ℝ)] ![(44647495183/50000000000000 : ℝ), (49953646449761/100000000000000 : ℝ), (49957058551153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9616233/2500000000 : ℝ)|^4923 ≤ (44647495183/50000000000000 : ℝ)^3899
        have hw : |(-9616233/2500000000 : ℝ)|=(9616233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(288560049/500000000 : ℝ)|^4923 ≤ (49953646449761/100000000000000 : ℝ)^3899
        have hw : |(288560049/500000000 : ℝ)|=(288560049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2885756593/5000000000 : ℝ)|^4923 ≤ (49957058551153/100000000000000 : ℝ)^3899
        have hw : |(2885756593/5000000000 : ℝ)|=(2885756593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_9 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (621369123/5000000000 : ℝ)*x 0 + (-539946209/1250000000 : ℝ)*x 1 + (1627592983/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621369123/5000000000 : ℝ)^4923 ≤ (3593397754489/50000000000000 : ℝ)^3899 := by
    have hnat : (621369123 : ℕ)^4923*50000000000000^3899 ≤ 3593397754489^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621369123 5000000000 3593397754489 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539946209/1250000000 : ℝ)^4923 ≤ (17324698898501/50000000000000 : ℝ)^3899 := by
    have hnat : (539946209 : ℕ)^4923*50000000000000^3899 ≤ 17324698898501^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539946209 1250000000 17324698898501 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1627592983/2500000000 : ℝ)^4923 ≤ (3635237917477/6250000000000 : ℝ)^3899 := by
    have hnat : (1627592983 : ℕ)^4923*6250000000000^3899 ≤ 3635237917477^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627592983 2500000000 3635237917477 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(621369123/5000000000 : ℝ), (-539946209/1250000000 : ℝ), (1627592983/2500000000 : ℝ)] ![(3593397754489/50000000000000 : ℝ), (17324698898501/50000000000000 : ℝ), (3635237917477/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(621369123/5000000000 : ℝ)|^4923 ≤ (3593397754489/50000000000000 : ℝ)^3899
        have hw : |(621369123/5000000000 : ℝ)|=(621369123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539946209/1250000000 : ℝ)|^4923 ≤ (17324698898501/50000000000000 : ℝ)^3899
        have hw : |(-539946209/1250000000 : ℝ)|=(539946209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1627592983/2500000000 : ℝ)|^4923 ≤ (3635237917477/6250000000000 : ℝ)^3899
        have hw : |(1627592983/2500000000 : ℝ)|=(1627592983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_10 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (123836267/1000000000 : ℝ)*x 0 + (7186314437/10000000000 : ℝ)*x 1 + (-885133101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123836267/1000000000 : ℝ)^4923 ≤ (3577430272213/50000000000000 : ℝ)^3899 := by
    have hnat : (123836267 : ℕ)^4923*50000000000000^3899 ≤ 3577430272213^3899*1000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123836267 1000000000 3577430272213 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7186314437/10000000000 : ℝ)^4923 ≤ (65890110532869/100000000000000 : ℝ)^3899 := by
    have hnat : (7186314437 : ℕ)^4923*100000000000000^3899 ≤ 65890110532869^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7186314437 10000000000 65890110532869 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885133101/2500000000 : ℝ)^4923 ≤ (26955028904717/100000000000000 : ℝ)^3899 := by
    have hnat : (885133101 : ℕ)^4923*100000000000000^3899 ≤ 26955028904717^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885133101 2500000000 26955028904717 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123836267/1000000000 : ℝ), (7186314437/10000000000 : ℝ), (-885133101/2500000000 : ℝ)] ![(3577430272213/50000000000000 : ℝ), (65890110532869/100000000000000 : ℝ), (26955028904717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123836267/1000000000 : ℝ)|^4923 ≤ (3577430272213/50000000000000 : ℝ)^3899
        have hw : |(123836267/1000000000 : ℝ)|=(123836267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7186314437/10000000000 : ℝ)|^4923 ≤ (65890110532869/100000000000000 : ℝ)^3899
        have hw : |(7186314437/10000000000 : ℝ)|=(7186314437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-885133101/2500000000 : ℝ)|^4923 ≤ (26955028904717/100000000000000 : ℝ)^3899
        have hw : |(-885133101/2500000000 : ℝ)|=(885133101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_s4_11 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262053599/1250000000 : ℝ)*x 0 + (5126827931/10000000000 : ℝ)*x 1 + (2566074557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262053599/1250000000 : ℝ)^4923 ≤ (13908473218847/100000000000000 : ℝ)^3899 := by
    have hnat : (262053599 : ℕ)^4923*100000000000000^3899 ≤ 13908473218847^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262053599 1250000000 13908473218847 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5126827931/10000000000 : ℝ)^4923 ≤ (43017572344867/100000000000000 : ℝ)^3899 := by
    have hnat : (5126827931 : ℕ)^4923*100000000000000^3899 ≤ 43017572344867^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126827931 10000000000 43017572344867 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566074557/5000000000 : ℝ)^4923 ≤ (2692122151803/6250000000000 : ℝ)^3899 := by
    have hnat : (2566074557 : ℕ)^4923*6250000000000^3899 ≤ 2692122151803^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566074557 5000000000 2692122151803 6250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262053599/1250000000 : ℝ), (5126827931/10000000000 : ℝ), (2566074557/5000000000 : ℝ)] ![(13908473218847/100000000000000 : ℝ), (43017572344867/100000000000000 : ℝ), (2692122151803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262053599/1250000000 : ℝ)|^4923 ≤ (13908473218847/100000000000000 : ℝ)^3899
        have hw : |(262053599/1250000000 : ℝ)|=(262053599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5126827931/10000000000 : ℝ)|^4923 ≤ (43017572344867/100000000000000 : ℝ)^3899
        have hw : |(5126827931/10000000000 : ℝ)|=(5126827931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2566074557/5000000000 : ℝ)|^4923 ≤ (2692122151803/6250000000000 : ℝ)^3899
        have hw : |(2566074557/5000000000 : ℝ)|=(2566074557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1651_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2669/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8133/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10671/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16271/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10671/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10671/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16271/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10671/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10671/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16271/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10671/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10671/100000 : ℝ) ^ (4919/1024 : ℝ) ≤ (429346869970117/20000000000000000000 : ℝ) := by
    have hpowers : (10671/100000 : ℝ)^4919 ≤ (429346869970117/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10671 : ℕ)^4919*20000000000000000000^1024 ≤ 429346869970117^1024*100000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10671 100000 429346869970117 20000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10671/100000 : ℝ)) (X := (429346869970117/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16271/100000 : ℝ) ^ (4919/1024 : ℝ) ≤ (4071945836987541/25000000000000000000 : ℝ) := by
    have hpowers : (16271/100000 : ℝ)^4919 ≤ (4071945836987541/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16271 : ℕ)^4919*25000000000000000000^1024 ≤ 4071945836987541^1024*100000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16271 100000 4071945836987541 25000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16271/100000 : ℝ)) (X := (4071945836987541/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000429346869970117/10000000000000000000 : ℝ) ≤ (10000089376645997/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (10000429346869970117/10000000000000000000 : ℝ)^1024 ≤ (10000089376645997/10000000000000000 : ℝ)^4919 := by
      have hnat : (10000429346869970117 : ℕ)^1024*10000000000000000^4919 ≤ 10000089376645997^4919*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000429346869970117 10000000000000000000 10000089376645997 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000089376645997/10000000000000000 : ℝ)) (X := (10000429346869970117/10000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018434517697800749/100000000000000000000 : ℝ) ≤ (2500095931940151/2500000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (100018434517697800749/100000000000000000000 : ℝ)^1024 ≤ (2500095931940151/2500000000000000 : ℝ)^4919 := by
      have hnat : (100018434517697800749 : ℕ)^1024*2500000000000000^4919 ≤ 2500095931940151^4919*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018434517697800749 100000000000000000000 2500095931940151 2500000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500095931940151/2500000000000000 : ℝ)) (X := (100018434517697800749/100000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504071945836987541/12500000000000000000 : ℝ) ≤ (10000678078875211/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (12504071945836987541/12500000000000000000 : ℝ)^1024 ≤ (10000678078875211/10000000000000000 : ℝ)^4919 := by
      have hnat : (12504071945836987541 : ℕ)^1024*10000000000000000^4919 ≤ 10000678078875211^4919*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504071945836987541 12500000000000000000 10000678078875211 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000678078875211/10000000000000000 : ℝ)) (X := (12504071945836987541/12500000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(429346869970117/20000000000000000000 : ℝ) ≤ ((27997109233864820303/28000000000000000000 : ℝ)+2*(294351114607/560000000000000 : ℝ)*(10671/100000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (27997109233864820303/28000000000000000000 : ℝ)+2*(294351114607/560000000000000 : ℝ)*(10671/100000 : ℝ)=(10000089376645997/10000000000000000 : ℝ) by norm_num, show 1+2*(429346869970117/20000000000000000000 : ℝ)=(10000429346869970117/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4071945836987541/25000000000000000000 : ℝ)+(429346869970117/20000000000000000000 : ℝ) ≤ ((27997109233864820303/28000000000000000000 : ℝ)+(294351114607/560000000000000 : ℝ)*((16271/100000 : ℝ)+(10671/100000 : ℝ)))^(4919/1024 : ℝ) := by
    rw [show (27997109233864820303/28000000000000000000 : ℝ)+(294351114607/560000000000000 : ℝ)*((16271/100000 : ℝ)+(10671/100000 : ℝ))=(2500095931940151/2500000000000000 : ℝ) by norm_num, show 1+(4071945836987541/25000000000000000000 : ℝ)+(429346869970117/20000000000000000000 : ℝ)=(100018434517697800749/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4071945836987541/25000000000000000000 : ℝ) ≤ ((27997109233864820303/28000000000000000000 : ℝ)+2*(294351114607/560000000000000 : ℝ)*(16271/100000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (27997109233864820303/28000000000000000000 : ℝ)+2*(294351114607/560000000000000 : ℝ)*(16271/100000 : ℝ)=(10000678078875211/10000000000000000 : ℝ) by norm_num, show 1+2*(4071945836987541/25000000000000000000 : ℝ)=(12504071945836987541/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27997109233864820303/28000000000000000000 : ℝ)*(X 1 0+X 2 0)+(294351114607/560000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (10671/100000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (27997109233864820303/28000000000000000000 : ℝ)) (alpha := (294351114607/560000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27997109233864820303/28000000000000000000 : ℝ)*(X 0 1+X 2 1)+(294351114607/560000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (10671/100000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (27997109233864820303/28000000000000000000 : ℝ)) (alpha := (294351114607/560000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27997109233864820303/28000000000000000000 : ℝ)*(X 0 2+X 1 2)+(294351114607/560000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (10671/100000 : ℝ)) (hi := (16271/100000 : ℝ)) (c := (27997109233864820303/28000000000000000000 : ℝ)) (alpha := (294351114607/560000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-200786091/1250000000 : ℝ)*X 0 0+(5447084591/10000000000 : ℝ)*X 0 1+(1296026281/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347550043/10000000000 : ℝ)*X 1 0+(-34833059/200000000 : ℝ)*X 1 1+(1296027521/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((33422211/62500000 : ℝ)*X 2 0+(648012829/1250000000 : ℝ)*X 2 1+(-1741657883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835994991/2000000000 : ℝ)*X 0 0+(3849408303/10000000000 : ℝ)*X 0 1+(566332357/1250000000 : ℝ)*X 0 2+(835994991/2000000000 : ℝ)*X 1 0+(3849408303/10000000000 : ℝ)*X 1 1+(566332357/1250000000 : ℝ)*X 1 2+(835994991/2000000000 : ℝ)*X 2 0+(3849408303/10000000000 : ℝ)*X 2 1+(566332357/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1606352573/10000000000 : ℝ)*X 0 0+(5186094983/10000000000 : ℝ)*X 0 1+(5445073901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638643531/5000000000 : ℝ)*X 1 0+(-370172353/2500000000 : ℝ)*X 1 1+(5445073901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638643531/5000000000 : ℝ)*X 2 0+(5445073901/10000000000 : ℝ)*X 2 1+(-1480689413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180145997/10000000000 : ℝ)*X 0 0+(4525501877/10000000000 : ℝ)*X 0 1+(3854614253/10000000000 : ℝ)*X 0 2+(4180145997/10000000000 : ℝ)*X 1 0+(4525501877/10000000000 : ℝ)*X 1 1+(3854614253/10000000000 : ℝ)*X 1 2+(4180145997/10000000000 : ℝ)*X 2 0+(4525501877/10000000000 : ℝ)*X 2 1+(3854614253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-9616233/2500000000 : ℝ)*X 0 0+(288560049/500000000 : ℝ)*X 0 1+(2885756593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((621369123/5000000000 : ℝ)*X 1 0+(-539946209/1250000000 : ℝ)*X 1 1+(1627592983/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((123836267/1000000000 : ℝ)*X 2 0+(7186314437/10000000000 : ℝ)*X 2 1+(-885133101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((262053599/1250000000 : ℝ)*X 0 0+(5126827931/10000000000 : ℝ)*X 0 1+(2566074557/5000000000 : ℝ)*X 0 2+(262053599/1250000000 : ℝ)*X 1 0+(5126827931/10000000000 : ℝ)*X 1 1+(2566074557/5000000000 : ℝ)*X 1 2+(262053599/1250000000 : ℝ)*X 2 0+(5126827931/10000000000 : ℝ)*X 2 1+(2566074557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_s4_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2972881084009004268053847/3125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (535173897/100000000000000 : ℝ)*(upper4) + (873009749/100000000000000 : ℝ)*(lower5) + (82354103248781/3125000000000 : ℝ)*(major0) + (82354103248781/3125000000000 : ℝ)*(major1) + (82354103248781/3125000000000 : ℝ)*(major2) + (1901325114706217/50000000000000 : ℝ)*(sp0) + (1901360099350509/50000000000000 : ℝ)*(sp1) + (3802646034685837/100000000000000 : ℝ)*(sp2) + (183488723951791/12500000000000 : ℝ)*(sp3) + (272504359/400000000000 : ℝ)*(sp4) + (36639846361/50000000000000 : ℝ)*(sp6) + (32585895901/100000000000000 : ℝ)*(sp7) + (921599417/50000000000000 : ℝ)*(sp8) + (442161229/50000000000000 : ℝ)*(sp10) + (1467942377510229/100000000000000 : ℝ)*(f.failure) + (1901360099350509/50000000000000 : ℝ)*(f.sum) + (132615513603/62500000000000000000000000 : ℝ)*base65 + (16429208987907051/12500000000000000000000000000000 : ℝ)*base68 + (57344956312907051/12500000000000000000000000000000 : ℝ)*base70 + (63059205062907051/12500000000000000000000000000000 : ℝ)*base72 + (154454165739/31250000000000000000000000 : ℝ)*base73 + (141678879087907051/12500000000000000000000000000000 : ℝ)*base76 + (64234942187907051/12500000000000000000000000000000 : ℝ)*base78 + (28423146162092949/12500000000000000000000000000000 : ℝ)*base79 + (115915041581/125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1671761/1250000000000000000000 : ℝ)*base90 + (1671761/1250000000000000000000 : ℝ)*base92 + (1671761/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4208471648794551785996331/400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (124781101/100000000000000 : ℝ)*(lower1) + (254468867/100000000000000 : ℝ)*(lower3) + (88787263/50000000000000 : ℝ)*(lower5) + (10703762567513/400000000000 : ℝ)*(major0) + (10703762567513/400000000000 : ℝ)*(major1) + (10703762567513/400000000000 : ℝ)*(major2) + (1249515561/100000000000000 : ℝ)*(sp1) + (1930657570522891/50000000000000 : ℝ)*(sp4) + (1930658457343899/50000000000000 : ℝ)*(sp5) + (3861318185964077/100000000000000 : ℝ)*(sp6) + (1490560184893539/100000000000000 : ℝ)*(sp7) + (608983659/20000000000000 : ℝ)*(sp8) + (21760717/100000000000000 : ℝ)*(sp9) + (2562192909/100000000000000 : ℝ)*(sp11) + (93160171692903/6250000000000 : ℝ)*(f.failure) + (3861318185964077/100000000000000 : ℝ)*(f.sum) + (170447621529/112000000000000000000000000 : ℝ)*base66 + (40357770144566439/11200000000000000000000000000000 : ℝ)*base67 + (13047891613833561/11200000000000000000000000000000 : ℝ)*base70 + (122114643500233561/11200000000000000000000000000000 : ℝ)*base72 + (347275946007/112000000000000000000000000 : ℝ)*base73 + (37973479450633561/11200000000000000000000000000000 : ℝ)*base76 + (34342492381833561/11200000000000000000000000000000 : ℝ)*base78 + (11932941850633561/11200000000000000000000000000000 : ℝ)*base80 + (108700516887/112000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (303473/78125000000000000000 : ℝ)*base89 + (303473/78125000000000000000 : ℝ)*base91 + (303473/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1651_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16271/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10671/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8133/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1651_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1651_box_0 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1348665411/10000000000 : ℝ)*x 0 + (168994343/312500000 : ℝ)*x 1 + (2703909507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348665411/10000000000 : ℝ)^4923 ≤ (3984370467897/50000000000000 : ℝ)^3899 := by
    have hnat : (1348665411 : ℕ)^4923*50000000000000^3899 ≤ 3984370467897^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348665411 10000000000 3984370467897 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168994343/312500000 : ℝ)^4923 ≤ (23007814660853/50000000000000 : ℝ)^3899 := by
    have hnat : (168994343 : ℕ)^4923*50000000000000^3899 ≤ 23007814660853^3899*312500000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168994343 312500000 23007814660853 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703909507/5000000000 : ℝ)^4923 ≤ (11503907432493/25000000000000 : ℝ)^3899 := by
    have hnat : (2703909507 : ℕ)^4923*25000000000000^3899 ≤ 11503907432493^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703909507 5000000000 11503907432493 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1348665411/10000000000 : ℝ), (168994343/312500000 : ℝ), (2703909507/5000000000 : ℝ)] ![(3984370467897/50000000000000 : ℝ), (23007814660853/50000000000000 : ℝ), (11503907432493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1348665411/10000000000 : ℝ)|^4923 ≤ (3984370467897/50000000000000 : ℝ)^3899
        have hw : |(-1348665411/10000000000 : ℝ)|=(1348665411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168994343/312500000 : ℝ)|^4923 ≤ (23007814660853/50000000000000 : ℝ)^3899
        have hw : |(168994343/312500000 : ℝ)|=(168994343/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703909507/5000000000 : ℝ)|^4923 ≤ (11503907432493/25000000000000 : ℝ)^3899
        have hw : |(2703909507/5000000000 : ℝ)|=(2703909507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_1 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656383393/1250000000 : ℝ)*x 0 + (-784495923/5000000000 : ℝ)*x 1 + (67597737/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656383393/1250000000 : ℝ)^4923 ≤ (44337968171837/100000000000000 : ℝ)^3899 := by
    have hnat : (656383393 : ℕ)^4923*100000000000000^3899 ≤ 44337968171837^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656383393 1250000000 44337968171837 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (784495923/5000000000 : ℝ)^4923 ≤ (4823201326943/50000000000000 : ℝ)^3899 := by
    have hnat : (784495923 : ℕ)^4923*50000000000000^3899 ≤ 4823201326943^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784495923 5000000000 4823201326943 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67597737/125000000 : ℝ)^4923 ≤ (9203125829961/20000000000000 : ℝ)^3899 := by
    have hnat : (67597737 : ℕ)^4923*20000000000000^3899 ≤ 9203125829961^3899*125000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67597737 125000000 9203125829961 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656383393/1250000000 : ℝ), (-784495923/5000000000 : ℝ), (67597737/125000000 : ℝ)] ![(44337968171837/100000000000000 : ℝ), (4823201326943/50000000000000 : ℝ), (9203125829961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656383393/1250000000 : ℝ)|^4923 ≤ (44337968171837/100000000000000 : ℝ)^3899
        have hw : |(656383393/1250000000 : ℝ)|=(656383393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-784495923/5000000000 : ℝ)|^4923 ≤ (4823201326943/50000000000000 : ℝ)^3899
        have hw : |(-784495923/5000000000 : ℝ)|=(784495923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67597737/125000000 : ℝ)|^4923 ≤ (9203125829961/20000000000000 : ℝ)^3899
        have hw : |(67597737/125000000 : ℝ)|=(67597737/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_2 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251067463/10000000000 : ℝ)*x 0 + (1081563807/2000000000 : ℝ)*x 1 + (-196123913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251067463/10000000000 : ℝ)^4923 ≤ (177351886291/400000000000 : ℝ)^3899 := by
    have hnat : (5251067463 : ℕ)^4923*400000000000^3899 ≤ 177351886291^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251067463 10000000000 177351886291 400000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081563807/2000000000 : ℝ)^4923 ≤ (46015629955593/100000000000000 : ℝ)^3899 := by
    have hnat : (1081563807 : ℕ)^4923*100000000000000^3899 ≤ 46015629955593^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081563807 2000000000 46015629955593 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196123913/1250000000 : ℝ)^4923 ≤ (9646398446421/100000000000000 : ℝ)^3899 := by
    have hnat : (196123913 : ℕ)^4923*100000000000000^3899 ≤ 9646398446421^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196123913 1250000000 9646398446421 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251067463/10000000000 : ℝ), (1081563807/2000000000 : ℝ), (-196123913/1250000000 : ℝ)] ![(177351886291/400000000000 : ℝ), (46015629955593/100000000000000 : ℝ), (9646398446421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251067463/10000000000 : ℝ)|^4923 ≤ (177351886291/400000000000 : ℝ)^3899
        have hw : |(5251067463/10000000000 : ℝ)|=(5251067463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081563807/2000000000 : ℝ)|^4923 ≤ (46015629955593/100000000000000 : ℝ)^3899
        have hw : |(1081563807/2000000000 : ℝ)|=(1081563807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196123913/1250000000 : ℝ)|^4923 ≤ (9646398446421/100000000000000 : ℝ)^3899
        have hw : |(-196123913/1250000000 : ℝ)|=(196123913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_3 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4456713927/10000000000 : ℝ)*x 0 + (4053618711/10000000000 : ℝ)*x 1 + (4053619487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4456713927/10000000000 : ℝ)^4923 ≤ (3604416731801/10000000000000 : ℝ)^3899 := by
    have hnat : (4456713927 : ℕ)^4923*10000000000000^3899 ≤ 3604416731801^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4456713927 10000000000 3604416731801 10000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4053618711/10000000000 : ℝ)^4923 ≤ (6395582494099/20000000000000 : ℝ)^3899 := by
    have hnat : (4053618711 : ℕ)^4923*20000000000000^3899 ≤ 6395582494099^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053618711 10000000000 6395582494099 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4053619487/10000000000 : ℝ)^4923 ≤ (31977920199891/100000000000000 : ℝ)^3899 := by
    have hnat : (4053619487 : ℕ)^4923*100000000000000^3899 ≤ 31977920199891^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4053619487 10000000000 31977920199891 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4456713927/10000000000 : ℝ), (4053618711/10000000000 : ℝ), (4053619487/10000000000 : ℝ)] ![(3604416731801/10000000000000 : ℝ), (6395582494099/20000000000000 : ℝ), (31977920199891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4456713927/10000000000 : ℝ)|^4923 ≤ (3604416731801/10000000000000 : ℝ)^3899
        have hw : |(4456713927/10000000000 : ℝ)|=(4456713927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4053618711/10000000000 : ℝ)|^4923 ≤ (6395582494099/20000000000000 : ℝ)^3899
        have hw : |(4053618711/10000000000 : ℝ)|=(4053618711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4053619487/10000000000 : ℝ)|^4923 ≤ (31977920199891/100000000000000 : ℝ)^3899
        have hw : |(4053619487/10000000000 : ℝ)|=(4053619487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_4 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-937254977/5000000000 : ℝ)*x 0 + (5215767649/10000000000 : ℝ)*x 1 + (2607884167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937254977/5000000000 : ℝ)^4923 ≤ (301901464483/2500000000000 : ℝ)^3899 := by
    have hnat : (937254977 : ℕ)^4923*2500000000000^3899 ≤ 301901464483^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937254977 5000000000 301901464483 2500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215767649/10000000000 : ℝ)^4923 ≤ (8792393411827/20000000000000 : ℝ)^3899 := by
    have hnat : (5215767649 : ℕ)^4923*20000000000000^3899 ≤ 8792393411827^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215767649 10000000000 8792393411827 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607884167/5000000000 : ℝ)^4923 ≤ (4396197434911/10000000000000 : ℝ)^3899 := by
    have hnat : (2607884167 : ℕ)^4923*10000000000000^3899 ≤ 4396197434911^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607884167 5000000000 4396197434911 10000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937254977/5000000000 : ℝ), (5215767649/10000000000 : ℝ), (2607884167/5000000000 : ℝ)] ![(301901464483/2500000000000 : ℝ), (8792393411827/20000000000000 : ℝ), (4396197434911/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937254977/5000000000 : ℝ)|^4923 ≤ (301901464483/2500000000000 : ℝ)^3899
        have hw : |(-937254977/5000000000 : ℝ)|=(937254977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215767649/10000000000 : ℝ)|^4923 ≤ (8792393411827/20000000000000 : ℝ)^3899
        have hw : |(5215767649/10000000000 : ℝ)|=(5215767649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607884167/5000000000 : ℝ)|^4923 ≤ (4396197434911/10000000000000 : ℝ)^3899
        have hw : |(2607884167/5000000000 : ℝ)|=(2607884167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_5 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691434921/5000000000 : ℝ)*x 0 + (-330275169/2000000000 : ℝ)*x 1 + (5215767581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691434921/5000000000 : ℝ)^4923 ≤ (45747742216261/100000000000000 : ℝ)^3899 := by
    have hnat : (2691434921 : ℕ)^4923*100000000000000^3899 ≤ 45747742216261^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691434921 5000000000 45747742216261 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330275169/2000000000 : ℝ)^4923 ≤ (10290291427137/100000000000000 : ℝ)^3899 := by
    have hnat : (330275169 : ℕ)^4923*100000000000000^3899 ≤ 10290291427137^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330275169 2000000000 10290291427137 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215767581/10000000000 : ℝ)^4923 ≤ (43961966335459/100000000000000 : ℝ)^3899 := by
    have hnat : (5215767581 : ℕ)^4923*100000000000000^3899 ≤ 43961966335459^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215767581 10000000000 43961966335459 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691434921/5000000000 : ℝ), (-330275169/2000000000 : ℝ), (5215767581/10000000000 : ℝ)] ![(45747742216261/100000000000000 : ℝ), (10290291427137/100000000000000 : ℝ), (43961966335459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691434921/5000000000 : ℝ)|^4923 ≤ (45747742216261/100000000000000 : ℝ)^3899
        have hw : |(2691434921/5000000000 : ℝ)|=(2691434921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-330275169/2000000000 : ℝ)|^4923 ≤ (10290291427137/100000000000000 : ℝ)^3899
        have hw : |(-330275169/2000000000 : ℝ)|=(330275169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215767581/10000000000 : ℝ)|^4923 ≤ (43961966335459/100000000000000 : ℝ)^3899
        have hw : |(5215767581/10000000000 : ℝ)|=(5215767581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_6 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691434587/5000000000 : ℝ)*x 0 + (5215768323/10000000000 : ℝ)*x 1 + (-1651375753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691434587/5000000000 : ℝ)^4923 ≤ (22873867524041/50000000000000 : ℝ)^3899 := by
    have hnat : (2691434587 : ℕ)^4923*50000000000000^3899 ≤ 22873867524041^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691434587 5000000000 22873867524041 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215768323/10000000000 : ℝ)^4923 ≤ (8792394846409/20000000000000 : ℝ)^3899 := by
    have hnat : (5215768323 : ℕ)^4923*20000000000000^3899 ≤ 8792394846409^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215768323 10000000000 8792394846409 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1651375753/10000000000 : ℝ)^4923 ≤ (10290290703291/100000000000000 : ℝ)^3899 := by
    have hnat : (1651375753 : ℕ)^4923*100000000000000^3899 ≤ 10290290703291^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651375753 10000000000 10290290703291 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691434587/5000000000 : ℝ), (5215768323/10000000000 : ℝ), (-1651375753/10000000000 : ℝ)] ![(22873867524041/50000000000000 : ℝ), (8792394846409/20000000000000 : ℝ), (10290290703291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691434587/5000000000 : ℝ)|^4923 ≤ (22873867524041/50000000000000 : ℝ)^3899
        have hw : |(2691434587/5000000000 : ℝ)|=(2691434587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215768323/10000000000 : ℝ)|^4923 ≤ (8792394846409/20000000000000 : ℝ)^3899
        have hw : |(5215768323/10000000000 : ℝ)|=(5215768323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1651375753/10000000000 : ℝ)|^4923 ≤ (10290290703291/100000000000000 : ℝ)^3899
        have hw : |(-1651375753/10000000000 : ℝ)|=(1651375753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_7 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3896718949/10000000000 : ℝ)*x 0 + (2166645879/5000000000 : ℝ)*x 1 + (433329233/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3896718949/10000000000 : ℝ)^4923 ≤ (30423122957823/100000000000000 : ℝ)^3899 := by
    have hnat : (3896718949 : ℕ)^4923*100000000000000^3899 ≤ 30423122957823^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3896718949 10000000000 30423122957823 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166645879/5000000000 : ℝ)^4923 ≤ (17394217805949/50000000000000 : ℝ)^3899 := by
    have hnat : (2166645879 : ℕ)^4923*50000000000000^3899 ≤ 17394217805949^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166645879 5000000000 17394217805949 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433329233/1000000000 : ℝ)^4923 ≤ (695768828201/2000000000000 : ℝ)^3899 := by
    have hnat : (433329233 : ℕ)^4923*2000000000000^3899 ≤ 695768828201^3899*1000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433329233 1000000000 695768828201 2000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3896718949/10000000000 : ℝ), (2166645879/5000000000 : ℝ), (433329233/1000000000 : ℝ)] ![(30423122957823/100000000000000 : ℝ), (17394217805949/50000000000000 : ℝ), (695768828201/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3896718949/10000000000 : ℝ)|^4923 ≤ (30423122957823/100000000000000 : ℝ)^3899
        have hw : |(3896718949/10000000000 : ℝ)|=(3896718949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166645879/5000000000 : ℝ)|^4923 ≤ (17394217805949/50000000000000 : ℝ)^3899
        have hw : |(2166645879/5000000000 : ℝ)|=(2166645879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(433329233/1000000000 : ℝ)|^4923 ≤ (695768828201/2000000000000 : ℝ)^3899
        have hw : |(433329233/1000000000 : ℝ)|=(433329233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_8 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-440583493/2500000000 : ℝ)*x 0 + (5077622373/10000000000 : ℝ)*x 1 + (5437262533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440583493/2500000000 : ℝ)^4923 ≤ (2234175409947/20000000000000 : ℝ)^3899 := by
    have hnat : (440583493 : ℕ)^4923*20000000000000^3899 ≤ 2234175409947^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440583493 2500000000 2234175409947 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077622373/10000000000 : ℝ)^4923 ≤ (8499386135367/20000000000000 : ℝ)^3899 := by
    have hnat : (5077622373 : ℕ)^4923*20000000000000^3899 ≤ 8499386135367^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077622373 10000000000 8499386135367 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437262533/10000000000 : ℝ)^4923 ≤ (463321922657/1000000000000 : ℝ)^3899 := by
    have hnat : (5437262533 : ℕ)^4923*1000000000000^3899 ≤ 463321922657^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437262533 10000000000 463321922657 1000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440583493/2500000000 : ℝ), (5077622373/10000000000 : ℝ), (5437262533/10000000000 : ℝ)] ![(2234175409947/20000000000000 : ℝ), (8499386135367/20000000000000 : ℝ), (463321922657/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440583493/2500000000 : ℝ)|^4923 ≤ (2234175409947/20000000000000 : ℝ)^3899
        have hw : |(-440583493/2500000000 : ℝ)|=(440583493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077622373/10000000000 : ℝ)|^4923 ≤ (8499386135367/20000000000000 : ℝ)^3899
        have hw : |(5077622373/10000000000 : ℝ)|=(5077622373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437262533/10000000000 : ℝ)|^4923 ≤ (463321922657/1000000000000 : ℝ)^3899
        have hw : |(5437262533/10000000000 : ℝ)|=(5437262533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_9 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (163464433/312500000 : ℝ)*x 0 + (-777966563/5000000000 : ℝ)*x 1 + (2718631351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163464433/312500000 : ℝ)^4923 ≤ (344708321363/781250000000 : ℝ)^3899 := by
    have hnat : (163464433 : ℕ)^4923*781250000000^3899 ≤ 344708321363^3899*312500000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163464433 312500000 344708321363 781250000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (777966563/5000000000 : ℝ)^4923 ≤ (2386285191691/25000000000000 : ℝ)^3899 := by
    have hnat : (777966563 : ℕ)^4923*25000000000000^3899 ≤ 2386285191691^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777966563 5000000000 2386285191691 25000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718631351/5000000000 : ℝ)^4923 ≤ (46332194084001/100000000000000 : ℝ)^3899 := by
    have hnat : (2718631351 : ℕ)^4923*100000000000000^3899 ≤ 46332194084001^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718631351 5000000000 46332194084001 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163464433/312500000 : ℝ), (-777966563/5000000000 : ℝ), (2718631351/5000000000 : ℝ)] ![(344708321363/781250000000 : ℝ), (2386285191691/25000000000000 : ℝ), (46332194084001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163464433/312500000 : ℝ)|^4923 ≤ (344708321363/781250000000 : ℝ)^3899
        have hw : |(163464433/312500000 : ℝ)|=(163464433/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-777966563/5000000000 : ℝ)|^4923 ≤ (2386285191691/25000000000000 : ℝ)^3899
        have hw : |(-777966563/5000000000 : ℝ)|=(777966563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718631351/5000000000 : ℝ)|^4923 ≤ (46332194084001/100000000000000 : ℝ)^3899
        have hw : |(2718631351/5000000000 : ℝ)|=(2718631351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_10 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230862017/10000000000 : ℝ)*x 0 + (5437262619/10000000000 : ℝ)*x 1 + (-77796651/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230862017/10000000000 : ℝ)^4923 ≤ (5515333356147/12500000000000 : ℝ)^3899 := by
    have hnat : (5230862017 : ℕ)^4923*12500000000000^3899 ≤ 5515333356147^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230862017 10000000000 5515333356147 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437262619/10000000000 : ℝ)^4923 ≤ (46332193190989/100000000000000 : ℝ)^3899 := by
    have hnat : (5437262619 : ℕ)^4923*100000000000000^3899 ≤ 46332193190989^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437262619 10000000000 46332193190989 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77796651/500000000 : ℝ)^4923 ≤ (4772569972853/50000000000000 : ℝ)^3899 := by
    have hnat : (77796651 : ℕ)^4923*50000000000000^3899 ≤ 4772569972853^3899*500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77796651 500000000 4772569972853 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230862017/10000000000 : ℝ), (5437262619/10000000000 : ℝ), (-77796651/500000000 : ℝ)] ![(5515333356147/12500000000000 : ℝ), (46332193190989/100000000000000 : ℝ), (4772569972853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230862017/10000000000 : ℝ)|^4923 ≤ (5515333356147/12500000000000 : ℝ)^3899
        have hw : |(5230862017/10000000000 : ℝ)|=(5230862017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437262619/10000000000 : ℝ)|^4923 ≤ (46332193190989/100000000000000 : ℝ)^3899
        have hw : |(5437262619/10000000000 : ℝ)|=(5437262619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77796651/500000000 : ℝ)|^4923 ≤ (4772569972853/50000000000000 : ℝ)^3899
        have hw : |(-77796651/500000000 : ℝ)|=(77796651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_11 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4540191163/10000000000 : ℝ)*x 0 + (1002665913/2500000000 : ℝ)*x 1 + (2005331707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4540191163/10000000000 : ℝ)^4923 ≤ (4612337069537/12500000000000 : ℝ)^3899 := by
    have hnat : (4540191163 : ℕ)^4923*12500000000000^3899 ≤ 4612337069537^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540191163 10000000000 4612337069537 12500000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002665913/2500000000 : ℝ)^4923 ≤ (6310130579529/20000000000000 : ℝ)^3899 := by
    have hnat : (1002665913 : ℕ)^4923*20000000000000^3899 ≤ 6310130579529^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002665913 2500000000 6310130579529 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005331707/5000000000 : ℝ)^4923 ≤ (6310130106731/20000000000000 : ℝ)^3899 := by
    have hnat : (2005331707 : ℕ)^4923*20000000000000^3899 ≤ 6310130106731^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005331707 5000000000 6310130106731 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4540191163/10000000000 : ℝ), (1002665913/2500000000 : ℝ), (2005331707/5000000000 : ℝ)] ![(4612337069537/12500000000000 : ℝ), (6310130579529/20000000000000 : ℝ), (6310130106731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4540191163/10000000000 : ℝ)|^4923 ≤ (4612337069537/12500000000000 : ℝ)^3899
        have hw : |(4540191163/10000000000 : ℝ)|=(4540191163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002665913/2500000000 : ℝ)|^4923 ≤ (6310130579529/20000000000000 : ℝ)^3899
        have hw : |(1002665913/2500000000 : ℝ)|=(1002665913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005331707/5000000000 : ℝ)|^4923 ≤ (6310130106731/20000000000000 : ℝ)^3899
        have hw : |(2005331707/5000000000 : ℝ)|=(2005331707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_12 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-291813081/2000000000 : ℝ)*x 0 + (5540692291/10000000000 : ℝ)*x 1 + (1298987597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291813081/2000000000 : ℝ)^4923 ≤ (352042015611/4000000000000 : ℝ)^3899 := by
    have hnat : (291813081 : ℕ)^4923*4000000000000^3899 ≤ 352042015611^3899*2000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291813081 2000000000 352042015611 4000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5540692291/10000000000 : ℝ)^4923 ≤ (47447778448173/100000000000000 : ℝ)^3899 := by
    have hnat : (5540692291 : ℕ)^4923*100000000000000^3899 ≤ 47447778448173^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540692291 10000000000 47447778448173 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298987597/2500000000 : ℝ)^4923 ≤ (21875585577187/50000000000000 : ℝ)^3899 := by
    have hnat : (1298987597 : ℕ)^4923*50000000000000^3899 ≤ 21875585577187^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298987597 2500000000 21875585577187 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291813081/2000000000 : ℝ), (5540692291/10000000000 : ℝ), (1298987597/2500000000 : ℝ)] ![(352042015611/4000000000000 : ℝ), (47447778448173/100000000000000 : ℝ), (21875585577187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291813081/2000000000 : ℝ)|^4923 ≤ (352042015611/4000000000000 : ℝ)^3899
        have hw : |(-291813081/2000000000 : ℝ)|=(291813081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5540692291/10000000000 : ℝ)|^4923 ≤ (47447778448173/100000000000000 : ℝ)^3899
        have hw : |(5540692291/10000000000 : ℝ)|=(5540692291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298987597/2500000000 : ℝ)|^4923 ≤ (21875585577187/50000000000000 : ℝ)^3899
        have hw : |(1298987597/2500000000 : ℝ)|=(1298987597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_13 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698239877/5000000000 : ℝ)*x 0 + (-207449201/1250000000 : ℝ)*x 1 + (1298987661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698239877/5000000000 : ℝ)^4923 ≤ (22946918007753/50000000000000 : ℝ)^3899 := by
    have hnat : (2698239877 : ℕ)^4923*50000000000000^3899 ≤ 22946918007753^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698239877 5000000000 22946918007753 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207449201/1250000000 : ℝ)^4923 ≤ (10354990091923/100000000000000 : ℝ)^3899 := by
    have hnat : (207449201 : ℕ)^4923*100000000000000^3899 ≤ 10354990091923^3899*1250000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207449201 1250000000 10354990091923 100000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298987661/2500000000 : ℝ)^4923 ≤ (546889673451/1250000000000 : ℝ)^3899 := by
    have hnat : (1298987661 : ℕ)^4923*1250000000000^3899 ≤ 546889673451^3899*2500000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298987661 2500000000 546889673451 1250000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698239877/5000000000 : ℝ), (-207449201/1250000000 : ℝ), (1298987661/2500000000 : ℝ)] ![(22946918007753/50000000000000 : ℝ), (10354990091923/100000000000000 : ℝ), (546889673451/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698239877/5000000000 : ℝ)|^4923 ≤ (22946918007753/50000000000000 : ℝ)^3899
        have hw : |(2698239877/5000000000 : ℝ)|=(2698239877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207449201/1250000000 : ℝ)|^4923 ≤ (10354990091923/100000000000000 : ℝ)^3899
        have hw : |(-207449201/1250000000 : ℝ)|=(207449201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298987661/2500000000 : ℝ)|^4923 ≤ (546889673451/1250000000000 : ℝ)^3899
        have hw : |(1298987661/2500000000 : ℝ)|=(1298987661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_14 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107929593/200000000 : ℝ)*x 0 + (5195951067/10000000000 : ℝ)*x 1 + (-1659593179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107929593/200000000 : ℝ)^4923 ≤ (22946917449381/50000000000000 : ℝ)^3899 := by
    have hnat : (107929593 : ℕ)^4923*50000000000000^3899 ≤ 22946917449381^3899*200000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107929593 200000000 22946917449381 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195951067/10000000000 : ℝ)^4923 ≤ (21875589186637/50000000000000 : ℝ)^3899 := by
    have hnat : (5195951067 : ℕ)^4923*50000000000000^3899 ≤ 21875589186637^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195951067 10000000000 21875589186637 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1659593179/10000000000 : ℝ)^4923 ≤ (2070997342439/20000000000000 : ℝ)^3899 := by
    have hnat : (1659593179 : ℕ)^4923*20000000000000^3899 ≤ 2070997342439^3899*10000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1659593179 10000000000 2070997342439 20000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107929593/200000000 : ℝ), (5195951067/10000000000 : ℝ), (-1659593179/10000000000 : ℝ)] ![(22946917449381/50000000000000 : ℝ), (21875589186637/50000000000000 : ℝ), (2070997342439/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107929593/200000000 : ℝ)|^4923 ≤ (22946917449381/50000000000000 : ℝ)^3899
        have hw : |(107929593/200000000 : ℝ)|=(107929593/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195951067/10000000000 : ℝ)|^4923 ≤ (21875589186637/50000000000000 : ℝ)^3899
        have hw : |(5195951067/10000000000 : ℝ)|=(5195951067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1659593179/10000000000 : ℝ)|^4923 ≤ (2070997342439/20000000000000 : ℝ)^3899
        have hw : |(-1659593179/10000000000 : ℝ)|=(1659593179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1651_box_15 (p : ℝ) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1918652709/5000000000 : ℝ)*x 0 + (68157781/156250000 : ℝ)*x 1 + (2181049591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1918652709/5000000000 : ℝ)^4923 ≤ (2983861156653/10000000000000 : ℝ)^3899 := by
    have hnat : (1918652709 : ℕ)^4923*10000000000000^3899 ≤ 2983861156653^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918652709 5000000000 2983861156653 10000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68157781/156250000 : ℝ)^4923 ≤ (17540344065791/50000000000000 : ℝ)^3899 := by
    have hnat : (68157781 : ℕ)^4923*50000000000000^3899 ≤ 17540344065791^3899*156250000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68157781 156250000 17540344065791 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181049591/5000000000 : ℝ)^4923 ≤ (17540350148207/50000000000000 : ℝ)^3899 := by
    have hnat : (2181049591 : ℕ)^4923*50000000000000^3899 ≤ 17540350148207^3899*5000000000^4923 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181049591 5000000000 17540350148207 50000000000000 4923 3899 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4923/1024 : ℝ)) 4923 3899 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1918652709/5000000000 : ℝ), (68157781/156250000 : ℝ), (2181049591/5000000000 : ℝ)] ![(2983861156653/10000000000000 : ℝ), (17540344065791/50000000000000 : ℝ), (17540350148207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1918652709/5000000000 : ℝ)|^4923 ≤ (2983861156653/10000000000000 : ℝ)^3899
        have hw : |(1918652709/5000000000 : ℝ)|=(1918652709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68157781/156250000 : ℝ)|^4923 ≤ (17540344065791/50000000000000 : ℝ)^3899
        have hw : |(68157781/156250000 : ℝ)|=(68157781/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2181049591/5000000000 : ℝ)|^4923 ≤ (17540350148207/50000000000000 : ℝ)^3899
        have hw : |(2181049591/5000000000 : ℝ)|=(2181049591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1651_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8133/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(4067/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58637/100000 : ℝ) ∧ (16243/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88233/100000 : ℝ) := by
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
  have lower0 : (2669/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8133/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2669/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8133/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2669/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8133/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2669/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8133/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2669/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8133/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2669/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2669/25000 : ℝ) ^ (4919/1024 : ℝ) ≤ (2151570581188579/100000000000000000000 : ℝ) := by
    have hpowers : (2669/25000 : ℝ)^4919 ≤ (2151570581188579/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2669 : ℕ)^4919*100000000000000000000^1024 ≤ 2151570581188579^1024*25000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2669 25000 2151570581188579 100000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2669/25000 : ℝ)) (X := (2151570581188579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8133/50000 : ℝ) ^ (4919/1024 : ℝ) ≤ (16263754066034841/100000000000000000000 : ℝ) := by
    have hpowers : (8133/50000 : ℝ)^4919 ≤ (16263754066034841/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8133 : ℕ)^4919*100000000000000000000^1024 ≤ 16263754066034841^1024*50000^4919 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8133 50000 16263754066034841 100000000000000000000 4919 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8133/50000 : ℝ)) (X := (16263754066034841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002151570581188579/50000000000000000000 : ℝ) ≤ (5000044788996557/5000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (50002151570581188579/50000000000000000000 : ℝ)^1024 ≤ (5000044788996557/5000000000000000 : ℝ)^4919 := by
      have hnat : (50002151570581188579 : ℕ)^1024*5000000000000000^4919 ≤ 5000044788996557^4919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002151570581188579 50000000000000000000 5000044788996557 5000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000044788996557/5000000000000000 : ℝ)) (X := (50002151570581188579/50000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5000920766232361171/5000000000000000000 : ℝ) ≤ (10000383328272559/10000000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (5000920766232361171/5000000000000000000 : ℝ)^1024 ≤ (10000383328272559/10000000000000000 : ℝ)^4919 := by
      have hnat : (5000920766232361171 : ℕ)^1024*10000000000000000^4919 ≤ 10000383328272559^4919*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000920766232361171 5000000000000000000 10000383328272559 10000000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000383328272559/10000000000000000 : ℝ)) (X := (5000920766232361171/5000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016263754066034841/50000000000000000000 : ℝ) ≤ (2500169269638001/2500000000000000 : ℝ) ^ (4919/1024 : ℝ) := by
    have hpowers : (50016263754066034841/50000000000000000000 : ℝ)^1024 ≤ (2500169269638001/2500000000000000 : ℝ)^4919 := by
      have hnat : (50016263754066034841 : ℕ)^1024*2500000000000000^4919 ≤ 2500169269638001^4919*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016263754066034841 50000000000000000000 2500169269638001 2500000000000000 1024 4919 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500169269638001/2500000000000000 : ℝ)) (X := (50016263754066034841/50000000000000000000 : ℝ)) (by norm_num) 4919 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2151570581188579/100000000000000000000 : ℝ) ≤ ((2794711429250739881/2795000000000000000 : ℝ)+2*(58750055889/111800000000000 : ℝ)*(2669/25000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (2794711429250739881/2795000000000000000 : ℝ)+2*(58750055889/111800000000000 : ℝ)*(2669/25000 : ℝ)=(5000044788996557/5000000000000000 : ℝ) by norm_num, show 1+2*(2151570581188579/100000000000000000000 : ℝ)=(50002151570581188579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16263754066034841/100000000000000000000 : ℝ)+(2151570581188579/100000000000000000000 : ℝ) ≤ ((2794711429250739881/2795000000000000000 : ℝ)+(58750055889/111800000000000 : ℝ)*((8133/50000 : ℝ)+(2669/25000 : ℝ)))^(4919/1024 : ℝ) := by
    rw [show (2794711429250739881/2795000000000000000 : ℝ)+(58750055889/111800000000000 : ℝ)*((8133/50000 : ℝ)+(2669/25000 : ℝ))=(10000383328272559/10000000000000000 : ℝ) by norm_num, show 1+(16263754066034841/100000000000000000000 : ℝ)+(2151570581188579/100000000000000000000 : ℝ)=(5000920766232361171/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16263754066034841/100000000000000000000 : ℝ) ≤ ((2794711429250739881/2795000000000000000 : ℝ)+2*(58750055889/111800000000000 : ℝ)*(8133/50000 : ℝ))^(4919/1024 : ℝ) := by
    rw [show (2794711429250739881/2795000000000000000 : ℝ)+2*(58750055889/111800000000000 : ℝ)*(8133/50000 : ℝ)=(2500169269638001/2500000000000000 : ℝ) by norm_num, show 1+2*(16263754066034841/100000000000000000000 : ℝ)=(50016263754066034841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2794711429250739881/2795000000000000000 : ℝ)*(X 1 0+X 2 0)+(58750055889/111800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (8133/50000 : ℝ)) (c := (2794711429250739881/2795000000000000000 : ℝ)) (alpha := (58750055889/111800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2794711429250739881/2795000000000000000 : ℝ)*(X 0 1+X 2 1)+(58750055889/111800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (8133/50000 : ℝ)) (c := (2794711429250739881/2795000000000000000 : ℝ)) (alpha := (58750055889/111800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2794711429250739881/2795000000000000000 : ℝ)*(X 0 2+X 1 2)+(58750055889/111800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4919/1024 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (8133/50000 : ℝ)) (c := (2794711429250739881/2795000000000000000 : ℝ)) (alpha := (58750055889/111800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1348665411/10000000000 : ℝ)*X 0 0+(168994343/312500000 : ℝ)*X 0 1+(2703909507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((656383393/1250000000 : ℝ)*X 1 0+(-784495923/5000000000 : ℝ)*X 1 1+(67597737/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251067463/10000000000 : ℝ)*X 2 0+(1081563807/2000000000 : ℝ)*X 2 1+(-196123913/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4456713927/10000000000 : ℝ)*X 0 0+(4053618711/10000000000 : ℝ)*X 0 1+(4053619487/10000000000 : ℝ)*X 0 2+(4456713927/10000000000 : ℝ)*X 1 0+(4053618711/10000000000 : ℝ)*X 1 1+(4053619487/10000000000 : ℝ)*X 1 2+(4456713927/10000000000 : ℝ)*X 2 0+(4053618711/10000000000 : ℝ)*X 2 1+(4053619487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-937254977/5000000000 : ℝ)*X 0 0+(5215767649/10000000000 : ℝ)*X 0 1+(2607884167/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2691434921/5000000000 : ℝ)*X 1 0+(-330275169/2000000000 : ℝ)*X 1 1+(5215767581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691434587/5000000000 : ℝ)*X 2 0+(5215768323/10000000000 : ℝ)*X 2 1+(-1651375753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3896718949/10000000000 : ℝ)*X 0 0+(2166645879/5000000000 : ℝ)*X 0 1+(433329233/1000000000 : ℝ)*X 0 2+(3896718949/10000000000 : ℝ)*X 1 0+(2166645879/5000000000 : ℝ)*X 1 1+(433329233/1000000000 : ℝ)*X 1 2+(3896718949/10000000000 : ℝ)*X 2 0+(2166645879/5000000000 : ℝ)*X 2 1+(433329233/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-440583493/2500000000 : ℝ)*X 0 0+(5077622373/10000000000 : ℝ)*X 0 1+(5437262533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((163464433/312500000 : ℝ)*X 1 0+(-777966563/5000000000 : ℝ)*X 1 1+(2718631351/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230862017/10000000000 : ℝ)*X 2 0+(5437262619/10000000000 : ℝ)*X 2 1+(-77796651/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4540191163/10000000000 : ℝ)*X 0 0+(1002665913/2500000000 : ℝ)*X 0 1+(2005331707/5000000000 : ℝ)*X 0 2+(4540191163/10000000000 : ℝ)*X 1 0+(1002665913/2500000000 : ℝ)*X 1 1+(2005331707/5000000000 : ℝ)*X 1 2+(4540191163/10000000000 : ℝ)*X 2 0+(1002665913/2500000000 : ℝ)*X 2 1+(2005331707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-291813081/2000000000 : ℝ)*X 0 0+(5540692291/10000000000 : ℝ)*X 0 1+(1298987597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2698239877/5000000000 : ℝ)*X 1 0+(-207449201/1250000000 : ℝ)*X 1 1+(1298987661/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((107929593/200000000 : ℝ)*X 2 0+(5195951067/10000000000 : ℝ)*X 2 1+(-1659593179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1918652709/5000000000 : ℝ)*X 0 0+(68157781/156250000 : ℝ)*X 0 1+(2181049591/5000000000 : ℝ)*X 0 2+(1918652709/5000000000 : ℝ)*X 1 0+(68157781/156250000 : ℝ)*X 1 1+(2181049591/5000000000 : ℝ)*X 1 2+(1918652709/5000000000 : ℝ)*X 2 0+(68157781/156250000 : ℝ)*X 2 1+(2181049591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1651_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-4067/6250 : ℝ) ≤ (-18186847410595771474256284168161/27950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (279039/4000000000000 : ℝ)*(lower3) + (8279637/10000000000000 : ℝ)*(lower4) + (2182463/12500000000000 : ℝ)*(upper5) + (880427932788433/50000000000000 : ℝ)*(major0) + (880427932788433/50000000000000 : ℝ)*(major1) + (1760855865576867/100000000000000 : ℝ)*(major2) + (1809636243/20000000000000 : ℝ)*(sp1) + (2342507319/100000000000000 : ℝ)*(sp2) + (2210611827/100000000000000 : ℝ)*(sp3) + (1281278301475299/50000000000000 : ℝ)*(sp4) + (320319214698051/12500000000000 : ℝ)*(sp5) + (40040006613411/1562500000000 : ℝ)*(sp6) + (490418247638941/50000000000000 : ℝ)*(sp7) + (246512601/4000000000000 : ℝ)*(sp12) + (980838705889709/100000000000000 : ℝ)*(f.failure) + (2562562765765623/100000000000000 : ℝ)*(f.sum) + (3557016014751/860000000000000000000000000 : ℝ)*base66 + (1035860994531866027/139750000000000000000000000000000 : ℝ)*base68 + (2573210058365282827/279500000000000000000000000000000 : ℝ)*base69 + (1020971500298616027/139750000000000000000000000000000 : ℝ)*base72 + (3394782065531/860000000000000000000000000 : ℝ)*base74 + (1864797738893282827/279500000000000000000000000000000 : ℝ)*base75 + (452121084802978527/139750000000000000000000000000000 : ℝ)*base78 + (602649956185478527/139750000000000000000000000000000 : ℝ)*base80 + (2407533271129/1397500000000000000000000000 : ℝ)*base82 + (14748919/1250000000000000000000 : ℝ)*base89 + (14748919/1250000000000000000000 : ℝ)*base91 + (2248919/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58637/100000 : ℝ) ≤ (16389600296232756668188088026773/27950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75712477/100000000000000 : ℝ)*(upper0) + (48290777/100000000000000 : ℝ)*(lower1) + (20882917/50000000000000 : ℝ)*(lower3) + (30022697/20000000000000 : ℝ)*(upper4) + (16739089/100000000000000 : ℝ)*(upper5) + (370278777375089/20000000000000 : ℝ)*(major0) + (370278777375089/20000000000000 : ℝ)*(major1) + (370278777375089/20000000000000 : ℝ)*(major2) + (265197089796903/10000000000000 : ℝ)*(sp0) + (1325981909083663/50000000000000 : ℝ)*(sp1) + (1325983506268063/50000000000000 : ℝ)*(sp2) + (64454408918221/6250000000000 : ℝ)*(sp3) + (485679113/12500000000000 : ℝ)*(sp6) + (884975213/12500000000000 : ℝ)*(sp9) + (64454408918221/6250000000000 : ℝ)*(f.failure) + (265197089796903/10000000000000 : ℝ)*(f.sum) + (719047548633/223600000000000000000000000 : ℝ)*base65 + (41381030317849409/55900000000000000000000000000000 : ℝ)*base67 + (182479188430550591/55900000000000000000000000000000 : ℝ)*base70 + (430449610540249409/55900000000000000000000000000000 : ℝ)*base71 + (8772591479207/1118000000000000000000000000 : ℝ)*base74 + (24719262556249409/55900000000000000000000000000000 : ℝ)*base75 + (229923449850849409/55900000000000000000000000000000 : ℝ)*base77 + (368854822001950591/55900000000000000000000000000000 : ℝ)*base80 + (9663947634767/1118000000000000000000000000 : ℝ)*base82 + (324461/78125000000000000000 : ℝ)*base89 + (324461/78125000000000000000 : ℝ)*base91 + (324461/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16243/20000 : ℝ) ≤ (14187635460599822657543022004623/17468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19226957/100000000000000 : ℝ)*(lower3) + (52387343/100000000000000 : ℝ)*(upper4) + (10234983/50000000000000 : ℝ)*(lower5) + (486430927701111/25000000000000 : ℝ)*(major0) + (486430927701111/25000000000000 : ℝ)*(major1) + (486430927701111/25000000000000 : ℝ)*(major2) + (1245766817/50000000000000 : ℝ)*(sp0) + (24981329237/100000000000000 : ℝ)*(sp1) + (28752552451/100000000000000 : ℝ)*(sp2) + (3245309317/25000000000000 : ℝ)*(sp3) + (1390279007481703/50000000000000 : ℝ)*(sp8) + (1390267762583901/50000000000000 : ℝ)*(sp9) + (2780531753944589/100000000000000 : ℝ)*(sp10) + (1083801522739261/100000000000000 : ℝ)*(sp11) + (1083814503976529/100000000000000 : ℝ)*(f.failure) + (34757006331213/1250000000000 : ℝ)*(f.sum) + (10552593519823/2795000000000000000000000000 : ℝ)*base65 + (418968840454567209/69875000000000000000000000000000 : ℝ)*base68 + (539086683731817209/69875000000000000000000000000000 : ℝ)*base70 + (213613190615057791/69875000000000000000000000000000 : ℝ)*base71 + (1908840370347/698750000000000000000000000 : ℝ)*base73 + (202377942450567209/69875000000000000000000000000000 : ℝ)*base76 + (543225866381692209/69875000000000000000000000000000 : ℝ)*base78 + (736998065965317209/69875000000000000000000000000000 : ℝ)*base80 + (1025151145747/698750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8541539/1250000000000000000000 : ℝ)*base89 + (8541539/1250000000000000000000 : ℝ)*base91 + (8541539/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-88233/100000 : ℝ) ≤ (-4932093106684750064671204358103/5590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1801469/100000000000000 : ℝ)*(lower0) + (36723447/20000000000000 : ℝ)*(lower1) + (94718323/100000000000000 : ℝ)*(lower2) + (79594432033593/4000000000000 : ℝ)*(major0) + (79594432033593/4000000000000 : ℝ)*(major1) + (79594432033593/4000000000000 : ℝ)*(major2) + (7568130791/100000000000000 : ℝ)*(sp0) + (136097443181/100000000000000 : ℝ)*(sp5) + (2216729493/5000000000000 : ℝ)*(sp6) + (15259387337/50000000000000 : ℝ)*(sp7) + (580144866649993/20000000000000 : ℝ)*(sp12) + (116023832157503/4000000000000 : ℝ)*(sp13) + (181292972924431/6250000000000 : ℝ)*(sp14) + (138546174603679/12500000000000 : ℝ)*(sp15) + (554199957802053/50000000000000 : ℝ)*(f.failure) + (725182975345189/25000000000000 : ℝ)*(f.sum) + (5221835734683/1118000000000000000000000000 : ℝ)*base66 + (20799994370732567/11180000000000000000000000000000 : ℝ)*base68 + (31825260118592567/11180000000000000000000000000000 : ℝ)*base70 + (9791633565472567/11180000000000000000000000000000 : ℝ)*base72 + (905777442889/223600000000000000000000000 : ℝ)*base74 + (54799790809652567/11180000000000000000000000000000 : ℝ)*base76 + (78162231389312567/11180000000000000000000000000000 : ℝ)*base78 + (69442843738312567/11180000000000000000000000000000 : ℝ)*base80 + (521318181911/223600000000000000000000000 : ℝ)*base82 + (4288623/625000000000000000000 : ℝ)*base89 + (4288623/625000000000000000000 : ℝ)*base91 + (4288623/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1651_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8133/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(4067/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(58637/100000 : ℝ) else (16243/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88233/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1651_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1651_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(4067/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(58637/100000 : ℝ) else (16243/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88233/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1651_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1651_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1651_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4919/1024 : ℝ) ≤ p) (hpb : p ≤ (4923/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22440691/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8171/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10607/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(4067/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(58637/100000 : ℝ) else (16243/20000 : ℝ) ≤ X j i ∧ X j i ≤ (88233/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1651_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:05.613204+00:00
-- url     : https://prove2.me/submissions/b67784bf-678b-4227-a7d6-cc92915a6f43

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
theorem support_rectangle_w1195_s0_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875149139/10000000000 : ℝ)*x 0 + (3021080639/5000000000 : ℝ)*x 1 + (2393569321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875149139/10000000000 : ℝ)^2097 ≤ (5459787601739/50000000000000 : ℝ)^1585 := by
    have hnat : (1875149139 : ℕ)^2097*50000000000000^1585 ≤ 5459787601739^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875149139 10000000000 5459787601739 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021080639/5000000000 : ℝ)^2097 ≤ (205386176293/400000000000 : ℝ)^1585 := by
    have hnat : (3021080639 : ℕ)^2097*400000000000^1585 ≤ 205386176293^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021080639 5000000000 205386176293 400000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2393569321/5000000000 : ℝ)^2097 ≤ (9433470177411/25000000000000 : ℝ)^1585 := by
    have hnat : (2393569321 : ℕ)^2097*25000000000000^1585 ≤ 9433470177411^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393569321 5000000000 9433470177411 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875149139/10000000000 : ℝ), (3021080639/5000000000 : ℝ), (2393569321/5000000000 : ℝ)] ![(5459787601739/50000000000000 : ℝ), (205386176293/400000000000 : ℝ), (9433470177411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875149139/10000000000 : ℝ)|^2097 ≤ (5459787601739/50000000000000 : ℝ)^1585
        have hw : |(-1875149139/10000000000 : ℝ)|=(1875149139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021080639/5000000000 : ℝ)|^2097 ≤ (205386176293/400000000000 : ℝ)^1585
        have hw : |(3021080639/5000000000 : ℝ)|=(3021080639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2393569321/5000000000 : ℝ)|^2097 ≤ (9433470177411/25000000000000 : ℝ)^1585
        have hw : |(2393569321/5000000000 : ℝ)|=(2393569321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5513807393/10000000000 : ℝ)*x 0 + (-2593906543/10000000000 : ℝ)*x 1 + (4787138601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513807393/10000000000 : ℝ)^2097 ≤ (45491799343837/100000000000000 : ℝ)^1585 := by
    have hnat : (5513807393 : ℕ)^2097*100000000000000^1585 ≤ 45491799343837^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513807393 10000000000 45491799343837 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593906543/10000000000 : ℝ)^2097 ≤ (16774320358491/100000000000000 : ℝ)^1585 := by
    have hnat : (2593906543 : ℕ)^2097*100000000000000^1585 ≤ 16774320358491^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593906543 10000000000 16774320358491 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787138601/10000000000 : ℝ)^2097 ≤ (4716735035259/12500000000000 : ℝ)^1585 := by
    have hnat : (4787138601 : ℕ)^2097*12500000000000^1585 ≤ 4716735035259^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787138601 10000000000 4716735035259 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513807393/10000000000 : ℝ), (-2593906543/10000000000 : ℝ), (4787138601/10000000000 : ℝ)] ![(45491799343837/100000000000000 : ℝ), (16774320358491/100000000000000 : ℝ), (4716735035259/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513807393/10000000000 : ℝ)|^2097 ≤ (45491799343837/100000000000000 : ℝ)^1585
        have hw : |(5513807393/10000000000 : ℝ)|=(5513807393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2593906543/10000000000 : ℝ)|^2097 ≤ (16774320358491/100000000000000 : ℝ)^1585
        have hw : |(-2593906543/10000000000 : ℝ)|=(2593906543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787138601/10000000000 : ℝ)|^2097 ≤ (4716735035259/12500000000000 : ℝ)^1585
        have hw : |(4787138601/10000000000 : ℝ)|=(4787138601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2756903813/5000000000 : ℝ)*x 0 + (2393569193/5000000000 : ℝ)*x 1 + (-2593906507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756903813/5000000000 : ℝ)^2097 ≤ (4549180188719/10000000000000 : ℝ)^1585 := by
    have hnat : (2756903813 : ℕ)^2097*10000000000000^1585 ≤ 4549180188719^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756903813 5000000000 4549180188719 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2393569193/5000000000 : ℝ)^2097 ≤ (37733878039931/100000000000000 : ℝ)^1585 := by
    have hnat : (2393569193 : ℕ)^2097*100000000000000^1585 ≤ 37733878039931^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393569193 5000000000 37733878039931 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2593906507/10000000000 : ℝ)^2097 ≤ (16774320050483/100000000000000 : ℝ)^1585 := by
    have hnat : (2593906507 : ℕ)^2097*100000000000000^1585 ≤ 16774320050483^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593906507 10000000000 16774320050483 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756903813/5000000000 : ℝ), (2393569193/5000000000 : ℝ), (-2593906507/10000000000 : ℝ)] ![(4549180188719/10000000000000 : ℝ), (37733878039931/100000000000000 : ℝ), (16774320050483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756903813/5000000000 : ℝ)|^2097 ≤ (4549180188719/10000000000000 : ℝ)^1585
        have hw : |(2756903813/5000000000 : ℝ)|=(2756903813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2393569193/5000000000 : ℝ)|^2097 ≤ (37733878039931/100000000000000 : ℝ)^1585
        have hw : |(2393569193/5000000000 : ℝ)|=(2393569193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2593906507/10000000000 : ℝ)|^2097 ≤ (16774320050483/100000000000000 : ℝ)^1585
        have hw : |(-2593906507/10000000000 : ℝ)|=(2593906507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4196738067/10000000000 : ℝ)*x 0 + (77968737/250000000 : ℝ)*x 1 + (2820783683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196738067/10000000000 : ℝ)^2097 ≤ (15851548533621/50000000000000 : ℝ)^1585 := by
    have hnat : (4196738067 : ℕ)^2097*50000000000000^1585 ≤ 15851548533621^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196738067 10000000000 15851548533621 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77968737/250000000 : ℝ)^2097 ≤ (21405324819991/100000000000000 : ℝ)^1585 := by
    have hnat : (77968737 : ℕ)^2097*100000000000000^1585 ≤ 21405324819991^1585*250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77968737 250000000 21405324819991 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2820783683/5000000000 : ℝ)^2097 ≤ (46891578096909/100000000000000 : ℝ)^1585 := by
    have hnat : (2820783683 : ℕ)^2097*100000000000000^1585 ≤ 46891578096909^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820783683 5000000000 46891578096909 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196738067/10000000000 : ℝ), (77968737/250000000 : ℝ), (2820783683/5000000000 : ℝ)] ![(15851548533621/50000000000000 : ℝ), (21405324819991/100000000000000 : ℝ), (46891578096909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196738067/10000000000 : ℝ)|^2097 ≤ (15851548533621/50000000000000 : ℝ)^1585
        have hw : |(4196738067/10000000000 : ℝ)|=(4196738067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77968737/250000000 : ℝ)|^2097 ≤ (21405324819991/100000000000000 : ℝ)^1585
        have hw : |(77968737/250000000 : ℝ)|=(77968737/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2820783683/5000000000 : ℝ)|^2097 ≤ (46891578096909/100000000000000 : ℝ)^1585
        have hw : |(2820783683/5000000000 : ℝ)|=(2820783683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880140569/10000000000 : ℝ)*x 0 + (481948591/1000000000 : ℝ)*x 1 + (6008673049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880140569/10000000000 : ℝ)^2097 ≤ (136975596553/1250000000000 : ℝ)^1585 := by
    have hnat : (1880140569 : ℕ)^2097*1250000000000^1585 ≤ 136975596553^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880140569 10000000000 136975596553 1250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481948591/1000000000 : ℝ)^2097 ≤ (38071583955809/100000000000000 : ℝ)^1585 := by
    have hnat : (481948591 : ℕ)^2097*100000000000000^1585 ≤ 38071583955809^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481948591 1000000000 38071583955809 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008673049/10000000000 : ℝ)^2097 ≤ (12742592076401/25000000000000 : ℝ)^1585 := by
    have hnat : (6008673049 : ℕ)^2097*25000000000000^1585 ≤ 12742592076401^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008673049 10000000000 12742592076401 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880140569/10000000000 : ℝ), (481948591/1000000000 : ℝ), (6008673049/10000000000 : ℝ)] ![(136975596553/1250000000000 : ℝ), (38071583955809/100000000000000 : ℝ), (12742592076401/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880140569/10000000000 : ℝ)|^2097 ≤ (136975596553/1250000000000 : ℝ)^1585
        have hw : |(-1880140569/10000000000 : ℝ)|=(1880140569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(481948591/1000000000 : ℝ)|^2097 ≤ (38071583955809/100000000000000 : ℝ)^1585
        have hw : |(481948591/1000000000 : ℝ)|=(481948591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008673049/10000000000 : ℝ)|^2097 ≤ (12742592076401/25000000000000 : ℝ)^1585
        have hw : |(6008673049/10000000000 : ℝ)|=(6008673049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517254107/1000000000 : ℝ)*x 0 + (-686186063/5000000000 : ℝ)*x 1 + (6008672753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517254107/1000000000 : ℝ)^2097 ≤ (41804419240697/100000000000000 : ℝ)^1585 := by
    have hnat : (517254107 : ℕ)^2097*100000000000000^1585 ≤ 41804419240697^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517254107 1000000000 41804419240697 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686186063/5000000000 : ℝ)^2097 ≤ (7225215757911/100000000000000 : ℝ)^1585 := by
    have hnat : (686186063 : ℕ)^2097*100000000000000^1585 ≤ 7225215757911^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686186063 5000000000 7225215757911 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6008672753/10000000000 : ℝ)^2097 ≤ (127425912459/250000000000 : ℝ)^1585 := by
    have hnat : (6008672753 : ℕ)^2097*250000000000^1585 ≤ 127425912459^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008672753 10000000000 127425912459 250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517254107/1000000000 : ℝ), (-686186063/5000000000 : ℝ), (6008672753/10000000000 : ℝ)] ![(41804419240697/100000000000000 : ℝ), (7225215757911/100000000000000 : ℝ), (127425912459/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517254107/1000000000 : ℝ)|^2097 ≤ (41804419240697/100000000000000 : ℝ)^1585
        have hw : |(517254107/1000000000 : ℝ)|=(517254107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-686186063/5000000000 : ℝ)|^2097 ≤ (7225215757911/100000000000000 : ℝ)^1585
        have hw : |(-686186063/5000000000 : ℝ)|=(686186063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6008672753/10000000000 : ℝ)|^2097 ≤ (127425912459/250000000000 : ℝ)^1585
        have hw : |(6008672753/10000000000 : ℝ)|=(6008672753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517254101/1000000000 : ℝ)*x 0 + (6008672931/10000000000 : ℝ)*x 1 + (-1372371933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517254101/1000000000 : ℝ)^2097 ≤ (8360883719827/20000000000000 : ℝ)^1585 := by
    have hnat : (517254101 : ℕ)^2097*20000000000000^1585 ≤ 8360883719827^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517254101 1000000000 8360883719827 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6008672931/10000000000 : ℝ)^2097 ≤ (50970366981291/100000000000000 : ℝ)^1585 := by
    have hnat : (6008672931 : ℕ)^2097*100000000000000^1585 ≤ 50970366981291^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008672931 10000000000 50970366981291 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372371933/10000000000 : ℝ)^2097 ≤ (3612607206791/50000000000000 : ℝ)^1585 := by
    have hnat : (1372371933 : ℕ)^2097*50000000000000^1585 ≤ 3612607206791^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372371933 10000000000 3612607206791 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517254101/1000000000 : ℝ), (6008672931/10000000000 : ℝ), (-1372371933/10000000000 : ℝ)] ![(8360883719827/20000000000000 : ℝ), (50970366981291/100000000000000 : ℝ), (3612607206791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517254101/1000000000 : ℝ)|^2097 ≤ (8360883719827/20000000000000 : ℝ)^1585
        have hw : |(517254101/1000000000 : ℝ)|=(517254101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6008672931/10000000000 : ℝ)|^2097 ≤ (50970366981291/100000000000000 : ℝ)^1585
        have hw : |(6008672931/10000000000 : ℝ)|=(6008672931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372371933/10000000000 : ℝ)|^2097 ≤ (3612607206791/50000000000000 : ℝ)^1585
        have hw : |(-1372371933/10000000000 : ℝ)|=(1372371933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s0_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (525846467/1250000000 : ℝ)*x 0 + (5576543119/10000000000 : ℝ)*x 1 + (3186067251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525846467/1250000000 : ℝ)^2097 ≤ (3975427099267/12500000000000 : ℝ)^1585 := by
    have hnat : (525846467 : ℕ)^2097*12500000000000^1585 ≤ 3975427099267^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525846467 1250000000 3975427099267 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5576543119/10000000000 : ℝ)^2097 ≤ (46177857527793/100000000000000 : ℝ)^1585 := by
    have hnat : (5576543119 : ℕ)^2097*100000000000000^1585 ≤ 46177857527793^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576543119 10000000000 46177857527793 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186067251/10000000000 : ℝ)^2097 ≤ (1100936283313/5000000000000 : ℝ)^1585 := by
    have hnat : (3186067251 : ℕ)^2097*5000000000000^1585 ≤ 1100936283313^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186067251 10000000000 1100936283313 5000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525846467/1250000000 : ℝ), (5576543119/10000000000 : ℝ), (3186067251/10000000000 : ℝ)] ![(3975427099267/12500000000000 : ℝ), (46177857527793/100000000000000 : ℝ), (1100936283313/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525846467/1250000000 : ℝ)|^2097 ≤ (3975427099267/12500000000000 : ℝ)^1585
        have hw : |(525846467/1250000000 : ℝ)|=(525846467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5576543119/10000000000 : ℝ)|^2097 ≤ (46177857527793/100000000000000 : ℝ)^1585
        have hw : |(5576543119/10000000000 : ℝ)|=(5576543119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186067251/10000000000 : ℝ)|^2097 ≤ (1100936283313/5000000000000 : ℝ)^1585
        have hw : |(3186067251/10000000000 : ℝ)|=(3186067251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (63/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27613/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8387/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8387 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8387*1^2048 ≤ 0^2048*1^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8387/2048 : ℝ) ≤ (117305985900786053/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8387 ≤ (117305985900786053/5000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8387*5000000000000000000^2048 ≤ 117305985900786053^2048*5^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 117305985900786053 5000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (117305985900786053/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8387 := by
      have hnat : (1 : ℕ)^2048*1^8387 ≤ 1^8387*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5117305985900786053/5000000000000000000 : ℝ) ≤ (10056788224316133/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (5117305985900786053/5000000000000000000 : ℝ)^2048 ≤ (10056788224316133/10000000000000000 : ℝ)^8387 := by
      have hnat : (5117305985900786053 : ℕ)^2048*10000000000000000^8387 ≤ 10056788224316133^8387*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5117305985900786053 5000000000000000000 10056788224316133 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056788224316133/10000000000000000 : ℝ)) (X := (5117305985900786053/5000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2617305985900786053/2500000000000000000 : ℝ) ≤ (5056788224316133/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (2617305985900786053/2500000000000000000 : ℝ)^2048 ≤ (5056788224316133/5000000000000000 : ℝ)^8387 := by
      have hnat : (2617305985900786053 : ℕ)^2048*5000000000000000^8387 ≤ 5056788224316133^8387*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2617305985900786053 2500000000000000000 5056788224316133 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056788224316133/5000000000000000 : ℝ)) (X := (2617305985900786053/2500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56788224316133/4000000000000000 : ℝ)*(0 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56788224316133/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117305985900786053/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56788224316133/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (1 : ℝ)+(56788224316133/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056788224316133/10000000000000000 : ℝ) by norm_num, show 1+(117305985900786053/5000000000000000000 : ℝ)+(0 : ℝ)=(5117305985900786053/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117305985900786053/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56788224316133/4000000000000000 : ℝ)*(2/5 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56788224316133/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056788224316133/5000000000000000 : ℝ) by norm_num, show 1+2*(117305985900786053/5000000000000000000 : ℝ)=(2617305985900786053/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56788224316133/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56788224316133/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56788224316133/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56788224316133/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56788224316133/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56788224316133/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1875149139/10000000000 : ℝ)*X 0 0+(3021080639/5000000000 : ℝ)*X 0 1+(2393569321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513807393/10000000000 : ℝ)*X 1 0+(-2593906543/10000000000 : ℝ)*X 1 1+(4787138601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2756903813/5000000000 : ℝ)*X 2 0+(2393569193/5000000000 : ℝ)*X 2 1+(-2593906507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196738067/10000000000 : ℝ)*X 0 0+(77968737/250000000 : ℝ)*X 0 1+(2820783683/5000000000 : ℝ)*X 0 2+(4196738067/10000000000 : ℝ)*X 1 0+(77968737/250000000 : ℝ)*X 1 1+(2820783683/5000000000 : ℝ)*X 1 2+(4196738067/10000000000 : ℝ)*X 2 0+(77968737/250000000 : ℝ)*X 2 1+(2820783683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1880140569/10000000000 : ℝ)*X 0 0+(481948591/1000000000 : ℝ)*X 0 1+(6008673049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517254107/1000000000 : ℝ)*X 1 0+(-686186063/5000000000 : ℝ)*X 1 1+(6008672753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517254101/1000000000 : ℝ)*X 2 0+(6008672931/10000000000 : ℝ)*X 2 1+(-1372371933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525846467/1250000000 : ℝ)*X 0 0+(5576543119/10000000000 : ℝ)*X 0 1+(3186067251/10000000000 : ℝ)*X 0 2+(525846467/1250000000 : ℝ)*X 1 0+(5576543119/10000000000 : ℝ)*X 1 1+(3186067251/10000000000 : ℝ)*X 1 2+(525846467/1250000000 : ℝ)*X 2 0+(5576543119/10000000000 : ℝ)*X 2 1+(3186067251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (127862951511402798592719/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76479/312500000000 : ℝ)*(base1) + (610493547/100000000000000 : ℝ)*(base19) + (593134761/100000000000000 : ℝ)*(base23) + (12757411/25000000000000 : ℝ)*(base24) + (75029973/50000000000000 : ℝ)*(upper3) + (298296379610773/50000000000000 : ℝ)*(major0) + (298296379610773/50000000000000 : ℝ)*(major1) + (298296379610773/50000000000000 : ℝ)*(major2) + (796800358218237/100000000000000 : ℝ)*(sp0) + (398400488702983/50000000000000 : ℝ)*(sp1) + (796800943735109/100000000000000 : ℝ)*(sp2) + (24773921392387/6250000000000 : ℝ)*(sp3) + (313538639/25000000000000 : ℝ)*(sp4) + (1078550131/100000000000000 : ℝ)*(sp7) + (99095961325401/25000000000000 : ℝ)*(f.failure) + (796801587899513/100000000000000 : ℝ)*(f.sum) + (298932447200809/100000000000000000000000000000 : ℝ)*base65 + (1915498325500809/200000000000000000000000000000 : ℝ)*base67 + (549089134300809/200000000000000000000000000000 : ℝ)*base69 + (1556644860900809/200000000000000000000000000000 : ℝ)*base71 + (292782323400809/100000000000000000000000000000 : ℝ)*base73 + (1717745500700809/200000000000000000000000000000 : ℝ)*base75 + (1629637941700809/200000000000000000000000000000 : ℝ)*base77 + (1069366079900809/200000000000000000000000000000 : ℝ)*base79 + (209103855500809/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (478003/156250000000000000000 : ℝ)*base89 + (478003/156250000000000000000 : ℝ)*base91 + (478003/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26170979078875431886053/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1646313/4000000000000 : ℝ)*(base1) + (539636301/50000000000000 : ℝ)*(base19) + (1073894713/100000000000000 : ℝ)*(base23) + (111649469/100000000000000 : ℝ)*(upper3) + (26365877/20000000000000 : ℝ)*(upper5) + (78702344149997/12500000000000 : ℝ)*(major0) + (78702344149997/12500000000000 : ℝ)*(major1) + (78702344149997/12500000000000 : ℝ)*(major2) + (551565011/25000000000000 : ℝ)*(sp1) + (1136295551/50000000000000 : ℝ)*(sp2) + (840910670670073/100000000000000 : ℝ)*(sp4) + (840907343979603/100000000000000 : ℝ)*(sp5) + (840907283026433/100000000000000 : ℝ)*(sp6) + (209163348075659/50000000000000 : ℝ)*(sp7) + (209163368654571/50000000000000 : ℝ)*(f.failure) + (105113828689031/12500000000000 : ℝ)*(f.sum) + (19602913773399/25000000000000000000000000000 : ℝ)*base66 + (335494114598399/50000000000000000000000000000 : ℝ)*base68 + (193913970748399/50000000000000000000000000000 : ℝ)*base70 + (462053928498399/50000000000000000000000000000 : ℝ)*base72 + (7973175298399/25000000000000000000000000000 : ℝ)*base74 + (554126617048399/50000000000000000000000000000 : ℝ)*base76 + (229371962498399/50000000000000000000000000000 : ℝ)*base78 + (170926867848399/50000000000000000000000000000 : ℝ)*base80 + (6251471126601/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (553487/312500000000000000000 : ℝ)*base90 + (553487/312500000000000000000 : ℝ)*base92 + (553487/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1195_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27613/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_s1_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2075976669/10000000000 : ℝ)*x 0 + (1421892331/2500000000 : ℝ)*x 1 + (5013175273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2075976669/10000000000 : ℝ)^2097 ≤ (2498595402071/20000000000000 : ℝ)^1585 := by
    have hnat : (2075976669 : ℕ)^2097*20000000000000^1585 ≤ 2498595402071^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075976669 10000000000 2498595402071 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1421892331/2500000000 : ℝ)^2097 ≤ (5924764375667/12500000000000 : ℝ)^1585 := by
    have hnat : (1421892331 : ℕ)^2097*12500000000000^1585 ≤ 5924764375667^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421892331 2500000000 5924764375667 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5013175273/10000000000 : ℝ)^2097 ≤ (40108907977467/100000000000000 : ℝ)^1585 := by
    have hnat : (5013175273 : ℕ)^2097*100000000000000^1585 ≤ 40108907977467^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013175273 10000000000 40108907977467 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2075976669/10000000000 : ℝ), (1421892331/2500000000 : ℝ), (5013175273/10000000000 : ℝ)] ![(2498595402071/20000000000000 : ℝ), (5924764375667/12500000000000 : ℝ), (40108907977467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2075976669/10000000000 : ℝ)|^2097 ≤ (2498595402071/20000000000000 : ℝ)^1585
        have hw : |(-2075976669/10000000000 : ℝ)|=(2075976669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1421892331/2500000000 : ℝ)|^2097 ≤ (5924764375667/12500000000000 : ℝ)^1585
        have hw : |(1421892331/2500000000 : ℝ)|=(1421892331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5013175273/10000000000 : ℝ)|^2097 ≤ (40108907977467/100000000000000 : ℝ)^1585
        have hw : |(5013175273/10000000000 : ℝ)|=(5013175273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2708109007/5000000000 : ℝ)*x 0 + (-609736641/2500000000 : ℝ)*x 1 + (5013175613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708109007/5000000000 : ℝ)^2097 ≤ (44429602623481/100000000000000 : ℝ)^1585 := by
    have hnat : (2708109007 : ℕ)^2097*100000000000000^1585 ≤ 44429602623481^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708109007 5000000000 44429602623481 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609736641/2500000000 : ℝ)^2097 ≤ (15461485780083/100000000000000 : ℝ)^1585 := by
    have hnat : (609736641 : ℕ)^2097*100000000000000^1585 ≤ 15461485780083^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609736641 2500000000 15461485780083 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5013175613/10000000000 : ℝ)^2097 ≤ (40108911576419/100000000000000 : ℝ)^1585 := by
    have hnat : (5013175613 : ℕ)^2097*100000000000000^1585 ≤ 40108911576419^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013175613 10000000000 40108911576419 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708109007/5000000000 : ℝ), (-609736641/2500000000 : ℝ), (5013175613/10000000000 : ℝ)] ![(44429602623481/100000000000000 : ℝ), (15461485780083/100000000000000 : ℝ), (40108911576419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708109007/5000000000 : ℝ)|^2097 ≤ (44429602623481/100000000000000 : ℝ)^1585
        have hw : |(2708109007/5000000000 : ℝ)|=(2708109007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-609736641/2500000000 : ℝ)|^2097 ≤ (15461485780083/100000000000000 : ℝ)^1585
        have hw : |(-609736641/2500000000 : ℝ)|=(609736641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5013175613/10000000000 : ℝ)|^2097 ≤ (40108911576419/100000000000000 : ℝ)^1585
        have hw : |(5013175613/10000000000 : ℝ)|=(5013175613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2708108501/5000000000 : ℝ)*x 0 + (501317627/1000000000 : ℝ)*x 1 + (-487789409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708108501/5000000000 : ℝ)^2097 ≤ (8885918328071/20000000000000 : ℝ)^1585 := by
    have hnat : (2708108501 : ℕ)^2097*20000000000000^1585 ≤ 8885918328071^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708108501 5000000000 8885918328071 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501317627/1000000000 : ℝ)^2097 ≤ (2506807408179/6250000000000 : ℝ)^1585 := by
    have hnat : (501317627 : ℕ)^2097*6250000000000^1585 ≤ 2506807408179^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501317627 1000000000 2506807408179 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487789409/2000000000 : ℝ)^2097 ≤ (15461489814337/100000000000000 : ℝ)^1585 := by
    have hnat : (487789409 : ℕ)^2097*100000000000000^1585 ≤ 15461489814337^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487789409 2000000000 15461489814337 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708108501/5000000000 : ℝ), (501317627/1000000000 : ℝ), (-487789409/2000000000 : ℝ)] ![(8885918328071/20000000000000 : ℝ), (2506807408179/6250000000000 : ℝ), (15461489814337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708108501/5000000000 : ℝ)|^2097 ≤ (8885918328071/20000000000000 : ℝ)^1585
        have hw : |(2708108501/5000000000 : ℝ)|=(2708108501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501317627/1000000000 : ℝ)|^2097 ≤ (2506807408179/6250000000000 : ℝ)^1585
        have hw : |(501317627/1000000000 : ℝ)|=(501317627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487789409/2000000000 : ℝ)|^2097 ≤ (15461489814337/100000000000000 : ℝ)^1585
        have hw : |(-487789409/2000000000 : ℝ)|=(487789409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (431291693/1000000000 : ℝ)*x 0 + (3686901281/10000000000 : ℝ)*x 1 + (504255299/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431291693/1000000000 : ℝ)^2097 ≤ (8217350203673/25000000000000 : ℝ)^1585 := by
    have hnat : (431291693 : ℕ)^2097*25000000000000^1585 ≤ 8217350203673^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431291693 1000000000 8217350203673 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3686901281/10000000000 : ℝ)^2097 ≤ (2671042964149/10000000000000 : ℝ)^1585 := by
    have hnat : (3686901281 : ℕ)^2097*10000000000000^1585 ≤ 2671042964149^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686901281 10000000000 2671042964149 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504255299/1000000000 : ℝ)^2097 ≤ (5052521190849/12500000000000 : ℝ)^1585 := by
    have hnat : (504255299 : ℕ)^2097*12500000000000^1585 ≤ 5052521190849^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504255299 1000000000 5052521190849 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431291693/1000000000 : ℝ), (3686901281/10000000000 : ℝ), (504255299/1000000000 : ℝ)] ![(8217350203673/25000000000000 : ℝ), (2671042964149/10000000000000 : ℝ), (5052521190849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431291693/1000000000 : ℝ)|^2097 ≤ (8217350203673/25000000000000 : ℝ)^1585
        have hw : |(431291693/1000000000 : ℝ)|=(431291693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3686901281/10000000000 : ℝ)|^2097 ≤ (2671042964149/10000000000000 : ℝ)^1585
        have hw : |(3686901281/10000000000 : ℝ)|=(3686901281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504255299/1000000000 : ℝ)|^2097 ≤ (5052521190849/12500000000000 : ℝ)^1585
        have hw : |(504255299/1000000000 : ℝ)|=(504255299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-519177733/2500000000 : ℝ)*x 0 + (980898/1953125 : ℝ)*x 1 + (1135674423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519177733/2500000000 : ℝ)^2097 ≤ (3124705854481/25000000000000 : ℝ)^1585 := by
    have hnat : (519177733 : ℕ)^2097*25000000000000^1585 ≤ 3124705854481^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519177733 2500000000 3124705854481 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980898/1953125 : ℝ)^2097 ≤ (2512777507963/6250000000000 : ℝ)^1585 := by
    have hnat : (980898 : ℕ)^2097*6250000000000^1585 ≤ 2512777507963^1585*1953125^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980898 1953125 2512777507963 6250000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135674423/2000000000 : ℝ)^2097 ≤ (47296736449233/100000000000000 : ℝ)^1585 := by
    have hnat : (1135674423 : ℕ)^2097*100000000000000^1585 ≤ 47296736449233^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135674423 2000000000 47296736449233 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519177733/2500000000 : ℝ), (980898/1953125 : ℝ), (1135674423/2000000000 : ℝ)] ![(3124705854481/25000000000000 : ℝ), (2512777507963/6250000000000 : ℝ), (47296736449233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519177733/2500000000 : ℝ)|^2097 ≤ (3124705854481/25000000000000 : ℝ)^1585
        have hw : |(-519177733/2500000000 : ℝ)|=(519177733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(980898/1953125 : ℝ)|^2097 ≤ (2512777507963/6250000000000 : ℝ)^1585
        have hw : |(980898/1953125 : ℝ)|=(980898/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135674423/2000000000 : ℝ)|^2097 ≤ (47296736449233/100000000000000 : ℝ)^1585
        have hw : |(1135674423/2000000000 : ℝ)|=(1135674423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5242863207/10000000000 : ℝ)*x 0 + (-443437597/2500000000 : ℝ)*x 1 + (354898247/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242863207/10000000000 : ℝ)^2097 ≤ (42557998886269/100000000000000 : ℝ)^1585 := by
    have hnat : (5242863207 : ℕ)^2097*100000000000000^1585 ≤ 42557998886269^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242863207 10000000000 42557998886269 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443437597/2500000000 : ℝ)^2097 ≤ (5072633221063/50000000000000 : ℝ)^1585 := by
    have hnat : (443437597 : ℕ)^2097*50000000000000^1585 ≤ 5072633221063^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443437597 2500000000 5072633221063 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354898247/625000000 : ℝ)^2097 ≤ (23648367326497/50000000000000 : ℝ)^1585 := by
    have hnat : (354898247 : ℕ)^2097*50000000000000^1585 ≤ 23648367326497^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354898247 625000000 23648367326497 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242863207/10000000000 : ℝ), (-443437597/2500000000 : ℝ), (354898247/625000000 : ℝ)] ![(42557998886269/100000000000000 : ℝ), (5072633221063/50000000000000 : ℝ), (23648367326497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242863207/10000000000 : ℝ)|^2097 ≤ (42557998886269/100000000000000 : ℝ)^1585
        have hw : |(5242863207/10000000000 : ℝ)|=(5242863207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443437597/2500000000 : ℝ)|^2097 ≤ (5072633221063/50000000000000 : ℝ)^1585
        have hw : |(-443437597/2500000000 : ℝ)|=(443437597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(354898247/625000000 : ℝ)|^2097 ≤ (23648367326497/50000000000000 : ℝ)^1585
        have hw : |(354898247/625000000 : ℝ)|=(354898247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2621431587/5000000000 : ℝ)*x 0 + (283918629/500000000 : ℝ)*x 1 + (-1773749521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621431587/5000000000 : ℝ)^2097 ≤ (42557998531867/100000000000000 : ℝ)^1585 := by
    have hnat : (2621431587 : ℕ)^2097*100000000000000^1585 ≤ 42557998531867^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621431587 5000000000 42557998531867 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283918629/500000000 : ℝ)^2097 ≤ (47296741573473/100000000000000 : ℝ)^1585 := by
    have hnat : (283918629 : ℕ)^2097*100000000000000^1585 ≤ 47296741573473^1585*500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283918629 500000000 47296741573473 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1773749521/10000000000 : ℝ)^2097 ≤ (1014525988129/10000000000000 : ℝ)^1585 := by
    have hnat : (1773749521 : ℕ)^2097*10000000000000^1585 ≤ 1014525988129^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773749521 10000000000 1014525988129 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621431587/5000000000 : ℝ), (283918629/500000000 : ℝ), (-1773749521/10000000000 : ℝ)] ![(42557998531867/100000000000000 : ℝ), (47296741573473/100000000000000 : ℝ), (1014525988129/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621431587/5000000000 : ℝ)|^2097 ≤ (42557998531867/100000000000000 : ℝ)^1585
        have hw : |(2621431587/5000000000 : ℝ)|=(2621431587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283918629/500000000 : ℝ)|^2097 ≤ (47296741573473/100000000000000 : ℝ)^1585
        have hw : |(283918629/500000000 : ℝ)|=(283918629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1773749521/10000000000 : ℝ)|^2097 ≤ (1014525988129/10000000000000 : ℝ)^1585
        have hw : |(-1773749521/10000000000 : ℝ)|=(1773749521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s1_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4314392789/10000000000 : ℝ)*x 0 + (502441607/1000000000 : ℝ)*x 1 + (3705389453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314392789/10000000000 : ℝ)^2097 ≤ (32884282726499/100000000000000 : ℝ)^1585 := by
    have hnat : (4314392789 : ℕ)^2097*100000000000000^1585 ≤ 32884282726499^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314392789 10000000000 32884282726499 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502441607/1000000000 : ℝ)^2097 ≤ (40227936595653/100000000000000 : ℝ)^1585 := by
    have hnat : (502441607 : ℕ)^2097*100000000000000^1585 ≤ 40227936595653^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502441607 1000000000 40227936595653 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3705389453/10000000000 : ℝ)^2097 ≤ (13443890334027/50000000000000 : ℝ)^1585 := by
    have hnat : (3705389453 : ℕ)^2097*50000000000000^1585 ≤ 13443890334027^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705389453 10000000000 13443890334027 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314392789/10000000000 : ℝ), (502441607/1000000000 : ℝ), (3705389453/10000000000 : ℝ)] ![(32884282726499/100000000000000 : ℝ), (40227936595653/100000000000000 : ℝ), (13443890334027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314392789/10000000000 : ℝ)|^2097 ≤ (32884282726499/100000000000000 : ℝ)^1585
        have hw : |(4314392789/10000000000 : ℝ)|=(4314392789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502441607/1000000000 : ℝ)|^2097 ≤ (40227936595653/100000000000000 : ℝ)^1585
        have hw : |(502441607/1000000000 : ℝ)|=(502441607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3705389453/10000000000 : ℝ)|^2097 ≤ (13443890334027/50000000000000 : ℝ)^1585
        have hw : |(3705389453/10000000000 : ℝ)|=(3705389453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27613/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5941/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20201/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27613/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (63/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27613/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (63/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27613/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (63/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27613/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (63/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27613/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (63/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27613/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (63/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (63/10000 : ℝ) ^ (8387/2048 : ℝ) ≤ (97235925473/100000000000000000000 : ℝ) := by
    have hpowers : (63/10000 : ℝ)^8387 ≤ (97235925473/100000000000000000000 : ℝ)^2048 := by
      have hnat : (63 : ℕ)^8387*100000000000000000000^2048 ≤ 97235925473^2048*10000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63 10000 97235925473 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63/10000 : ℝ)) (X := (97235925473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27613/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (514327907309380417/100000000000000000000 : ℝ) := by
    have hpowers : (27613/100000 : ℝ)^8387 ≤ (514327907309380417/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27613 : ℕ)^8387*100000000000000000000^2048 ≤ 514327907309380417^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27613 100000 514327907309380417 100000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27613/100000 : ℝ)) (X := (514327907309380417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000097235925473/50000000000000000000 : ℝ) ≤ (10000000004748759/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50000000097235925473/50000000000000000000 : ℝ)^2048 ≤ (10000000004748759/10000000000000000 : ℝ)^8387 := by
      have hnat : (50000000097235925473 : ℕ)^2048*10000000000000000^8387 ≤ 10000000004748759^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000097235925473 50000000000000000000 10000000004748759 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000004748759/10000000000000000 : ℝ)) (X := (50000000097235925473/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10051432800454530589/10000000000000000000 : ℝ) ≤ (5006267452805687/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (10051432800454530589/10000000000000000000 : ℝ)^2048 ≤ (5006267452805687/5000000000000000 : ℝ)^8387 := by
      have hnat : (10051432800454530589 : ℕ)^2048*5000000000000000^8387 ≤ 5006267452805687^8387*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10051432800454530589 10000000000000000000 5006267452805687 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006267452805687/5000000000000000 : ℝ)) (X := (10051432800454530589/10000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50514327907309380417/50000000000000000000 : ℝ) ≤ (10025069806473989/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50514327907309380417/50000000000000000000 : ℝ)^2048 ≤ (10025069806473989/10000000000000000 : ℝ)^8387 := by
      have hnat : (50514327907309380417 : ℕ)^2048*10000000000000000^8387 ≤ 10025069806473989^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50514327907309380417 50000000000000000000 10025069806473989 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025069806473989/10000000000000000 : ℝ)) (X := (50514327907309380417/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(97235925473/100000000000000000000 : ℝ) ≤ ((269814206153048869197/269830000000000000000 : ℝ)+2*(2506980172523/539660000000000 : ℝ)*(63/10000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (269814206153048869197/269830000000000000000 : ℝ)+2*(2506980172523/539660000000000 : ℝ)*(63/10000 : ℝ)=(10000000004748759/10000000000000000 : ℝ) by norm_num, show 1+2*(97235925473/100000000000000000000 : ℝ)=(50000000097235925473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(514327907309380417/100000000000000000000 : ℝ)+(97235925473/100000000000000000000 : ℝ) ≤ ((269814206153048869197/269830000000000000000 : ℝ)+(2506980172523/539660000000000 : ℝ)*((27613/100000 : ℝ)+(63/10000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (269814206153048869197/269830000000000000000 : ℝ)+(2506980172523/539660000000000 : ℝ)*((27613/100000 : ℝ)+(63/10000 : ℝ))=(5006267452805687/5000000000000000 : ℝ) by norm_num, show 1+(514327907309380417/100000000000000000000 : ℝ)+(97235925473/100000000000000000000 : ℝ)=(10051432800454530589/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(514327907309380417/100000000000000000000 : ℝ) ≤ ((269814206153048869197/269830000000000000000 : ℝ)+2*(2506980172523/539660000000000 : ℝ)*(27613/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (269814206153048869197/269830000000000000000 : ℝ)+2*(2506980172523/539660000000000 : ℝ)*(27613/100000 : ℝ)=(10025069806473989/10000000000000000 : ℝ) by norm_num, show 1+2*(514327907309380417/100000000000000000000 : ℝ)=(50514327907309380417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (269814206153048869197/269830000000000000000 : ℝ)*(X 1 0+X 2 0)+(2506980172523/539660000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (63/10000 : ℝ)) (hi := (27613/100000 : ℝ)) (c := (269814206153048869197/269830000000000000000 : ℝ)) (alpha := (2506980172523/539660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (269814206153048869197/269830000000000000000 : ℝ)*(X 0 1+X 2 1)+(2506980172523/539660000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (63/10000 : ℝ)) (hi := (27613/100000 : ℝ)) (c := (269814206153048869197/269830000000000000000 : ℝ)) (alpha := (2506980172523/539660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (269814206153048869197/269830000000000000000 : ℝ)*(X 0 2+X 1 2)+(2506980172523/539660000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (63/10000 : ℝ)) (hi := (27613/100000 : ℝ)) (c := (269814206153048869197/269830000000000000000 : ℝ)) (alpha := (2506980172523/539660000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2075976669/10000000000 : ℝ)*X 0 0+(1421892331/2500000000 : ℝ)*X 0 1+(5013175273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2708109007/5000000000 : ℝ)*X 1 0+(-609736641/2500000000 : ℝ)*X 1 1+(5013175613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2708108501/5000000000 : ℝ)*X 2 0+(501317627/1000000000 : ℝ)*X 2 1+(-487789409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((431291693/1000000000 : ℝ)*X 0 0+(3686901281/10000000000 : ℝ)*X 0 1+(504255299/1000000000 : ℝ)*X 0 2+(431291693/1000000000 : ℝ)*X 1 0+(3686901281/10000000000 : ℝ)*X 1 1+(504255299/1000000000 : ℝ)*X 1 2+(431291693/1000000000 : ℝ)*X 2 0+(3686901281/10000000000 : ℝ)*X 2 1+(504255299/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-519177733/2500000000 : ℝ)*X 0 0+(980898/1953125 : ℝ)*X 0 1+(1135674423/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242863207/10000000000 : ℝ)*X 1 0+(-443437597/2500000000 : ℝ)*X 1 1+(354898247/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621431587/5000000000 : ℝ)*X 2 0+(283918629/500000000 : ℝ)*X 2 1+(-1773749521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314392789/10000000000 : ℝ)*X 0 0+(502441607/1000000000 : ℝ)*X 0 1+(3705389453/10000000000 : ℝ)*X 0 2+(4314392789/10000000000 : ℝ)*X 1 0+(502441607/1000000000 : ℝ)*X 1 1+(3705389453/10000000000 : ℝ)*X 1 2+(4314392789/10000000000 : ℝ)*X 2 0+(502441607/1000000000 : ℝ)*X 2 1+(3705389453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5287969235012092195301242371/843218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (787811343/50000000000000 : ℝ)*(base19) + (1279304337/100000000000000 : ℝ)*(base23) + (305957051/100000000000000 : ℝ)*(upper3) + (10430059/100000000000000 : ℝ)*(upper4) + (42012759/100000000000000 : ℝ)*(upper5) + (138780873853669/12500000000000 : ℝ)*(major0) + (138780873853669/12500000000000 : ℝ)*(major1) + (138780873853669/12500000000000 : ℝ)*(major2) + (59312941122429/4000000000000 : ℝ)*(sp0) + (46338435091551/3125000000000 : ℝ)*(sp1) + (74141510962399/5000000000000 : ℝ)*(sp2) + (73765691790879/10000000000000 : ℝ)*(sp3) + (7970491593/100000000000000 : ℝ)*(sp4) + (5356158547/100000000000000 : ℝ)*(sp7) + (737662274067337/100000000000000 : ℝ)*(f.failure) + (741415749276159/50000000000000 : ℝ)*(f.sum) + (9595603509499/2698300000000000000000000000 : ℝ)*base65 + (6801970711495533793/3372875000000000000000000000000000 : ℝ)*base67 + (2137588765433591207/3372875000000000000000000000000000 : ℝ)*base70 + (13433106132071408793/3372875000000000000000000000000000 : ℝ)*base71 + (610735421689/168643750000000000000000000 : ℝ)*base73 + (4905371235445408793/3372875000000000000000000000000000 : ℝ)*base75 + (5212178279934408793/3372875000000000000000000000000000 : ℝ)*base77 + (29066982975413033793/3372875000000000000000000000000000 : ℝ)*base79 + (7552840790543/26983000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2106389/625000000000000000000 : ℝ)*base90 + (2106389/625000000000000000000 : ℝ)*base92 + (2106389/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34846502889484283093866673613/6745750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (145934743/10000000000000 : ℝ)*(base19) + (790812391/50000000000000 : ℝ)*(base23) + (6070587/20000000000000 : ℝ)*(upper2) + (7601843/5000000000000 : ℝ)*(upper3) + (114819/78125000000 : ℝ)*(upper5) + (1141060090819243/100000000000000 : ℝ)*(major0) + (1141060090819243/100000000000000 : ℝ)*(major1) + (1141060090819243/100000000000000 : ℝ)*(major2) + (6822013807/100000000000000 : ℝ)*(sp1) + (1132419777/12500000000000 : ℝ)*(sp2) + (1523985118389381/100000000000000 : ℝ)*(sp4) + (95248552314259/6250000000000 : ℝ)*(sp5) + (1523974477406383/100000000000000 : ℝ)*(sp6) + (758134891059191/100000000000000 : ℝ)*(sp7) + (758134891059191/100000000000000 : ℝ)*(f.failure) + (1523985118389381/100000000000000 : ℝ)*(f.sum) + (99584737489/210804687500000000000000000 : ℝ)*base66 + (70087137256667942129/26983000000000000000000000000000000 : ℝ)*base68 + (107392144136731942129/26983000000000000000000000000000000 : ℝ)*base70 + (7092206101207057871/26983000000000000000000000000000000 : ℝ)*base71 + (20056123806039/26983000000000000000000000000 : ℝ)*base73 + (159830770450343942129/26983000000000000000000000000000000 : ℝ)*base76 + (61434116648336942129/26983000000000000000000000000000000 : ℝ)*base78 + (85168634816367942129/26983000000000000000000000000000000 : ℝ)*base80 + (17730273339491/26983000000000000000000000000 : ℝ)*base82 + (2326373/625000000000000000000 : ℝ)*base89 + (2326373/625000000000000000000 : ℝ)*base91 + (2326373/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27613/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (63/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5941/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20201/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1195_s2_0 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063206117/5000000000 : ℝ)*x 0 + (1375252349/2500000000 : ℝ)*x 1 + (5167614007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063206117/5000000000 : ℝ)^2097 ≤ (1289610331313/10000000000000 : ℝ)^1585 := by
    have hnat : (1063206117 : ℕ)^2097*10000000000000^1585 ≤ 1289610331313^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063206117 5000000000 1289610331313 10000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375252349/2500000000 : ℝ)^2097 ≤ (2267607646877/5000000000000 : ℝ)^1585 := by
    have hnat : (1375252349 : ℕ)^2097*5000000000000^1585 ≤ 2267607646877^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375252349 2500000000 2267607646877 5000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5167614007/10000000000 : ℝ)^2097 ≤ (10437935934441/25000000000000 : ℝ)^1585 := by
    have hnat : (5167614007 : ℕ)^2097*25000000000000^1585 ≤ 10437935934441^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167614007 10000000000 10437935934441 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063206117/5000000000 : ℝ), (1375252349/2500000000 : ℝ), (5167614007/10000000000 : ℝ)] ![(1289610331313/10000000000000 : ℝ), (2267607646877/5000000000000 : ℝ), (10437935934441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063206117/5000000000 : ℝ)|^2097 ≤ (1289610331313/10000000000000 : ℝ)^1585
        have hw : |(-1063206117/5000000000 : ℝ)|=(1063206117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375252349/2500000000 : ℝ)|^2097 ≤ (2267607646877/5000000000000 : ℝ)^1585
        have hw : |(1375252349/2500000000 : ℝ)|=(1375252349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5167614007/10000000000 : ℝ)|^2097 ≤ (10437935934441/25000000000000 : ℝ)^1585
        have hw : |(5167614007/10000000000 : ℝ)|=(5167614007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_1 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685809161/5000000000 : ℝ)*x 0 + (-18395163/80000000 : ℝ)*x 1 + (322976141/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685809161/5000000000 : ℝ)^2097 ≤ (5493276496447/12500000000000 : ℝ)^1585 := by
    have hnat : (2685809161 : ℕ)^2097*12500000000000^1585 ≤ 5493276496447^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685809161 5000000000 5493276496447 12500000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18395163/80000000 : ℝ)^2097 ≤ (3575499714519/25000000000000 : ℝ)^1585 := by
    have hnat : (18395163 : ℕ)^2097*25000000000000^1585 ≤ 3575499714519^1585*80000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18395163 80000000 3575499714519 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322976141/625000000 : ℝ)^2097 ≤ (41751789157071/100000000000000 : ℝ)^1585 := by
    have hnat : (322976141 : ℕ)^2097*100000000000000^1585 ≤ 41751789157071^1585*625000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322976141 625000000 41751789157071 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685809161/5000000000 : ℝ), (-18395163/80000000 : ℝ), (322976141/625000000 : ℝ)] ![(5493276496447/12500000000000 : ℝ), (3575499714519/25000000000000 : ℝ), (41751789157071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685809161/5000000000 : ℝ)|^2097 ≤ (5493276496447/12500000000000 : ℝ)^1585
        have hw : |(2685809161/5000000000 : ℝ)|=(2685809161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18395163/80000000 : ℝ)|^2097 ≤ (3575499714519/25000000000000 : ℝ)^1585
        have hw : |(-18395163/80000000 : ℝ)|=(18395163/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322976141/625000000 : ℝ)|^2097 ≤ (41751789157071/100000000000000 : ℝ)^1585
        have hw : |(322976141/625000000 : ℝ)|=(322976141/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_2 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074324019/2000000000 : ℝ)*x 0 + (5167615777/10000000000 : ℝ)*x 1 + (-287424533/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074324019/2000000000 : ℝ)^2097 ≤ (21973115581213/50000000000000 : ℝ)^1585 := by
    have hnat : (1074324019 : ℕ)^2097*50000000000000^1585 ≤ 21973115581213^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074324019 2000000000 21973115581213 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167615777/10000000000 : ℝ)^2097 ≤ (2087588132901/5000000000000 : ℝ)^1585 := by
    have hnat : (5167615777 : ℕ)^2097*5000000000000^1585 ≤ 2087588132901^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167615777 10000000000 2087588132901 5000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287424533/1250000000 : ℝ)^2097 ≤ (2860401234749/20000000000000 : ℝ)^1585 := by
    have hnat : (287424533 : ℕ)^2097*20000000000000^1585 ≤ 2860401234749^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287424533 1250000000 2860401234749 20000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074324019/2000000000 : ℝ), (5167615777/10000000000 : ℝ), (-287424533/1250000000 : ℝ)] ![(21973115581213/50000000000000 : ℝ), (2087588132901/5000000000000 : ℝ), (2860401234749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074324019/2000000000 : ℝ)|^2097 ≤ (21973115581213/50000000000000 : ℝ)^1585
        have hw : |(1074324019/2000000000 : ℝ)|=(1074324019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167615777/10000000000 : ℝ)|^2097 ≤ (2087588132901/5000000000000 : ℝ)^1585
        have hw : |(5167615777/10000000000 : ℝ)|=(5167615777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287424533/1250000000 : ℝ)|^2097 ≤ (2860401234749/20000000000000 : ℝ)^1585
        have hw : |(-287424533/1250000000 : ℝ)|=(287424533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_3 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1086911209/2500000000 : ℝ)*x 0 + (1006299373/2500000000 : ℝ)*x 1 + (1173844283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086911209/2500000000 : ℝ)^2097 ≤ (33220016932599/100000000000000 : ℝ)^1585 := by
    have hnat : (1086911209 : ℕ)^2097*100000000000000^1585 ≤ 33220016932599^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086911209 2500000000 33220016932599 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006299373/2500000000 : ℝ)^2097 ≤ (7500016952029/25000000000000 : ℝ)^1585 := by
    have hnat : (1006299373 : ℕ)^2097*25000000000000^1585 ≤ 7500016952029^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006299373 2500000000 7500016952029 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1173844283/2500000000 : ℝ)^2097 ≤ (36779915235139/100000000000000 : ℝ)^1585 := by
    have hnat : (1173844283 : ℕ)^2097*100000000000000^1585 ≤ 36779915235139^1585*2500000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173844283 2500000000 36779915235139 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086911209/2500000000 : ℝ), (1006299373/2500000000 : ℝ), (1173844283/2500000000 : ℝ)] ![(33220016932599/100000000000000 : ℝ), (7500016952029/25000000000000 : ℝ), (36779915235139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086911209/2500000000 : ℝ)|^2097 ≤ (33220016932599/100000000000000 : ℝ)^1585
        have hw : |(1086911209/2500000000 : ℝ)|=(1086911209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006299373/2500000000 : ℝ)|^2097 ≤ (7500016952029/25000000000000 : ℝ)^1585
        have hw : |(1006299373/2500000000 : ℝ)|=(1006299373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1173844283/2500000000 : ℝ)|^2097 ≤ (36779915235139/100000000000000 : ℝ)^1585
        have hw : |(1173844283/2500000000 : ℝ)|=(1173844283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_4 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126500071/10000000000 : ℝ)*x 0 + (5169830259/10000000000 : ℝ)*x 1 + (5498772541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126500071/10000000000 : ℝ)^2097 ≤ (12896808104531/100000000000000 : ℝ)^1585 := by
    have hnat : (2126500071 : ℕ)^2097*100000000000000^1585 ≤ 12896808104531^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126500071 10000000000 12896808104531 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169830259/10000000000 : ℝ)^2097 ≤ (41775435803841/100000000000000 : ℝ)^1585 := by
    have hnat : (5169830259 : ℕ)^2097*100000000000000^1585 ≤ 41775435803841^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169830259 10000000000 41775435803841 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498772541/10000000000 : ℝ)^2097 ≤ (45327756074277/100000000000000 : ℝ)^1585 := by
    have hnat : (5498772541 : ℕ)^2097*100000000000000^1585 ≤ 45327756074277^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498772541 10000000000 45327756074277 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126500071/10000000000 : ℝ), (5169830259/10000000000 : ℝ), (5498772541/10000000000 : ℝ)] ![(12896808104531/100000000000000 : ℝ), (41775435803841/100000000000000 : ℝ), (45327756074277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126500071/10000000000 : ℝ)|^2097 ≤ (12896808104531/100000000000000 : ℝ)^1585
        have hw : |(-2126500071/10000000000 : ℝ)|=(2126500071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169830259/10000000000 : ℝ)|^2097 ≤ (41775435803841/100000000000000 : ℝ)^1585
        have hw : |(5169830259/10000000000 : ℝ)|=(5169830259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498772541/10000000000 : ℝ)|^2097 ≤ (45327756074277/100000000000000 : ℝ)^1585
        have hw : |(5498772541/10000000000 : ℝ)|=(5498772541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_5 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (660841669/1250000000 : ℝ)*x 0 + (-984119727/5000000000 : ℝ)*x 1 + (2749386279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660841669/1250000000 : ℝ)^2097 ≤ (43029775435417/100000000000000 : ℝ)^1585 := by
    have hnat : (660841669 : ℕ)^2097*100000000000000^1585 ≤ 43029775435417^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660841669 1250000000 43029775435417 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984119727/5000000000 : ℝ)^2097 ≤ (5821234142883/50000000000000 : ℝ)^1585 := by
    have hnat : (984119727 : ℕ)^2097*50000000000000^1585 ≤ 5821234142883^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984119727 5000000000 5821234142883 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2749386279/5000000000 : ℝ)^2097 ≤ (283298476623/625000000000 : ℝ)^1585 := by
    have hnat : (2749386279 : ℕ)^2097*625000000000^1585 ≤ 283298476623^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749386279 5000000000 283298476623 625000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660841669/1250000000 : ℝ), (-984119727/5000000000 : ℝ), (2749386279/5000000000 : ℝ)] ![(43029775435417/100000000000000 : ℝ), (5821234142883/50000000000000 : ℝ), (283298476623/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660841669/1250000000 : ℝ)|^2097 ≤ (43029775435417/100000000000000 : ℝ)^1585
        have hw : |(660841669/1250000000 : ℝ)|=(660841669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984119727/5000000000 : ℝ)|^2097 ≤ (5821234142883/50000000000000 : ℝ)^1585
        have hw : |(-984119727/5000000000 : ℝ)|=(984119727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2749386279/5000000000 : ℝ)|^2097 ≤ (283298476623/625000000000 : ℝ)^1585
        have hw : |(2749386279/5000000000 : ℝ)|=(2749386279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_6 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (66084169/125000000 : ℝ)*x 0 + (5498772571/10000000000 : ℝ)*x 1 + (-393647841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66084169/125000000 : ℝ)^2097 ≤ (43029777244507/100000000000000 : ℝ)^1585 := by
    have hnat : (66084169 : ℕ)^2097*100000000000000^1585 ≤ 43029777244507^1585*125000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66084169 125000000 43029777244507 100000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5498772571/10000000000 : ℝ)^2097 ≤ (22663878200729/50000000000000 : ℝ)^1585 := by
    have hnat : (5498772571 : ℕ)^2097*50000000000000^1585 ≤ 22663878200729^1585*10000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498772571 10000000000 22663878200729 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393647841/2000000000 : ℝ)^2097 ≤ (2910616584277/25000000000000 : ℝ)^1585 := by
    have hnat : (393647841 : ℕ)^2097*25000000000000^1585 ≤ 2910616584277^1585*2000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393647841 2000000000 2910616584277 25000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66084169/125000000 : ℝ), (5498772571/10000000000 : ℝ), (-393647841/2000000000 : ℝ)] ![(43029777244507/100000000000000 : ℝ), (22663878200729/50000000000000 : ℝ), (2910616584277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66084169/125000000 : ℝ)|^2097 ≤ (43029777244507/100000000000000 : ℝ)^1585
        have hw : |(66084169/125000000 : ℝ)|=(66084169/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5498772571/10000000000 : ℝ)|^2097 ≤ (22663878200729/50000000000000 : ℝ)^1585
        have hw : |(5498772571/10000000000 : ℝ)|=(5498772571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393647841/2000000000 : ℝ)|^2097 ≤ (2910616584277/25000000000000 : ℝ)^1585
        have hw : |(-393647841/2000000000 : ℝ)|=(393647841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1195_s2_7 (p : ℝ) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ)) (x : Fin 3 → ℝ) :
    (543477959/1250000000 : ℝ)*x 0 + (469092479/1000000000 : ℝ)*x 1 + (2014846029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543477959/1250000000 : ℝ)^2097 ≤ (16610912412933/50000000000000 : ℝ)^1585 := by
    have hnat : (543477959 : ℕ)^2097*50000000000000^1585 ≤ 16610912412933^1585*1250000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543477959 1250000000 16610912412933 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469092479/1000000000 : ℝ)^2097 ≤ (18366890071583/50000000000000 : ℝ)^1585 := by
    have hnat : (469092479 : ℕ)^2097*50000000000000^1585 ≤ 18366890071583^1585*1000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469092479 1000000000 18366890071583 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014846029/5000000000 : ℝ)^2097 ≤ (15022197502379/50000000000000 : ℝ)^1585 := by
    have hnat : (2014846029 : ℕ)^2097*50000000000000^1585 ≤ 15022197502379^1585*5000000000^2097 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014846029 5000000000 15022197502379 50000000000000 2097 1585 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2097/512 : ℝ)) 2097 1585 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543477959/1250000000 : ℝ), (469092479/1000000000 : ℝ), (2014846029/5000000000 : ℝ)] ![(16610912412933/50000000000000 : ℝ), (18366890071583/50000000000000 : ℝ), (15022197502379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543477959/1250000000 : ℝ)|^2097 ≤ (16610912412933/50000000000000 : ℝ)^1585
        have hw : |(543477959/1250000000 : ℝ)|=(543477959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469092479/1000000000 : ℝ)|^2097 ≤ (18366890071583/50000000000000 : ℝ)^1585
        have hw : |(469092479/1000000000 : ℝ)|=(469092479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014846029/5000000000 : ℝ)|^2097 ≤ (15022197502379/50000000000000 : ℝ)^1585
        have hw : |(2014846029/5000000000 : ℝ)|=(2014846029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1195_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20201/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9303/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (327/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20201/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20201/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5941/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20201/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20201/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5941/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20201/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20201/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5941/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5941/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (238029863216959/25000000000000000000 : ℝ) := by
    have hpowers : (5941/100000 : ℝ)^8387 ≤ (238029863216959/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5941 : ℕ)^8387*25000000000000000000^2048 ≤ 238029863216959^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5941 100000 238029863216959 25000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5941/100000 : ℝ)) (X := (238029863216959/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20201/100000 : ℝ) ^ (8387/2048 : ℝ) ≤ (71502736830451751/50000000000000000000 : ℝ) := by
    have hpowers : (20201/100000 : ℝ)^8387 ≤ (71502736830451751/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20201 : ℕ)^8387*50000000000000000000^2048 ≤ 71502736830451751^2048*100000^8387 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20201 100000 71502736830451751 50000000000000000000 8387 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20201/100000 : ℝ)) (X := (71502736830451751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500238029863216959/12500000000000000000 : ℝ) ≤ (5000023249393197/5000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (12500238029863216959/12500000000000000000 : ℝ)^2048 ≤ (5000023249393197/5000000000000000 : ℝ)^8387 := by
      have hnat : (12500238029863216959 : ℕ)^2048*5000000000000000^8387 ≤ 5000023249393197^8387*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500238029863216959 12500000000000000000 5000023249393197 5000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000023249393197/5000000000000000 : ℝ)) (X := (12500238029863216959/12500000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50071978796556885669/50000000000000000000 : ℝ) ≤ (10003513352730531/10000000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (50071978796556885669/50000000000000000000 : ℝ)^2048 ≤ (10003513352730531/10000000000000000 : ℝ)^8387 := by
      have hnat : (50071978796556885669 : ℕ)^2048*10000000000000000^8387 ≤ 10003513352730531^8387*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071978796556885669 50000000000000000000 10003513352730531 10000000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003513352730531/10000000000000000 : ℝ)) (X := (50071978796556885669/50000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25071502736830451751/25000000000000000000 : ℝ) ≤ (2501745051668667/2500000000000000 : ℝ) ^ (8387/2048 : ℝ) := by
    have hpowers : (25071502736830451751/25000000000000000000 : ℝ)^2048 ≤ (2501745051668667/2500000000000000 : ℝ)^8387 := by
      have hnat : (25071502736830451751 : ℕ)^2048*2500000000000000^8387 ≤ 2501745051668667^8387*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25071502736830451751 25000000000000000000 2501745051668667 2500000000000000 2048 8387 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501745051668667/2500000000000000 : ℝ)) (X := (25071502736830451751/25000000000000000000 : ℝ)) (by norm_num) 8387 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(238029863216959/25000000000000000000 : ℝ) ≤ ((71279734957064871303/71300000000000000000 : ℝ)+2*(3466853944137/1426000000000000 : ℝ)*(5941/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (71279734957064871303/71300000000000000000 : ℝ)+2*(3466853944137/1426000000000000 : ℝ)*(5941/100000 : ℝ)=(5000023249393197/5000000000000000 : ℝ) by norm_num, show 1+2*(238029863216959/25000000000000000000 : ℝ)=(12500238029863216959/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71502736830451751/50000000000000000000 : ℝ)+(238029863216959/25000000000000000000 : ℝ) ≤ ((71279734957064871303/71300000000000000000 : ℝ)+(3466853944137/1426000000000000 : ℝ)*((20201/100000 : ℝ)+(5941/100000 : ℝ)))^(8387/2048 : ℝ) := by
    rw [show (71279734957064871303/71300000000000000000 : ℝ)+(3466853944137/1426000000000000 : ℝ)*((20201/100000 : ℝ)+(5941/100000 : ℝ))=(10003513352730531/10000000000000000 : ℝ) by norm_num, show 1+(71502736830451751/50000000000000000000 : ℝ)+(238029863216959/25000000000000000000 : ℝ)=(50071978796556885669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71502736830451751/50000000000000000000 : ℝ) ≤ ((71279734957064871303/71300000000000000000 : ℝ)+2*(3466853944137/1426000000000000 : ℝ)*(20201/100000 : ℝ))^(8387/2048 : ℝ) := by
    rw [show (71279734957064871303/71300000000000000000 : ℝ)+2*(3466853944137/1426000000000000 : ℝ)*(20201/100000 : ℝ)=(2501745051668667/2500000000000000 : ℝ) by norm_num, show 1+2*(71502736830451751/50000000000000000000 : ℝ)=(25071502736830451751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71279734957064871303/71300000000000000000 : ℝ)*(X 1 0+X 2 0)+(3466853944137/1426000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5941/100000 : ℝ)) (hi := (20201/100000 : ℝ)) (c := (71279734957064871303/71300000000000000000 : ℝ)) (alpha := (3466853944137/1426000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71279734957064871303/71300000000000000000 : ℝ)*(X 0 1+X 2 1)+(3466853944137/1426000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5941/100000 : ℝ)) (hi := (20201/100000 : ℝ)) (c := (71279734957064871303/71300000000000000000 : ℝ)) (alpha := (3466853944137/1426000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71279734957064871303/71300000000000000000 : ℝ)*(X 0 2+X 1 2)+(3466853944137/1426000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8387/2048 : ℝ)) (lo := (5941/100000 : ℝ)) (hi := (20201/100000 : ℝ)) (c := (71279734957064871303/71300000000000000000 : ℝ)) (alpha := (3466853944137/1426000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1063206117/5000000000 : ℝ)*X 0 0+(1375252349/2500000000 : ℝ)*X 0 1+(5167614007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2685809161/5000000000 : ℝ)*X 1 0+(-18395163/80000000 : ℝ)*X 1 1+(322976141/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1074324019/2000000000 : ℝ)*X 2 0+(5167615777/10000000000 : ℝ)*X 2 1+(-287424533/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1086911209/2500000000 : ℝ)*X 0 0+(1006299373/2500000000 : ℝ)*X 0 1+(1173844283/2500000000 : ℝ)*X 0 2+(1086911209/2500000000 : ℝ)*X 1 0+(1006299373/2500000000 : ℝ)*X 1 1+(1173844283/2500000000 : ℝ)*X 1 2+(1086911209/2500000000 : ℝ)*X 2 0+(1006299373/2500000000 : ℝ)*X 2 1+(1173844283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2126500071/10000000000 : ℝ)*X 0 0+(5169830259/10000000000 : ℝ)*X 0 1+(5498772541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660841669/1250000000 : ℝ)*X 1 0+(-984119727/5000000000 : ℝ)*X 1 1+(2749386279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66084169/125000000 : ℝ)*X 2 0+(5498772571/10000000000 : ℝ)*X 2 1+(-393647841/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543477959/1250000000 : ℝ)*X 0 0+(469092479/1000000000 : ℝ)*X 0 1+(2014846029/5000000000 : ℝ)*X 0 2+(543477959/1250000000 : ℝ)*X 1 0+(469092479/1000000000 : ℝ)*X 1 1+(2014846029/5000000000 : ℝ)*X 1 2+(543477959/1250000000 : ℝ)*X 2 0+(469092479/1000000000 : ℝ)*X 2 1+(2014846029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1195_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6353390515093999998427404783/713000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1457926503/100000000000000 : ℝ)*(base19) + (513155787/25000000000000 : ℝ)*(base23) + (62177511/100000000000000 : ℝ)*(upper2) + (680729119/100000000000000 : ℝ)*(upper3) + (274544807/100000000000000 : ℝ)*(upper4) + (449169690113871/20000000000000 : ℝ)*(major0) + (449169690113871/20000000000000 : ℝ)*(major1) + (449169690113871/20000000000000 : ℝ)*(major2) + (299948701851351/10000000000000 : ℝ)*(sp0) + (2999524765233141/100000000000000 : ℝ)*(sp1) + (187470260658531/6250000000000 : ℝ)*(sp2) + (23314836926539/1562500000000 : ℝ)*(sp3) + (19602323067/50000000000000 : ℝ)*(sp4) + (20817654359/100000000000000 : ℝ)*(sp7) + (186521297619107/12500000000000 : ℝ)*(f.failure) + (749881555789911/25000000000000 : ℝ)*(f.sum) + (35598099151327/14260000000000000000000000000 : ℝ)*base65 + (672502802038493913/1426000000000000000000000000000000 : ℝ)*base67 + (16753397780738493913/1426000000000000000000000000000000 : ℝ)*base69 + (6575255832890493913/1426000000000000000000000000000000 : ℝ)*base71 + (46676511806907/14260000000000000000000000000 : ℝ)*base73 + (2961010229106493913/1426000000000000000000000000000000 : ℝ)*base75 + (6507837807022493913/1426000000000000000000000000000000 : ℝ)*base77 + (9399068478762493913/1426000000000000000000000000000000 : ℝ)*base79 + (117083627853327/14260000000000000000000000000 : ℝ)*base81 + (8829/78125000000000000000 : ℝ)*base90 + (8829/78125000000000000000 : ℝ)*base92 + (8829/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3469274139994161755182401261/445625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1873029157/100000000000000 : ℝ)*(base19) + (40857681/2000000000000 : ℝ)*(base23) + (1423911/20000000000000 : ℝ)*(upper2) + (9398251/4000000000000 : ℝ)*(upper3) + (80834799/50000000000000 : ℝ)*(upper5) + (569046758073129/25000000000000 : ℝ)*(major0) + (569046758073129/25000000000000 : ℝ)*(major1) + (569046758073129/25000000000000 : ℝ)*(major2) + (18520213187/100000000000000 : ℝ)*(sp1) + (1390195029/6250000000000 : ℝ)*(sp2) + (1520023041564081/50000000000000 : ℝ)*(sp4) + (3040025689885817/100000000000000 : ℝ)*(sp5) + (3040021797123647/100000000000000 : ℝ)*(sp6) + (1512327721950617/100000000000000 : ℝ)*(sp7) + (1512327721950617/100000000000000 : ℝ)*(f.failure) + (1520023041564081/50000000000000 : ℝ)*(f.sum) + (92132005170023/17825000000000000000000000000 : ℝ)*base65 + (13362054861728832913/1782500000000000000000000000000000 : ℝ)*base68 + (5736430808028832913/1782500000000000000000000000000000 : ℝ)*base70 + (1789596124833832913/1782500000000000000000000000000000 : ℝ)*base72 + (27483113714301/8912500000000000000000000000 : ℝ)*base74 + (2593441454798832913/1782500000000000000000000000000000 : ℝ)*base76 + (9499349413201167087/1782500000000000000000000000000000 : ℝ)*base77 + (4475210396706332913/1782500000000000000000000000000000 : ℝ)*base80 + (23793072109649/8912500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4847451/625000000000000000000 : ℝ)*base89 + (4847451/625000000000000000000 : ℝ)*base91 + (4847451/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1195_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20201/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5941/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1195_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1195_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1195_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1195_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1195_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8387/2048 : ℝ) ≤ p) (hpb : p ≤ (2097/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9406803/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1195_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:54:46.609012+00:00
-- url     : https://prove2.me/submissions/1381ea16-8864-437a-b3b7-2b3a88b32f6b

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
theorem support_rectangle_w1051_s0_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1920949389/10000000000 : ℝ)*x 0 + (6075602653/10000000000 : ℝ)*x 1 + (2384428279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920949389/10000000000 : ℝ)^2061 ≤ (556752618399/5000000000000 : ℝ)^1549 := by
    have hnat : (1920949389 : ℕ)^2061*5000000000000^1549 ≤ 556752618399^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920949389 10000000000 556752618399 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6075602653/10000000000 : ℝ)^2061 ≤ (12882433294237/25000000000000 : ℝ)^1549 := by
    have hnat : (6075602653 : ℕ)^2061*25000000000000^1549 ≤ 12882433294237^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6075602653 10000000000 12882433294237 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384428279/5000000000 : ℝ)^2061 ≤ (583362725517/1562500000000 : ℝ)^1549 := by
    have hnat : (2384428279 : ℕ)^2061*1562500000000^1549 ≤ 583362725517^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384428279 5000000000 583362725517 1562500000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1920949389/10000000000 : ℝ), (6075602653/10000000000 : ℝ), (2384428279/5000000000 : ℝ)] ![(556752618399/5000000000000 : ℝ), (12882433294237/25000000000000 : ℝ), (583362725517/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1920949389/10000000000 : ℝ)|^2061 ≤ (556752618399/5000000000000 : ℝ)^1549
        have hw : |(-1920949389/10000000000 : ℝ)|=(1920949389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6075602653/10000000000 : ℝ)|^2061 ≤ (12882433294237/25000000000000 : ℝ)^1549
        have hw : |(6075602653/10000000000 : ℝ)|=(6075602653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2384428279/5000000000 : ℝ)|^2061 ≤ (583362725517/1562500000000 : ℝ)^1549
        have hw : |(2384428279/5000000000 : ℝ)|=(2384428279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2760958483/5000000000 : ℝ)*x 0 + (-534713987/2000000000 : ℝ)*x 1 + (4768856599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760958483/5000000000 : ℝ)^2061 ≤ (45377580261301/100000000000000 : ℝ)^1549 := by
    have hnat : (2760958483 : ℕ)^2061*100000000000000^1549 ≤ 45377580261301^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760958483 5000000000 45377580261301 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534713987/2000000000 : ℝ)^2061 ≤ (17287204862433/100000000000000 : ℝ)^1549 := by
    have hnat : (534713987 : ℕ)^2061*100000000000000^1549 ≤ 17287204862433^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534713987 2000000000 17287204862433 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4768856599/10000000000 : ℝ)^2061 ≤ (37335214860173/100000000000000 : ℝ)^1549 := by
    have hnat : (4768856599 : ℕ)^2061*100000000000000^1549 ≤ 37335214860173^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768856599 10000000000 37335214860173 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2760958483/5000000000 : ℝ), (-534713987/2000000000 : ℝ), (4768856599/10000000000 : ℝ)] ![(45377580261301/100000000000000 : ℝ), (17287204862433/100000000000000 : ℝ), (37335214860173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2760958483/5000000000 : ℝ)|^2061 ≤ (45377580261301/100000000000000 : ℝ)^1549
        have hw : |(2760958483/5000000000 : ℝ)|=(2760958483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534713987/2000000000 : ℝ)|^2061 ≤ (17287204862433/100000000000000 : ℝ)^1549
        have hw : |(-534713987/2000000000 : ℝ)|=(534713987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4768856599/10000000000 : ℝ)|^2061 ≤ (37335214860173/100000000000000 : ℝ)^1549
        have hw : |(4768856599/10000000000 : ℝ)|=(4768856599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (220876679/400000000 : ℝ)*x 0 + (4768856803/10000000000 : ℝ)*x 1 + (-2673569677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220876679/400000000 : ℝ)^2061 ≤ (45377580359707/100000000000000 : ℝ)^1549 := by
    have hnat : (220876679 : ℕ)^2061*100000000000000^1549 ≤ 45377580359707^1549*400000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220876679 400000000 45377580359707 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4768856803/10000000000 : ℝ)^2061 ≤ (1166725530787/3125000000000 : ℝ)^1549 := by
    have hnat : (4768856803 : ℕ)^2061*3125000000000^1549 ≤ 1166725530787^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768856803 10000000000 1166725530787 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2673569677/10000000000 : ℝ)^2061 ≤ (17287202642809/100000000000000 : ℝ)^1549 := by
    have hnat : (2673569677 : ℕ)^2061*100000000000000^1549 ≤ 17287202642809^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673569677 10000000000 17287202642809 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(220876679/400000000 : ℝ), (4768856803/10000000000 : ℝ), (-2673569677/10000000000 : ℝ)] ![(45377580359707/100000000000000 : ℝ), (1166725530787/3125000000000 : ℝ), (17287202642809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(220876679/400000000 : ℝ)|^2061 ≤ (45377580359707/100000000000000 : ℝ)^1549
        have hw : |(220876679/400000000 : ℝ)|=(220876679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4768856803/10000000000 : ℝ)|^2061 ≤ (1166725530787/3125000000000 : ℝ)^1549
        have hw : |(4768856803/10000000000 : ℝ)|=(4768856803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2673569677/10000000000 : ℝ)|^2061 ≤ (17287202642809/100000000000000 : ℝ)^1549
        have hw : |(-2673569677/10000000000 : ℝ)|=(2673569677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4208454453/10000000000 : ℝ)*x 0 + (781419623/2500000000 : ℝ)*x 1 + (709886781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4208454453/10000000000 : ℝ)^2061 ≤ (7903540845517/25000000000000 : ℝ)^1549 := by
    have hnat : (4208454453 : ℕ)^2061*25000000000000^1549 ≤ 7903540845517^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4208454453 10000000000 7903540845517 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781419623/2500000000 : ℝ)^2061 ≤ (5320412555687/25000000000000 : ℝ)^1549 := by
    have hnat : (781419623 : ℕ)^2061*25000000000000^1549 ≤ 5320412555687^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781419623 2500000000 5320412555687 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709886781/1250000000 : ℝ)^2061 ≤ (47104186378099/100000000000000 : ℝ)^1549 := by
    have hnat : (709886781 : ℕ)^2061*100000000000000^1549 ≤ 47104186378099^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709886781 1250000000 47104186378099 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4208454453/10000000000 : ℝ), (781419623/2500000000 : ℝ), (709886781/1250000000 : ℝ)] ![(7903540845517/25000000000000 : ℝ), (5320412555687/25000000000000 : ℝ), (47104186378099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4208454453/10000000000 : ℝ)|^2061 ≤ (7903540845517/25000000000000 : ℝ)^1549
        have hw : |(4208454453/10000000000 : ℝ)|=(4208454453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781419623/2500000000 : ℝ)|^2061 ≤ (5320412555687/25000000000000 : ℝ)^1549
        have hw : |(781419623/2500000000 : ℝ)|=(781419623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709886781/1250000000 : ℝ)|^2061 ≤ (47104186378099/100000000000000 : ℝ)^1549
        have hw : |(709886781/1250000000 : ℝ)|=(709886781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-481591953/2500000000 : ℝ)*x 0 + (2401301911/5000000000 : ℝ)*x 1 + (241627077/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (481591953/2500000000 : ℝ)^2061 ≤ (11176862169173/100000000000000 : ℝ)^1549 := by
    have hnat : (481591953 : ℕ)^2061*100000000000000^1549 ≤ 11176862169173^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481591953 2500000000 11176862169173 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2401301911/5000000000 : ℝ)^2061 ≤ (2355447543599/6250000000000 : ℝ)^1549 := by
    have hnat : (2401301911 : ℕ)^2061*6250000000000^1549 ≤ 2355447543599^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401301911 5000000000 2355447543599 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241627077/400000000 : ℝ)^2061 ≤ (5113597712207/10000000000000 : ℝ)^1549 := by
    have hnat : (241627077 : ℕ)^2061*10000000000000^1549 ≤ 5113597712207^1549*400000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241627077 400000000 5113597712207 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-481591953/2500000000 : ℝ), (2401301911/5000000000 : ℝ), (241627077/400000000 : ℝ)] ![(11176862169173/100000000000000 : ℝ), (2355447543599/6250000000000 : ℝ), (5113597712207/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-481591953/2500000000 : ℝ)|^2061 ≤ (11176862169173/100000000000000 : ℝ)^1549
        have hw : |(-481591953/2500000000 : ℝ)|=(481591953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2401301911/5000000000 : ℝ)|^2061 ≤ (2355447543599/6250000000000 : ℝ)^1549
        have hw : |(2401301911/5000000000 : ℝ)|=(2401301911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241627077/400000000 : ℝ)|^2061 ≤ (5113597712207/10000000000000 : ℝ)^1549
        have hw : |(241627077/400000000 : ℝ)|=(241627077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (516732909/1000000000 : ℝ)*x 0 + (-700875193/5000000000 : ℝ)*x 1 + (1208135343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516732909/1000000000 : ℝ)^2061 ≤ (4154227733109/10000000000000 : ℝ)^1549 := by
    have hnat : (516732909 : ℕ)^2061*10000000000000^1549 ≤ 4154227733109^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516732909 1000000000 4154227733109 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700875193/5000000000 : ℝ)^2061 ≤ (1464349579341/20000000000000 : ℝ)^1549 := by
    have hnat : (700875193 : ℕ)^2061*20000000000000^1549 ≤ 1464349579341^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700875193 5000000000 1464349579341 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208135343/2000000000 : ℝ)^2061 ≤ (51135974756767/100000000000000 : ℝ)^1549 := by
    have hnat : (1208135343 : ℕ)^2061*100000000000000^1549 ≤ 51135974756767^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208135343 2000000000 51135974756767 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516732909/1000000000 : ℝ), (-700875193/5000000000 : ℝ), (1208135343/2000000000 : ℝ)] ![(4154227733109/10000000000000 : ℝ), (1464349579341/20000000000000 : ℝ), (51135974756767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516732909/1000000000 : ℝ)|^2061 ≤ (4154227733109/10000000000000 : ℝ)^1549
        have hw : |(516732909/1000000000 : ℝ)|=(516732909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-700875193/5000000000 : ℝ)|^2061 ≤ (1464349579341/20000000000000 : ℝ)^1549
        have hw : |(-700875193/5000000000 : ℝ)|=(700875193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208135343/2000000000 : ℝ)|^2061 ≤ (51135974756767/100000000000000 : ℝ)^1549
        have hw : |(1208135343/2000000000 : ℝ)|=(1208135343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2583664973/5000000000 : ℝ)*x 0 + (6040676067/10000000000 : ℝ)*x 1 + (-35043753/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583664973/5000000000 : ℝ)^2061 ≤ (8308457297497/20000000000000 : ℝ)^1549 := by
    have hnat : (2583664973 : ℕ)^2061*20000000000000^1549 ≤ 8308457297497^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583664973 5000000000 8308457297497 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6040676067/10000000000 : ℝ)^2061 ≤ (51135967458117/100000000000000 : ℝ)^1549 := by
    have hnat : (6040676067 : ℕ)^2061*100000000000000^1549 ≤ 51135967458117^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6040676067 10000000000 51135967458117 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35043753/250000000 : ℝ)^2061 ≤ (3660873024033/50000000000000 : ℝ)^1549 := by
    have hnat : (35043753 : ℕ)^2061*50000000000000^1549 ≤ 3660873024033^1549*250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35043753 250000000 3660873024033 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583664973/5000000000 : ℝ), (6040676067/10000000000 : ℝ), (-35043753/250000000 : ℝ)] ![(8308457297497/20000000000000 : ℝ), (51135967458117/100000000000000 : ℝ), (3660873024033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583664973/5000000000 : ℝ)|^2061 ≤ (8308457297497/20000000000000 : ℝ)^1549
        have hw : |(2583664973/5000000000 : ℝ)|=(2583664973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6040676067/10000000000 : ℝ)|^2061 ≤ (51135967458117/100000000000000 : ℝ)^1549
        have hw : |(6040676067/10000000000 : ℝ)|=(6040676067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35043753/250000000 : ℝ)|^2061 ≤ (3660873024033/50000000000000 : ℝ)^1549
        have hw : |(-35043753/250000000 : ℝ)|=(35043753/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s0_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2109521411/5000000000 : ℝ)*x 0 + (701643839/1250000000 : ℝ)*x 1 + (3193924307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109521411/5000000000 : ℝ)^2061 ≤ (31720038802819/100000000000000 : ℝ)^1549 := by
    have hnat : (2109521411 : ℕ)^2061*100000000000000^1549 ≤ 31720038802819^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109521411 5000000000 31720038802819 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701643839/1250000000 : ℝ)^2061 ≤ (11594460392471/25000000000000 : ℝ)^1549 := by
    have hnat : (701643839 : ℕ)^2061*25000000000000^1549 ≤ 11594460392471^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701643839 1250000000 11594460392471 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3193924307/10000000000 : ℝ)^2061 ≤ (21902119615933/100000000000000 : ℝ)^1549 := by
    have hnat : (3193924307 : ℕ)^2061*100000000000000^1549 ≤ 21902119615933^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3193924307 10000000000 21902119615933 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109521411/5000000000 : ℝ), (701643839/1250000000 : ℝ), (3193924307/10000000000 : ℝ)] ![(31720038802819/100000000000000 : ℝ), (11594460392471/25000000000000 : ℝ), (21902119615933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109521411/5000000000 : ℝ)|^2061 ≤ (31720038802819/100000000000000 : ℝ)^1549
        have hw : |(2109521411/5000000000 : ℝ)|=(2109521411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(701643839/1250000000 : ℝ)|^2061 ≤ (11594460392471/25000000000000 : ℝ)^1549
        have hw : |(701643839/1250000000 : ℝ)|=(701643839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3193924307/10000000000 : ℝ)|^2061 ≤ (21902119615933/100000000000000 : ℝ)^1549
        have hw : |(3193924307/10000000000 : ℝ)|=(3193924307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (33/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/12500 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8243/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8243 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8243*1^2048 ≤ 0^2048*1^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8243/2048 : ℝ) ≤ (2502247859562279541/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8243 ≤ (2502247859562279541/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8243*100000000000000000000^2048 ≤ 2502247859562279541^2048*5^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2502247859562279541 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2502247859562279541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8243 := by
      have hnat : (1 : ℕ)^2048*1^8243 ≤ 1^8243*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102502247859562279541/100000000000000000000 : ℝ) ≤ (2012318597971073/2000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (102502247859562279541/100000000000000000000 : ℝ)^2048 ≤ (2012318597971073/2000000000000000 : ℝ)^8243 := by
      have hnat : (102502247859562279541 : ℕ)^2048*2000000000000000^8243 ≤ 2012318597971073^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102502247859562279541 100000000000000000000 2012318597971073 2000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012318597971073/2000000000000000 : ℝ)) (X := (102502247859562279541/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52502247859562279541/50000000000000000000 : ℝ) ≤ (1012318597971073/1000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (52502247859562279541/50000000000000000000 : ℝ)^2048 ≤ (1012318597971073/1000000000000000 : ℝ)^8243 := by
      have hnat : (52502247859562279541 : ℕ)^2048*1000000000000000^8243 ≤ 1012318597971073^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52502247859562279541 50000000000000000000 1012318597971073 1000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012318597971073/1000000000000000 : ℝ)) (X := (52502247859562279541/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12318597971073/800000000000000 : ℝ)*(0 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12318597971073/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2502247859562279541/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12318597971073/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (1 : ℝ)+(12318597971073/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012318597971073/2000000000000000 : ℝ) by norm_num, show 1+(2502247859562279541/100000000000000000000 : ℝ)+(0 : ℝ)=(102502247859562279541/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2502247859562279541/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12318597971073/800000000000000 : ℝ)*(2/5 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12318597971073/800000000000000 : ℝ)*(2/5 : ℝ)=(1012318597971073/1000000000000000 : ℝ) by norm_num, show 1+2*(2502247859562279541/100000000000000000000 : ℝ)=(52502247859562279541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12318597971073/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12318597971073/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12318597971073/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12318597971073/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12318597971073/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12318597971073/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1920949389/10000000000 : ℝ)*X 0 0+(6075602653/10000000000 : ℝ)*X 0 1+(2384428279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2760958483/5000000000 : ℝ)*X 1 0+(-534713987/2000000000 : ℝ)*X 1 1+(4768856599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((220876679/400000000 : ℝ)*X 2 0+(4768856803/10000000000 : ℝ)*X 2 1+(-2673569677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4208454453/10000000000 : ℝ)*X 0 0+(781419623/2500000000 : ℝ)*X 0 1+(709886781/1250000000 : ℝ)*X 0 2+(4208454453/10000000000 : ℝ)*X 1 0+(781419623/2500000000 : ℝ)*X 1 1+(709886781/1250000000 : ℝ)*X 1 2+(4208454453/10000000000 : ℝ)*X 2 0+(781419623/2500000000 : ℝ)*X 2 1+(709886781/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-481591953/2500000000 : ℝ)*X 0 0+(2401301911/5000000000 : ℝ)*X 0 1+(241627077/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((516732909/1000000000 : ℝ)*X 1 0+(-700875193/5000000000 : ℝ)*X 1 1+(1208135343/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2583664973/5000000000 : ℝ)*X 2 0+(6040676067/10000000000 : ℝ)*X 2 1+(-35043753/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2109521411/5000000000 : ℝ)*X 0 0+(701643839/1250000000 : ℝ)*X 0 1+(3193924307/10000000000 : ℝ)*X 0 2+(2109521411/5000000000 : ℝ)*X 1 0+(701643839/1250000000 : ℝ)*X 1 1+(3193924307/10000000000 : ℝ)*X 1 2+(2109521411/5000000000 : ℝ)*X 2 0+(701643839/1250000000 : ℝ)*X 2 1+(3193924307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (173155914746200753913727/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7492239/12500000000000 : ℝ)*(base1) + (1036142009/100000000000000 : ℝ)*(base19) + (474345623/50000000000000 : ℝ)*(base23) + (88698043/100000000000000 : ℝ)*(base24) + (235091577/100000000000000 : ℝ)*(upper3) + (578450145282489/100000000000000 : ℝ)*(major0) + (578450145282489/100000000000000 : ℝ)*(major1) + (578450145282489/100000000000000 : ℝ)*(major2) + (95657868286537/12500000000000 : ℝ)*(sp0) + (382632031721673/50000000000000 : ℝ)*(sp1) + (382632031098033/50000000000000 : ℝ)*(sp2) + (195816627588963/50000000000000 : ℝ)*(sp3) + (2213230971/100000000000000 : ℝ)*(sp4) + (1731567183/100000000000000 : ℝ)*(sp7) + (19581752334151/5000000000000 : ℝ)*(f.failure) + (153053019917071/20000000000000 : ℝ)*(f.sum) + (16821743120697/40000000000000000000000000000 : ℝ)*base65 + (204768911599303/80000000000000000000000000000 : ℝ)*base68 + (188685181680697/80000000000000000000000000000 : ℝ)*base69 + (160187984240697/80000000000000000000000000000 : ℝ)*base71 + (33812139679303/40000000000000000000000000000 : ℝ)*base74 + (72267668800697/80000000000000000000000000000 : ℝ)*base75 + (162875015120697/80000000000000000000000000000 : ℝ)*base77 + (268870724560697/80000000000000000000000000000 : ℝ)*base79 + (284513989560697/40000000000000000000000000000 : ℝ)*base81 + (4218227/500000000000000000000 : ℝ)*base90 + (4218227/500000000000000000000 : ℝ)*base92 + (4218227/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17095340753532248575809/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128031489/100000000000000 : ℝ)*(base1) + (1605792123/100000000000000 : ℝ)*(base19) + (871639477/50000000000000 : ℝ)*(base23) + (184021801/50000000000000 : ℝ)*(base45) + (8671997/5000000000000 : ℝ)*(upper3) + (111045321/50000000000000 : ℝ)*(upper5) + (38158066533389/6250000000000 : ℝ)*(major0) + (38158066533389/6250000000000 : ℝ)*(major1) + (38158066533389/6250000000000 : ℝ)*(major2) + (53714597/100000000000000 : ℝ)*(sp2) + (403852103320651/50000000000000 : ℝ)*(sp4) + (80770247281769/10000000000000 : ℝ)*(sp5) + (807702281616263/100000000000000 : ℝ)*(sp6) + (25834605905579/6250000000000 : ℝ)*(sp7) + (413353822520753/100000000000000 : ℝ)*(f.failure) + (403852039304907/50000000000000 : ℝ)*(f.sum) + (696281196397/2500000000000000000000000000 : ℝ)*base65 + (13053050403603/5000000000000000000000000000 : ℝ)*base68 + (29360528666397/5000000000000000000000000000 : ℝ)*base69 + (4083685116397/5000000000000000000000000000 : ℝ)*base71 + (3804058413603/2500000000000000000000000000 : ℝ)*base74 + (961868666397/5000000000000000000000000000 : ℝ)*base75 + (7198783748603/5000000000000000000000000000 : ℝ)*base78 + (15741424243603/5000000000000000000000000000 : ℝ)*base80 + (14191852358897/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13056219/10000000000000000000000 : ℝ)*base89 + (13056219/10000000000000000000000 : ℝ)*base91 + (13056219/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1051_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (33/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_s1_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132151171/10000000000 : ℝ)*x 0 + (357909449/625000000 : ℝ)*x 1 + (4982640967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132151171/10000000000 : ℝ)^2061 ≤ (2558575797917/20000000000000 : ℝ)^1549 := by
    have hnat : (2132151171 : ℕ)^2061*20000000000000^1549 ≤ 2558575797917^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132151171 10000000000 2558575797917 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357909449/625000000 : ℝ)^2061 ≤ (47628637422893/100000000000000 : ℝ)^1549 := by
    have hnat : (357909449 : ℕ)^2061*100000000000000^1549 ≤ 47628637422893^1549*625000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357909449 625000000 47628637422893 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4982640967/10000000000 : ℝ)^2061 ≤ (19789241789659/50000000000000 : ℝ)^1549 := by
    have hnat : (4982640967 : ℕ)^2061*50000000000000^1549 ≤ 19789241789659^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4982640967 10000000000 19789241789659 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132151171/10000000000 : ℝ), (357909449/625000000 : ℝ), (4982640967/10000000000 : ℝ)] ![(2558575797917/20000000000000 : ℝ), (47628637422893/100000000000000 : ℝ), (19789241789659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132151171/10000000000 : ℝ)|^2061 ≤ (2558575797917/20000000000000 : ℝ)^1549
        have hw : |(-2132151171/10000000000 : ℝ)|=(2132151171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(357909449/625000000 : ℝ)|^2061 ≤ (47628637422893/100000000000000 : ℝ)^1549
        have hw : |(357909449/625000000 : ℝ)|=(357909449/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4982640967/10000000000 : ℝ)|^2061 ≤ (19789241789659/50000000000000 : ℝ)^1549
        have hw : |(4982640967/10000000000 : ℝ)|=(4982640967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2712071497/5000000000 : ℝ)*x 0 + (-507105447/2000000000 : ℝ)*x 1 + (1245660323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712071497/5000000000 : ℝ)^2061 ≤ (8862332611277/20000000000000 : ℝ)^1549 := by
    have hnat : (2712071497 : ℕ)^2061*20000000000000^1549 ≤ 8862332611277^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712071497 5000000000 8862332611277 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507105447/2000000000 : ℝ)^2061 ≤ (16109849912281/100000000000000 : ℝ)^1549 := by
    have hnat : (507105447 : ℕ)^2061*100000000000000^1549 ≤ 16109849912281^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507105447 2000000000 16109849912281 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245660323/2500000000 : ℝ)^2061 ≤ (39578487014181/100000000000000 : ℝ)^1549 := by
    have hnat : (1245660323 : ℕ)^2061*100000000000000^1549 ≤ 39578487014181^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245660323 2500000000 39578487014181 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712071497/5000000000 : ℝ), (-507105447/2000000000 : ℝ), (1245660323/2500000000 : ℝ)] ![(8862332611277/20000000000000 : ℝ), (16109849912281/100000000000000 : ℝ), (39578487014181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712071497/5000000000 : ℝ)|^2061 ≤ (8862332611277/20000000000000 : ℝ)^1549
        have hw : |(2712071497/5000000000 : ℝ)|=(2712071497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507105447/2000000000 : ℝ)|^2061 ≤ (16109849912281/100000000000000 : ℝ)^1549
        have hw : |(-507105447/2000000000 : ℝ)|=(507105447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1245660323/2500000000 : ℝ)|^2061 ≤ (39578487014181/100000000000000 : ℝ)^1549
        have hw : |(1245660323/2500000000 : ℝ)|=(1245660323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67801793/125000000 : ℝ)*x 0 + (2491320377/5000000000 : ℝ)*x 1 + (-1267763667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67801793/125000000 : ℝ)^2061 ≤ (22155833952113/50000000000000 : ℝ)^1549 := by
    have hnat : (67801793 : ℕ)^2061*50000000000000^1549 ≤ 22155833952113^1549*125000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67801793 125000000 22155833952113 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2491320377/5000000000 : ℝ)^2061 ≤ (39578481328161/100000000000000 : ℝ)^1549 := by
    have hnat : (2491320377 : ℕ)^2061*100000000000000^1549 ≤ 39578481328161^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491320377 5000000000 39578481328161 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267763667/5000000000 : ℝ)^2061 ≤ (16109850749203/100000000000000 : ℝ)^1549 := by
    have hnat : (1267763667 : ℕ)^2061*100000000000000^1549 ≤ 16109850749203^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267763667 5000000000 16109850749203 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67801793/125000000 : ℝ), (2491320377/5000000000 : ℝ), (-1267763667/5000000000 : ℝ)] ![(22155833952113/50000000000000 : ℝ), (39578481328161/100000000000000 : ℝ), (16109850749203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67801793/125000000 : ℝ)|^2061 ≤ (22155833952113/50000000000000 : ℝ)^1549
        have hw : |(67801793/125000000 : ℝ)|=(67801793/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2491320377/5000000000 : ℝ)|^2061 ≤ (39578481328161/100000000000000 : ℝ)^1549
        have hw : |(2491320377/5000000000 : ℝ)|=(2491320377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267763667/5000000000 : ℝ)|^2061 ≤ (16109850749203/100000000000000 : ℝ)^1549
        have hw : |(-1267763667/5000000000 : ℝ)|=(1267763667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (865008007/2000000000 : ℝ)*x 0 + (365962789/1000000000 : ℝ)*x 1 + (5113246803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865008007/2000000000 : ℝ)^2061 ≤ (32784746366199/100000000000000 : ℝ)^1549 := by
    have hnat : (865008007 : ℕ)^2061*100000000000000^1549 ≤ 32784746366199^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865008007 2000000000 32784746366199 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (365962789/1000000000 : ℝ)^2061 ≤ (13125238268367/50000000000000 : ℝ)^1549 := by
    have hnat : (365962789 : ℕ)^2061*50000000000000^1549 ≤ 13125238268367^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365962789 1000000000 13125238268367 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5113246803/10000000000 : ℝ)^2061 ≤ (4096477708241/10000000000000 : ℝ)^1549 := by
    have hnat : (5113246803 : ℕ)^2061*10000000000000^1549 ≤ 4096477708241^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113246803 10000000000 4096477708241 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865008007/2000000000 : ℝ), (365962789/1000000000 : ℝ), (5113246803/10000000000 : ℝ)] ![(32784746366199/100000000000000 : ℝ), (13125238268367/50000000000000 : ℝ), (4096477708241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865008007/2000000000 : ℝ)|^2061 ≤ (32784746366199/100000000000000 : ℝ)^1549
        have hw : |(865008007/2000000000 : ℝ)|=(865008007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(365962789/1000000000 : ℝ)|^2061 ≤ (13125238268367/50000000000000 : ℝ)^1549
        have hw : |(365962789/1000000000 : ℝ)|=(365962789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5113246803/10000000000 : ℝ)|^2061 ≤ (4096477708241/10000000000000 : ℝ)^1549
        have hw : |(5113246803/10000000000 : ℝ)|=(5113246803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133097073/10000000000 : ℝ)*x 0 + (4993154607/10000000000 : ℝ)*x 1 + (5715820921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133097073/10000000000 : ℝ)^2061 ≤ (12800430865651/100000000000000 : ℝ)^1549 := by
    have hnat : (2133097073 : ℕ)^2061*100000000000000^1549 ≤ 12800430865651^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133097073 10000000000 12800430865651 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993154607/10000000000 : ℝ)^2061 ≤ (39689638983863/100000000000000 : ℝ)^1549 := by
    have hnat : (4993154607 : ℕ)^2061*100000000000000^1549 ≤ 39689638983863^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993154607 10000000000 39689638983863 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5715820921/10000000000 : ℝ)^2061 ≤ (47509930134661/100000000000000 : ℝ)^1549 := by
    have hnat : (5715820921 : ℕ)^2061*100000000000000^1549 ≤ 47509930134661^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5715820921 10000000000 47509930134661 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133097073/10000000000 : ℝ), (4993154607/10000000000 : ℝ), (5715820921/10000000000 : ℝ)] ![(12800430865651/100000000000000 : ℝ), (39689638983863/100000000000000 : ℝ), (47509930134661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133097073/10000000000 : ℝ)|^2061 ≤ (12800430865651/100000000000000 : ℝ)^1549
        have hw : |(-2133097073/10000000000 : ℝ)|=(2133097073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993154607/10000000000 : ℝ)|^2061 ≤ (39689638983863/100000000000000 : ℝ)^1549
        have hw : |(4993154607/10000000000 : ℝ)|=(4993154607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5715820921/10000000000 : ℝ)|^2061 ≤ (47509930134661/100000000000000 : ℝ)^1549
        have hw : |(5715820921/10000000000 : ℝ)|=(5715820921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5234309881/10000000000 : ℝ)*x 0 + (-1802345821/10000000000 : ℝ)*x 1 + (571582227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234309881/10000000000 : ℝ)^2061 ≤ (845205655337/2000000000000 : ℝ)^1549 := by
    have hnat : (5234309881 : ℕ)^2061*2000000000000^1549 ≤ 845205655337^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234309881 10000000000 845205655337 2000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1802345821/10000000000 : ℝ)^2061 ≤ (2557443038519/25000000000000 : ℝ)^1549 := by
    have hnat : (1802345821 : ℕ)^2061*25000000000000^1549 ≤ 2557443038519^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802345821 10000000000 2557443038519 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571582227/1000000000 : ℝ)^2061 ≤ (47509945053819/100000000000000 : ℝ)^1549 := by
    have hnat : (571582227 : ℕ)^2061*100000000000000^1549 ≤ 47509945053819^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571582227 1000000000 47509945053819 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234309881/10000000000 : ℝ), (-1802345821/10000000000 : ℝ), (571582227/1000000000 : ℝ)] ![(845205655337/2000000000000 : ℝ), (2557443038519/25000000000000 : ℝ), (47509945053819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234309881/10000000000 : ℝ)|^2061 ≤ (845205655337/2000000000000 : ℝ)^1549
        have hw : |(5234309881/10000000000 : ℝ)|=(5234309881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1802345821/10000000000 : ℝ)|^2061 ≤ (2557443038519/25000000000000 : ℝ)^1549
        have hw : |(-1802345821/10000000000 : ℝ)|=(1802345821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571582227/1000000000 : ℝ)|^2061 ≤ (47509945053819/100000000000000 : ℝ)^1549
        have hw : |(571582227/1000000000 : ℝ)|=(571582227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5234307939/10000000000 : ℝ)*x 0 + (1143164881/2000000000 : ℝ)*x 1 + (-1802345459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5234307939/10000000000 : ℝ)^2061 ≤ (10565065476299/25000000000000 : ℝ)^1549 := by
    have hnat : (5234307939 : ℕ)^2061*25000000000000^1549 ≤ 10565065476299^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234307939 10000000000 10565065476299 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143164881/2000000000 : ℝ)^2061 ≤ (11877492166421/25000000000000 : ℝ)^1549 := by
    have hnat : (1143164881 : ℕ)^2061*25000000000000^1549 ≤ 11877492166421^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143164881 2000000000 11877492166421 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1802345459/10000000000 : ℝ)^2061 ≤ (102297694203/1000000000000 : ℝ)^1549 := by
    have hnat : (1802345459 : ℕ)^2061*1000000000000^1549 ≤ 102297694203^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1802345459 10000000000 102297694203 1000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5234307939/10000000000 : ℝ), (1143164881/2000000000 : ℝ), (-1802345459/10000000000 : ℝ)] ![(10565065476299/25000000000000 : ℝ), (11877492166421/25000000000000 : ℝ), (102297694203/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5234307939/10000000000 : ℝ)|^2061 ≤ (10565065476299/25000000000000 : ℝ)^1549
        have hw : |(5234307939/10000000000 : ℝ)|=(5234307939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143164881/2000000000 : ℝ)|^2061 ≤ (11877492166421/25000000000000 : ℝ)^1549
        have hw : |(1143164881/2000000000 : ℝ)|=(1143164881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1802345459/10000000000 : ℝ)|^2061 ≤ (102297694203/1000000000000 : ℝ)^1549
        have hw : |(-1802345459/10000000000 : ℝ)|=(1802345459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s1_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (865376997/2000000000 : ℝ)*x 0 + (1273174869/2500000000 : ℝ)*x 1 + (736118451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865376997/2000000000 : ℝ)^2061 ≤ (32803355385421/100000000000000 : ℝ)^1549 := by
    have hnat : (865376997 : ℕ)^2061*100000000000000^1549 ≤ 32803355385421^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865376997 2000000000 32803355385421 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273174869/2500000000 : ℝ)^2061 ≤ (8149179326987/20000000000000 : ℝ)^1549 := by
    have hnat : (1273174869 : ℕ)^2061*20000000000000^1549 ≤ 8149179326987^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273174869 2500000000 8149179326987 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736118451/2000000000 : ℝ)^2061 ≤ (13225373983063/50000000000000 : ℝ)^1549 := by
    have hnat : (736118451 : ℕ)^2061*50000000000000^1549 ≤ 13225373983063^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736118451 2000000000 13225373983063 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865376997/2000000000 : ℝ), (1273174869/2500000000 : ℝ), (736118451/2000000000 : ℝ)] ![(32803355385421/100000000000000 : ℝ), (8149179326987/20000000000000 : ℝ), (13225373983063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865376997/2000000000 : ℝ)|^2061 ≤ (32803355385421/100000000000000 : ℝ)^1549
        have hw : |(865376997/2000000000 : ℝ)|=(865376997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1273174869/2500000000 : ℝ)|^2061 ≤ (8149179326987/20000000000000 : ℝ)^1549
        have hw : |(1273174869/2500000000 : ℝ)|=(1273174869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(736118451/2000000000 : ℝ)|^2061 ≤ (13225373983063/50000000000000 : ℝ)^1549
        have hw : |(736118451/2000000000 : ℝ)|=(736118451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1281/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20863/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (33/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (33/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (33/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (33/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (33/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (33/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (33/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (60707/6250000000000000000 : ℝ) := by
    have hpowers : (33/100000 : ℝ)^8243 ≤ (60707/6250000000000000000 : ℝ)^2048 := by
      have hnat : (33 : ℕ)^8243*6250000000000000000^2048 ≤ 60707^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33 100000 60707 6250000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33/100000 : ℝ)) (X := (60707/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/12500 : ℝ) ^ (8243/2048 : ℝ) ≤ (609988550423143307/100000000000000000000 : ℝ) := by
    have hpowers : (3521/12500 : ℝ)^8243 ≤ (609988550423143307/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3521 : ℕ)^8243*100000000000000000000^2048 ≤ 609988550423143307^2048*12500^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 12500 609988550423143307 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/12500 : ℝ)) (X := (609988550423143307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000000000060707/3125000000000000000 : ℝ) ≤ (10000000000000049/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (3125000000000060707/3125000000000000000 : ℝ)^2048 ≤ (10000000000000049/10000000000000000 : ℝ)^8243 := by
      have hnat : (3125000000000060707 : ℕ)^2048*10000000000000000^8243 ≤ 10000000000000049^8243*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000000000060707 3125000000000000000 10000000000000049 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000049/10000000000000000 : ℝ)) (X := (3125000000000060707/3125000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100609988550424114619/100000000000000000000 : ℝ) ≤ (10015120747211817/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (100609988550424114619/100000000000000000000 : ℝ)^2048 ≤ (10015120747211817/10000000000000000 : ℝ)^8243 := by
      have hnat : (100609988550424114619 : ℕ)^2048*10000000000000000^8243 ≤ 10015120747211817^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100609988550424114619 100000000000000000000 10015120747211817 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015120747211817/10000000000000000 : ℝ)) (X := (100609988550424114619/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50609988550423143307/50000000000000000000 : ℝ) ≤ (2006048298884717/2000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50609988550423143307/50000000000000000000 : ℝ)^2048 ≤ (2006048298884717/2000000000000000 : ℝ)^8243 := by
      have hnat : (50609988550423143307 : ℕ)^2048*2000000000000000^8243 ≤ 2006048298884717^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50609988550423143307 50000000000000000000 2006048298884717 2000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006048298884717/2000000000000000 : ℝ)) (X := (50609988550423143307/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(60707/6250000000000000000 : ℝ) ≤ ((281349002030685401927/281350000000000000000 : ℝ)+2*(1890093401471/351687500000000 : ℝ)*(33/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (281349002030685401927/281350000000000000000 : ℝ)+2*(1890093401471/351687500000000 : ℝ)*(33/100000 : ℝ)=(10000000000000049/10000000000000000 : ℝ) by norm_num, show 1+2*(60707/6250000000000000000 : ℝ)=(3125000000000060707/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(609988550423143307/100000000000000000000 : ℝ)+(60707/6250000000000000000 : ℝ) ≤ ((281349002030685401927/281350000000000000000 : ℝ)+(1890093401471/351687500000000 : ℝ)*((3521/12500 : ℝ)+(33/100000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (281349002030685401927/281350000000000000000 : ℝ)+(1890093401471/351687500000000 : ℝ)*((3521/12500 : ℝ)+(33/100000 : ℝ))=(10015120747211817/10000000000000000 : ℝ) by norm_num, show 1+(609988550423143307/100000000000000000000 : ℝ)+(60707/6250000000000000000 : ℝ)=(100609988550424114619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(609988550423143307/100000000000000000000 : ℝ) ≤ ((281349002030685401927/281350000000000000000 : ℝ)+2*(1890093401471/351687500000000 : ℝ)*(3521/12500 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (281349002030685401927/281350000000000000000 : ℝ)+2*(1890093401471/351687500000000 : ℝ)*(3521/12500 : ℝ)=(2006048298884717/2000000000000000 : ℝ) by norm_num, show 1+2*(609988550423143307/100000000000000000000 : ℝ)=(50609988550423143307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (281349002030685401927/281350000000000000000 : ℝ)*(X 1 0+X 2 0)+(1890093401471/351687500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (33/100000 : ℝ)) (hi := (3521/12500 : ℝ)) (c := (281349002030685401927/281350000000000000000 : ℝ)) (alpha := (1890093401471/351687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (281349002030685401927/281350000000000000000 : ℝ)*(X 0 1+X 2 1)+(1890093401471/351687500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (33/100000 : ℝ)) (hi := (3521/12500 : ℝ)) (c := (281349002030685401927/281350000000000000000 : ℝ)) (alpha := (1890093401471/351687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (281349002030685401927/281350000000000000000 : ℝ)*(X 0 2+X 1 2)+(1890093401471/351687500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (33/100000 : ℝ)) (hi := (3521/12500 : ℝ)) (c := (281349002030685401927/281350000000000000000 : ℝ)) (alpha := (1890093401471/351687500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2132151171/10000000000 : ℝ)*X 0 0+(357909449/625000000 : ℝ)*X 0 1+(4982640967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2712071497/5000000000 : ℝ)*X 1 0+(-507105447/2000000000 : ℝ)*X 1 1+(1245660323/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((67801793/125000000 : ℝ)*X 2 0+(2491320377/5000000000 : ℝ)*X 2 1+(-1267763667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865008007/2000000000 : ℝ)*X 0 0+(365962789/1000000000 : ℝ)*X 0 1+(5113246803/10000000000 : ℝ)*X 0 2+(865008007/2000000000 : ℝ)*X 1 0+(365962789/1000000000 : ℝ)*X 1 1+(5113246803/10000000000 : ℝ)*X 1 2+(865008007/2000000000 : ℝ)*X 2 0+(365962789/1000000000 : ℝ)*X 2 1+(5113246803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2133097073/10000000000 : ℝ)*X 0 0+(4993154607/10000000000 : ℝ)*X 0 1+(5715820921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5234309881/10000000000 : ℝ)*X 1 0+(-1802345821/10000000000 : ℝ)*X 1 1+(571582227/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5234307939/10000000000 : ℝ)*X 2 0+(1143164881/2000000000 : ℝ)*X 2 1+(-1802345459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865376997/2000000000 : ℝ)*X 0 0+(1273174869/2500000000 : ℝ)*X 0 1+(736118451/2000000000 : ℝ)*X 0 2+(865376997/2000000000 : ℝ)*X 1 0+(1273174869/2500000000 : ℝ)*X 1 1+(736118451/2000000000 : ℝ)*X 1 2+(865376997/2000000000 : ℝ)*X 2 0+(1273174869/2500000000 : ℝ)*X 2 1+(736118451/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (55285664273812528779116179839/7033750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125566359/100000000000000 : ℝ)*(base1) + (1747533523/100000000000000 : ℝ)*(base19) + (1858065599/100000000000000 : ℝ)*(base23) + (3750839/2000000000000 : ℝ)*(upper3) + (36910883/20000000000000 : ℝ)*(upper5) + (1016106499129981/100000000000000 : ℝ)*(major0) + (1016106499129981/100000000000000 : ℝ)*(major1) + (1016106499129981/100000000000000 : ℝ)*(major2) + (1344256935950189/100000000000000 : ℝ)*(sp0) + (168033025791483/12500000000000 : ℝ)*(sp1) + (336066023949947/25000000000000 : ℝ)*(sp2) + (27517692515373/4000000000000 : ℝ)*(sp3) + (4571740779/50000000000000 : ℝ)*(sp4) + (4343942037/100000000000000 : ℝ)*(sp7) + (343973391196361/50000000000000 : ℝ)*(f.failure) + (336066488466347/25000000000000 : ℝ)*(f.sum) + (5588356281317/140675000000000000000000000000 : ℝ)*base66 + (47988796433998326613/28135000000000000000000000000000000 : ℝ)*base68 + (138187651974156673387/28135000000000000000000000000000000 : ℝ)*base69 + (153997480920581673387/28135000000000000000000000000000000 : ℝ)*base71 + (383778376159221/70337500000000000000000000000 : ℝ)*base74 + (232584498796211673387/28135000000000000000000000000000000 : ℝ)*base75 + (123638974571541673387/28135000000000000000000000000000000 : ℝ)*base77 + (188819315735551673387/28135000000000000000000000000000000 : ℝ)*base79 + (45069333487129/70337500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (22485603/5000000000000000000000 : ℝ)*base89 + (22485603/5000000000000000000000 : ℝ)*base91 + (22485603/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14704478671061303133468407829/7033750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2151970883/100000000000000 : ℝ)*(base19) + (1023206243/50000000000000 : ℝ)*(base23) + (197586891/100000000000000 : ℝ)*(upper2) + (20935121/6250000000000 : ℝ)*(upper3) + (478238393/100000000000000 : ℝ)*(upper5) + (522981061401809/50000000000000 : ℝ)*(major0) + (522981061401809/50000000000000 : ℝ)*(major1) + (522981061401809/50000000000000 : ℝ)*(major2) + (10551970221/100000000000000 : ℝ)*(sp1) + (11388726367/100000000000000 : ℝ)*(sp2) + (691881941094683/50000000000000 : ℝ)*(sp4) + (1383751178248263/100000000000000 : ℝ)*(sp5) + (691875223525257/50000000000000 : ℝ)*(sp6) + (17704007343313/2500000000000 : ℝ)*(sp7) + (17704007343313/2500000000000 : ℝ)*(f.failure) + (691881941094683/50000000000000 : ℝ)*(f.sum) + (293054704139363/70337500000000000000000000000 : ℝ)*base66 + (126209345020006085943/14067500000000000000000000000000000 : ℝ)*base67 + (23039847388736085943/14067500000000000000000000000000000 : ℝ)*base69 + (13566909062906414057/14067500000000000000000000000000000 : ℝ)*base72 + (229746688012387/70337500000000000000000000000 : ℝ)*base73 + (101973192306043914057/14067500000000000000000000000000000 : ℝ)*base76 + (93140352319463914057/14067500000000000000000000000000000 : ℝ)*base78 + (49187701730498914057/14067500000000000000000000000000000 : ℝ)*base80 + (25574321987103/17584375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (303099/250000000000000000000 : ℝ)*base89 + (303099/250000000000000000000 : ℝ)*base91 + (303099/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1051_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1281/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20863/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_s2_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190425487/10000000000 : ℝ)*x 0 + (138226031/250000000 : ℝ)*x 1 + (5143195217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190425487/10000000000 : ℝ)^2061 ≤ (1657522882057/12500000000000 : ℝ)^1549 := by
    have hnat : (2190425487 : ℕ)^2061*12500000000000^1549 ≤ 1657522882057^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190425487 10000000000 1657522882057 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138226031/250000000 : ℝ)^2061 ≤ (45455493492579/100000000000000 : ℝ)^1549 := by
    have hnat : (138226031 : ℕ)^2061*100000000000000^1549 ≤ 45455493492579^1549*250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138226031 250000000 45455493492579 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143195217/10000000000 : ℝ)^2061 ≤ (1651372937827/4000000000000 : ℝ)^1549 := by
    have hnat : (5143195217 : ℕ)^2061*4000000000000^1549 ≤ 1651372937827^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143195217 10000000000 1651372937827 4000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190425487/10000000000 : ℝ), (138226031/250000000 : ℝ), (5143195217/10000000000 : ℝ)] ![(1657522882057/12500000000000 : ℝ), (45455493492579/100000000000000 : ℝ), (1651372937827/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190425487/10000000000 : ℝ)|^2061 ≤ (1657522882057/12500000000000 : ℝ)^1549
        have hw : |(-2190425487/10000000000 : ℝ)|=(2190425487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138226031/250000000 : ℝ)|^2061 ≤ (45455493492579/100000000000000 : ℝ)^1549
        have hw : |(138226031/250000000 : ℝ)|=(138226031/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143195217/10000000000 : ℝ)|^2061 ≤ (1651372937827/4000000000000 : ℝ)^1549
        have hw : |(5143195217/10000000000 : ℝ)|=(5143195217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5377879151/10000000000 : ℝ)*x 0 + (-2391780037/10000000000 : ℝ)*x 1 + (2571597291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377879151/10000000000 : ℝ)^2061 ≤ (21904751936003/50000000000000 : ℝ)^1549 := by
    have hnat : (5377879151 : ℕ)^2061*50000000000000^1549 ≤ 21904751936003^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377879151 10000000000 21904751936003 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2391780037/10000000000 : ℝ)^2061 ≤ (7453089726319/50000000000000 : ℝ)^1549 := by
    have hnat : (2391780037 : ℕ)^2061*50000000000000^1549 ≤ 7453089726319^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391780037 10000000000 7453089726319 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2571597291/5000000000 : ℝ)^2061 ≤ (20642158331879/50000000000000 : ℝ)^1549 := by
    have hnat : (2571597291 : ℕ)^2061*50000000000000^1549 ≤ 20642158331879^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571597291 5000000000 20642158331879 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377879151/10000000000 : ℝ), (-2391780037/10000000000 : ℝ), (2571597291/5000000000 : ℝ)] ![(21904751936003/50000000000000 : ℝ), (7453089726319/50000000000000 : ℝ), (20642158331879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377879151/10000000000 : ℝ)|^2061 ≤ (21904751936003/50000000000000 : ℝ)^1549
        have hw : |(5377879151/10000000000 : ℝ)|=(5377879151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2391780037/10000000000 : ℝ)|^2061 ≤ (7453089726319/50000000000000 : ℝ)^1549
        have hw : |(-2391780037/10000000000 : ℝ)|=(2391780037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2571597291/5000000000 : ℝ)|^2061 ≤ (20642158331879/50000000000000 : ℝ)^1549
        have hw : |(2571597291/5000000000 : ℝ)|=(2571597291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5377879121/10000000000 : ℝ)*x 0 + (321449669/625000000 : ℝ)*x 1 + (-29897249/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377879121/10000000000 : ℝ)^2061 ≤ (1095237588671/2500000000000 : ℝ)^1549 := by
    have hnat : (5377879121 : ℕ)^2061*2500000000000^1549 ≤ 1095237588671^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377879121 10000000000 1095237588671 2500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321449669/625000000 : ℝ)^2061 ≤ (2064215898337/5000000000000 : ℝ)^1549 := by
    have hnat : (321449669 : ℕ)^2061*5000000000000^1549 ≤ 2064215898337^1549*625000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321449669 625000000 2064215898337 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29897249/125000000 : ℝ)^2061 ≤ (7453089241223/50000000000000 : ℝ)^1549 := by
    have hnat : (29897249 : ℕ)^2061*50000000000000^1549 ≤ 7453089241223^1549*125000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29897249 125000000 7453089241223 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377879121/10000000000 : ℝ), (321449669/625000000 : ℝ), (-29897249/125000000 : ℝ)] ![(1095237588671/2500000000000 : ℝ), (2064215898337/5000000000000 : ℝ), (7453089241223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377879121/10000000000 : ℝ)|^2061 ≤ (1095237588671/2500000000000 : ℝ)^1549
        have hw : |(5377879121/10000000000 : ℝ)|=(5377879121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321449669/625000000 : ℝ)|^2061 ≤ (2064215898337/5000000000000 : ℝ)^1549
        have hw : |(321449669/625000000 : ℝ)|=(321449669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29897249/125000000 : ℝ)|^2061 ≤ (7453089241223/50000000000000 : ℝ)^1549
        have hw : |(-29897249/125000000 : ℝ)|=(29897249/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1091189443/2500000000 : ℝ)*x 0 + (800850883/2000000000 : ℝ)*x 1 + (2379104623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091189443/2500000000 : ℝ)^2061 ≤ (33185936317807/100000000000000 : ℝ)^1549 := by
    have hnat : (1091189443 : ℕ)^2061*100000000000000^1549 ≤ 33185936317807^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091189443 2500000000 33185936317807 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (800850883/2000000000 : ℝ)^2061 ≤ (2958971834483/10000000000000 : ℝ)^1549 := by
    have hnat : (800850883 : ℕ)^2061*10000000000000^1549 ≤ 2958971834483^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800850883 2000000000 2958971834483 10000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2379104623/5000000000 : ℝ)^2061 ≤ (37224345316959/100000000000000 : ℝ)^1549 := by
    have hnat : (2379104623 : ℕ)^2061*100000000000000^1549 ≤ 37224345316959^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2379104623 5000000000 37224345316959 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091189443/2500000000 : ℝ), (800850883/2000000000 : ℝ), (2379104623/5000000000 : ℝ)] ![(33185936317807/100000000000000 : ℝ), (2958971834483/10000000000000 : ℝ), (37224345316959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091189443/2500000000 : ℝ)|^2061 ≤ (33185936317807/100000000000000 : ℝ)^1549
        have hw : |(1091189443/2500000000 : ℝ)|=(1091189443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(800850883/2000000000 : ℝ)|^2061 ≤ (2958971834483/10000000000000 : ℝ)^1549
        have hw : |(800850883/2000000000 : ℝ)|=(800850883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2379104623/5000000000 : ℝ)|^2061 ≤ (37224345316959/100000000000000 : ℝ)^1549
        have hw : |(2379104623/5000000000 : ℝ)|=(2379104623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190557043/10000000000 : ℝ)*x 0 + (2573015627/5000000000 : ℝ)*x 1 + (138154371/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190557043/10000000000 : ℝ)^2061 ≤ (1657655338349/12500000000000 : ℝ)^1549 := by
    have hnat : (2190557043 : ℕ)^2061*12500000000000^1549 ≤ 1657655338349^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190557043 10000000000 1657655338349 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2573015627/5000000000 : ℝ)^2061 ≤ (41314615602791/100000000000000 : ℝ)^1549 := by
    have hnat : (2573015627 : ℕ)^2061*100000000000000^1549 ≤ 41314615602791^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573015627 5000000000 41314615602791 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138154371/250000000 : ℝ)^2061 ≤ (2271207083831/5000000000000 : ℝ)^1549 := by
    have hnat : (138154371 : ℕ)^2061*5000000000000^1549 ≤ 2271207083831^1549*250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138154371 250000000 2271207083831 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190557043/10000000000 : ℝ), (2573015627/5000000000 : ℝ), (138154371/250000000 : ℝ)] ![(1657655338349/12500000000000 : ℝ), (41314615602791/100000000000000 : ℝ), (2271207083831/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190557043/10000000000 : ℝ)|^2061 ≤ (1657655338349/12500000000000 : ℝ)^1549
        have hw : |(-2190557043/10000000000 : ℝ)|=(2190557043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2573015627/5000000000 : ℝ)|^2061 ≤ (41314615602791/100000000000000 : ℝ)^1549
        have hw : |(2573015627/5000000000 : ℝ)|=(2573015627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138154371/250000000 : ℝ)|^2061 ≤ (2271207083831/5000000000000 : ℝ)^1549
        have hw : |(138154371/250000000 : ℝ)|=(138154371/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5280590911/10000000000 : ℝ)*x 0 + (-2008800039/10000000000 : ℝ)*x 1 + (5526174909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280590911/10000000000 : ℝ)^2061 ≤ (1710327005579/4000000000000 : ℝ)^1549 := by
    have hnat : (5280590911 : ℕ)^2061*4000000000000^1549 ≤ 1710327005579^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280590911 10000000000 1710327005579 4000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008800039/10000000000 : ℝ)^2061 ≤ (11817682415109/100000000000000 : ℝ)^1549 := by
    have hnat : (2008800039 : ℕ)^2061*100000000000000^1549 ≤ 11817682415109^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008800039 10000000000 11817682415109 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5526174909/10000000000 : ℝ)^2061 ≤ (5678017803907/12500000000000 : ℝ)^1549 := by
    have hnat : (5526174909 : ℕ)^2061*12500000000000^1549 ≤ 5678017803907^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526174909 10000000000 5678017803907 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280590911/10000000000 : ℝ), (-2008800039/10000000000 : ℝ), (5526174909/10000000000 : ℝ)] ![(1710327005579/4000000000000 : ℝ), (11817682415109/100000000000000 : ℝ), (5678017803907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280590911/10000000000 : ℝ)|^2061 ≤ (1710327005579/4000000000000 : ℝ)^1549
        have hw : |(5280590911/10000000000 : ℝ)|=(5280590911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2008800039/10000000000 : ℝ)|^2061 ≤ (11817682415109/100000000000000 : ℝ)^1549
        have hw : |(-2008800039/10000000000 : ℝ)|=(2008800039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5526174909/10000000000 : ℝ)|^2061 ≤ (5678017803907/12500000000000 : ℝ)^1549
        have hw : |(5526174909/10000000000 : ℝ)|=(5526174909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5280591143/10000000000 : ℝ)*x 0 + (5526174747/10000000000 : ℝ)*x 1 + (-1004399973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280591143/10000000000 : ℝ)^2061 ≤ (42758177638963/100000000000000 : ℝ)^1549 := by
    have hnat : (5280591143 : ℕ)^2061*100000000000000^1549 ≤ 42758177638963^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280591143 10000000000 42758177638963 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5526174747/10000000000 : ℝ)^2061 ≤ (45424140659501/100000000000000 : ℝ)^1549 := by
    have hnat : (5526174747 : ℕ)^2061*100000000000000^1549 ≤ 45424140659501^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526174747 10000000000 45424140659501 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004399973/5000000000 : ℝ)^2061 ≤ (11817681687153/100000000000000 : ℝ)^1549 := by
    have hnat : (1004399973 : ℕ)^2061*100000000000000^1549 ≤ 11817681687153^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004399973 5000000000 11817681687153 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280591143/10000000000 : ℝ), (5526174747/10000000000 : ℝ), (-1004399973/5000000000 : ℝ)] ![(42758177638963/100000000000000 : ℝ), (45424140659501/100000000000000 : ℝ), (11817681687153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280591143/10000000000 : ℝ)|^2061 ≤ (42758177638963/100000000000000 : ℝ)^1549
        have hw : |(5280591143/10000000000 : ℝ)|=(5280591143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5526174747/10000000000 : ℝ)|^2061 ≤ (45424140659501/100000000000000 : ℝ)^1549
        have hw : |(5526174747/10000000000 : ℝ)|=(5526174747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004399973/5000000000 : ℝ)|^2061 ≤ (11817681687153/100000000000000 : ℝ)^1549
        have hw : |(-1004399973/5000000000 : ℝ)|=(1004399973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s2_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2182507099/5000000000 : ℝ)*x 0 + (4752666719/10000000000 : ℝ)*x 1 + (4009855909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182507099/5000000000 : ℝ)^2061 ≤ (6637706083637/20000000000000 : ℝ)^1549 := by
    have hnat : (2182507099 : ℕ)^2061*20000000000000^1549 ≤ 6637706083637^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182507099 5000000000 6637706083637 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4752666719/10000000000 : ℝ)^2061 ≤ (18583332058439/50000000000000 : ℝ)^1549 := by
    have hnat : (4752666719 : ℕ)^2061*50000000000000^1549 ≤ 18583332058439^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752666719 10000000000 18583332058439 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4009855909/10000000000 : ℝ)^2061 ≤ (14822402726811/50000000000000 : ℝ)^1549 := by
    have hnat : (4009855909 : ℕ)^2061*50000000000000^1549 ≤ 14822402726811^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009855909 10000000000 14822402726811 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182507099/5000000000 : ℝ), (4752666719/10000000000 : ℝ), (4009855909/10000000000 : ℝ)] ![(6637706083637/20000000000000 : ℝ), (18583332058439/50000000000000 : ℝ), (14822402726811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182507099/5000000000 : ℝ)|^2061 ≤ (6637706083637/20000000000000 : ℝ)^1549
        have hw : |(2182507099/5000000000 : ℝ)|=(2182507099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4752666719/10000000000 : ℝ)|^2061 ≤ (18583332058439/50000000000000 : ℝ)^1549
        have hw : |(4752666719/10000000000 : ℝ)|=(4752666719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4009855909/10000000000 : ℝ)|^2061 ≤ (14822402726811/50000000000000 : ℝ)^1549
        have hw : |(4009855909/10000000000 : ℝ)|=(4009855909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8637/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16791/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20863/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1281/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20863/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1281/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20863/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1281/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20863/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1281/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20863/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1281/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20863/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1281/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1281/25000 : ℝ) ^ (8243/2048 : ℝ) ≤ (640180921173199/100000000000000000000 : ℝ) := by
    have hpowers : (1281/25000 : ℝ)^8243 ≤ (640180921173199/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1281 : ℕ)^8243*100000000000000000000^2048 ≤ 640180921173199^2048*25000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1281 25000 640180921173199 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1281/25000 : ℝ)) (X := (640180921173199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20863/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (182204004744731261/100000000000000000000 : ℝ) := by
    have hpowers : (20863/100000 : ℝ)^8243 ≤ (182204004744731261/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20863 : ℕ)^8243*100000000000000000000^2048 ≤ 182204004744731261^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20863 100000 182204004744731261 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20863/100000 : ℝ)) (X := (182204004744731261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000640180921173199/50000000000000000000 : ℝ) ≤ (10000031810850871/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50000640180921173199/50000000000000000000 : ℝ)^2048 ≤ (10000031810850871/10000000000000000 : ℝ)^8243 := by
      have hnat : (50000640180921173199 : ℕ)^2048*10000000000000000^8243 ≤ 10000031810850871^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000640180921173199 50000000000000000000 10000031810850871 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031810850871/10000000000000000 : ℝ)) (X := (50000640180921173199/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5009142209283295223/5000000000000000000 : ℝ) ≤ (1250567463119169/1250000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (5009142209283295223/5000000000000000000 : ℝ)^2048 ≤ (1250567463119169/1250000000000000 : ℝ)^8243 := by
      have hnat : (5009142209283295223 : ℕ)^2048*1250000000000000^8243 ≤ 1250567463119169^8243*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5009142209283295223 5000000000000000000 1250567463119169 1250000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250567463119169/1250000000000000 : ℝ)) (X := (5009142209283295223/5000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50182204004744731261/50000000000000000000 : ℝ) ≤ (10009047599055833/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50182204004744731261/50000000000000000000 : ℝ)^2048 ≤ (10009047599055833/10000000000000000 : ℝ)^8243 := by
      have hnat : (50182204004744731261 : ℕ)^2048*10000000000000000^8243 ≤ 10009047599055833^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50182204004744731261 50000000000000000000 10009047599055833 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009047599055833/10000000000000000 : ℝ)) (X := (50182204004744731261/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(640180921173199/100000000000000000000 : ℝ) ≤ ((157344303772219633381/157390000000000000000 : ℝ)+2*(4507894102481/1573900000000000 : ℝ)*(1281/25000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (157344303772219633381/157390000000000000000 : ℝ)+2*(4507894102481/1573900000000000 : ℝ)*(1281/25000 : ℝ)=(10000031810850871/10000000000000000 : ℝ) by norm_num, show 1+2*(640180921173199/100000000000000000000 : ℝ)=(50000640180921173199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(182204004744731261/100000000000000000000 : ℝ)+(640180921173199/100000000000000000000 : ℝ) ≤ ((157344303772219633381/157390000000000000000 : ℝ)+(4507894102481/1573900000000000 : ℝ)*((20863/100000 : ℝ)+(1281/25000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (157344303772219633381/157390000000000000000 : ℝ)+(4507894102481/1573900000000000 : ℝ)*((20863/100000 : ℝ)+(1281/25000 : ℝ))=(1250567463119169/1250000000000000 : ℝ) by norm_num, show 1+(182204004744731261/100000000000000000000 : ℝ)+(640180921173199/100000000000000000000 : ℝ)=(5009142209283295223/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(182204004744731261/100000000000000000000 : ℝ) ≤ ((157344303772219633381/157390000000000000000 : ℝ)+2*(4507894102481/1573900000000000 : ℝ)*(20863/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (157344303772219633381/157390000000000000000 : ℝ)+2*(4507894102481/1573900000000000 : ℝ)*(20863/100000 : ℝ)=(10009047599055833/10000000000000000 : ℝ) by norm_num, show 1+2*(182204004744731261/100000000000000000000 : ℝ)=(50182204004744731261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (157344303772219633381/157390000000000000000 : ℝ)*(X 1 0+X 2 0)+(4507894102481/1573900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (1281/25000 : ℝ)) (hi := (20863/100000 : ℝ)) (c := (157344303772219633381/157390000000000000000 : ℝ)) (alpha := (4507894102481/1573900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (157344303772219633381/157390000000000000000 : ℝ)*(X 0 1+X 2 1)+(4507894102481/1573900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (1281/25000 : ℝ)) (hi := (20863/100000 : ℝ)) (c := (157344303772219633381/157390000000000000000 : ℝ)) (alpha := (4507894102481/1573900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (157344303772219633381/157390000000000000000 : ℝ)*(X 0 2+X 1 2)+(4507894102481/1573900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (1281/25000 : ℝ)) (hi := (20863/100000 : ℝ)) (c := (157344303772219633381/157390000000000000000 : ℝ)) (alpha := (4507894102481/1573900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190425487/10000000000 : ℝ)*X 0 0+(138226031/250000000 : ℝ)*X 0 1+(5143195217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377879151/10000000000 : ℝ)*X 1 0+(-2391780037/10000000000 : ℝ)*X 1 1+(2571597291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377879121/10000000000 : ℝ)*X 2 0+(321449669/625000000 : ℝ)*X 2 1+(-29897249/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091189443/2500000000 : ℝ)*X 0 0+(800850883/2000000000 : ℝ)*X 0 1+(2379104623/5000000000 : ℝ)*X 0 2+(1091189443/2500000000 : ℝ)*X 1 0+(800850883/2000000000 : ℝ)*X 1 1+(2379104623/5000000000 : ℝ)*X 1 2+(1091189443/2500000000 : ℝ)*X 2 0+(800850883/2000000000 : ℝ)*X 2 1+(2379104623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2190557043/10000000000 : ℝ)*X 0 0+(2573015627/5000000000 : ℝ)*X 0 1+(138154371/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280590911/10000000000 : ℝ)*X 1 0+(-2008800039/10000000000 : ℝ)*X 1 1+(5526174909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5280591143/10000000000 : ℝ)*X 2 0+(5526174747/10000000000 : ℝ)*X 2 1+(-1004399973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182507099/5000000000 : ℝ)*X 0 0+(4752666719/10000000000 : ℝ)*X 0 1+(4009855909/10000000000 : ℝ)*X 0 2+(2182507099/5000000000 : ℝ)*X 1 0+(4752666719/10000000000 : ℝ)*X 1 1+(4009855909/10000000000 : ℝ)*X 1 2+(2182507099/5000000000 : ℝ)*X 2 0+(4752666719/10000000000 : ℝ)*X 2 1+(4009855909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37009472851770126041300565441/3934750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41390707/20000000000000 : ℝ)*(base1) + (1913883563/100000000000000 : ℝ)*(base19) + (1899425829/100000000000000 : ℝ)*(base23) + (134919837/100000000000000 : ℝ)*(upper3) + (49987389/25000000000000 : ℝ)*(upper5) + (1959044527271087/100000000000000 : ℝ)*(major0) + (1959044527271087/100000000000000 : ℝ)*(major1) + (1959044527271087/100000000000000 : ℝ)*(major2) + (518343967956673/20000000000000 : ℝ)*(sp0) + (161983211919651/6250000000000 : ℝ)*(sp1) + (51834628103443/2000000000000 : ℝ)*(sp2) + (1326347512001853/100000000000000 : ℝ)*(sp3) + (273435363/2000000000000 : ℝ)*(sp4) + (7717462123/100000000000000 : ℝ)*(sp7) + (1326355436417511/100000000000000 : ℝ)*(f.failure) + (2591733304597979/100000000000000 : ℝ)*(f.sum) + (6825786940041/9836875000000000000000000000 : ℝ)*base66 + (114692078463321944853/15739000000000000000000000000000000 : ℝ)*base68 + (224950552533923944853/15739000000000000000000000000000000 : ℝ)*base70 + (15380265643272055147/15739000000000000000000000000000000 : ℝ)*base71 + (451979245770953/78695000000000000000000000000 : ℝ)*base74 + (90429050507196944853/15739000000000000000000000000000000 : ℝ)*base76 + (49057393334553944853/15739000000000000000000000000000000 : ℝ)*base78 + (35927211468421944853/15739000000000000000000000000000000 : ℝ)*base80 + (145732671274107/19673750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (55067053/10000000000000000000000 : ℝ)*base89 + (55067053/10000000000000000000000 : ℝ)*base91 + (55067053/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14607098549768163234361290081/1967375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (714797677/50000000000000 : ℝ)*(base19) + (1648315191/100000000000000 : ℝ)*(base23) + (190693963/100000000000000 : ℝ)*(upper3) + (18154317/50000000000000 : ℝ)*(lower4) + (20489311/12500000000000 : ℝ)*(upper5) + (497102882761433/25000000000000 : ℝ)*(major0) + (497102882761433/25000000000000 : ℝ)*(major1) + (497102882761433/25000000000000 : ℝ)*(major2) + (6097350109/50000000000000 : ℝ)*(sp1) + (7030618427/50000000000000 : ℝ)*(sp2) + (263058468304189/10000000000000 : ℝ)*(sp4) + (2630571058746319/100000000000000 : ℝ)*(sp5) + (526113794697969/20000000000000 : ℝ)*(sp6) + (673119065780383/50000000000000 : ℝ)*(sp7) + (673119065780383/50000000000000 : ℝ)*(f.failure) + (263058468304189/10000000000000 : ℝ)*(f.sum) + (202290461669759/39347500000000000000000000000 : ℝ)*base66 + (9520879936213005027/3934750000000000000000000000000000 : ℝ)*base68 + (25694199713256994973/3934750000000000000000000000000000 : ℝ)*base69 + (5249867700352755027/3934750000000000000000000000000000 : ℝ)*base72 + (396543633716573/78695000000000000000000000000 : ℝ)*base74 + (1292134426623744973/3934750000000000000000000000000000 : ℝ)*base75 + (11959522240037744973/3934750000000000000000000000000000 : ℝ)*base77 + (16640740162744744973/3934750000000000000000000000000000 : ℝ)*base79 + (23964122623689/9836875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3453291/5000000000000000000000 : ℝ)*base90 + (3453291/5000000000000000000000 : ℝ)*base92 + (3453291/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1051_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1281/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1051_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1051_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1051_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1051_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8637/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16791/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1166_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:42:33.808655+00:00
-- url     : https://prove2.me/submissions/f89aa37c-7cb9-4e0b-b0d9-ad2bb9522537

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
theorem support_rectangle_w1166_box_0 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-507339833/2500000000 : ℝ)*x 0 + (2687982061/5000000000 : ℝ)*x 1 + (2687982203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (507339833/2500000000 : ℝ)^8359 ≤ (6047252497031/50000000000000 : ℝ)^6311 := by
    have hnat : (507339833 : ℕ)^8359*50000000000000^6311 ≤ 6047252497031^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507339833 2500000000 6047252497031 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687982061/5000000000 : ℝ)^8359 ≤ (43952745953967/100000000000000 : ℝ)^6311 := by
    have hnat : (2687982061 : ℕ)^8359*100000000000000^6311 ≤ 43952745953967^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687982061 5000000000 43952745953967 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687982203/5000000000 : ℝ)^8359 ≤ (8790549805877/20000000000000 : ℝ)^6311 := by
    have hnat : (2687982203 : ℕ)^8359*20000000000000^6311 ≤ 8790549805877^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687982203 5000000000 8790549805877 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-507339833/2500000000 : ℝ), (2687982061/5000000000 : ℝ), (2687982203/5000000000 : ℝ)] ![(6047252497031/50000000000000 : ℝ), (43952745953967/100000000000000 : ℝ), (8790549805877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-507339833/2500000000 : ℝ)|^8359 ≤ (6047252497031/50000000000000 : ℝ)^6311
        have hw : |(-507339833/2500000000 : ℝ)|=(507339833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687982061/5000000000 : ℝ)|^8359 ≤ (43952745953967/100000000000000 : ℝ)^6311
        have hw : |(2687982061/5000000000 : ℝ)|=(2687982061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687982203/5000000000 : ℝ)|^8359 ≤ (8790549805877/20000000000000 : ℝ)^6311
        have hw : |(2687982203/5000000000 : ℝ)|=(2687982203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_1 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296202107/10000000000 : ℝ)*x 0 + (-534397619/2500000000 : ℝ)*x 1 + (5375963643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296202107/10000000000 : ℝ)^8359 ≤ (43091094499927/100000000000000 : ℝ)^6311 := by
    have hnat : (5296202107 : ℕ)^8359*100000000000000^6311 ≤ 43091094499927^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296202107 10000000000 43091094499927 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534397619/2500000000 : ℝ)^8359 ≤ (6478082359309/50000000000000 : ℝ)^6311 := by
    have hnat : (534397619 : ℕ)^8359*50000000000000^6311 ≤ 6478082359309^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534397619 2500000000 6478082359309 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375963643/10000000000 : ℝ)^8359 ≤ (21976370383453/50000000000000 : ℝ)^6311 := by
    have hnat : (5375963643 : ℕ)^8359*50000000000000^6311 ≤ 21976370383453^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375963643 10000000000 21976370383453 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296202107/10000000000 : ℝ), (-534397619/2500000000 : ℝ), (5375963643/10000000000 : ℝ)] ![(43091094499927/100000000000000 : ℝ), (6478082359309/50000000000000 : ℝ), (21976370383453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296202107/10000000000 : ℝ)|^8359 ≤ (43091094499927/100000000000000 : ℝ)^6311
        have hw : |(5296202107/10000000000 : ℝ)|=(5296202107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534397619/2500000000 : ℝ)|^8359 ≤ (6478082359309/50000000000000 : ℝ)^6311
        have hw : |(-534397619/2500000000 : ℝ)|=(534397619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375963643/10000000000 : ℝ)|^8359 ≤ (21976370383453/50000000000000 : ℝ)^6311
        have hw : |(5375963643/10000000000 : ℝ)|=(5375963643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_2 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648100857/5000000000 : ℝ)*x 0 + (2687982099/5000000000 : ℝ)*x 1 + (-427518051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648100857/5000000000 : ℝ)^8359 ≤ (43091090264749/100000000000000 : ℝ)^6311 := by
    have hnat : (2648100857 : ℕ)^8359*100000000000000^6311 ≤ 43091090264749^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648100857 5000000000 43091090264749 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687982099/5000000000 : ℝ)^8359 ≤ (21976373388483/50000000000000 : ℝ)^6311 := by
    have hnat : (2687982099 : ℕ)^8359*50000000000000^6311 ≤ 21976373388483^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687982099 5000000000 21976373388483 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427518051/2000000000 : ℝ)^8359 ≤ (12956162944427/100000000000000 : ℝ)^6311 := by
    have hnat : (427518051 : ℕ)^8359*100000000000000^6311 ≤ 12956162944427^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427518051 2000000000 12956162944427 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648100857/5000000000 : ℝ), (2687982099/5000000000 : ℝ), (-427518051/2000000000 : ℝ)] ![(43091090264749/100000000000000 : ℝ), (21976373388483/50000000000000 : ℝ), (12956162944427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648100857/5000000000 : ℝ)|^8359 ≤ (43091090264749/100000000000000 : ℝ)^6311
        have hw : |(2648100857/5000000000 : ℝ)|=(2648100857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687982099/5000000000 : ℝ)|^8359 ≤ (21976373388483/50000000000000 : ℝ)^6311
        have hw : |(2687982099/5000000000 : ℝ)|=(2687982099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-427518051/2000000000 : ℝ)|^8359 ≤ (12956162944427/100000000000000 : ℝ)^6311
        have hw : |(-427518051/2000000000 : ℝ)|=(427518051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_3 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4468593133/10000000000 : ℝ)*x 0 + (538718991/1250000000 : ℝ)*x 1 + (4309754033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468593133/10000000000 : ℝ)^8359 ≤ (8601749468437/25000000000000 : ℝ)^6311 := by
    have hnat : (4468593133 : ℕ)^8359*25000000000000^6311 ≤ 8601749468437^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468593133 10000000000 8601749468437 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538718991/1250000000 : ℝ)^8359 ≤ (32796490447033/100000000000000 : ℝ)^6311 := by
    have hnat : (538718991 : ℕ)^8359*100000000000000^6311 ≤ 32796490447033^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538718991 1250000000 32796490447033 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4309754033/10000000000 : ℝ)^8359 ≤ (32796511664003/100000000000000 : ℝ)^6311 := by
    have hnat : (4309754033 : ℕ)^8359*100000000000000^6311 ≤ 32796511664003^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309754033 10000000000 32796511664003 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468593133/10000000000 : ℝ), (538718991/1250000000 : ℝ), (4309754033/10000000000 : ℝ)] ![(8601749468437/25000000000000 : ℝ), (32796490447033/100000000000000 : ℝ), (32796511664003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468593133/10000000000 : ℝ)|^8359 ≤ (8601749468437/25000000000000 : ℝ)^6311
        have hw : |(4468593133/10000000000 : ℝ)|=(4468593133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538718991/1250000000 : ℝ)|^8359 ≤ (32796490447033/100000000000000 : ℝ)^6311
        have hw : |(538718991/1250000000 : ℝ)|=(538718991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4309754033/10000000000 : ℝ)|^8359 ≤ (32796511664003/100000000000000 : ℝ)^6311
        have hw : |(4309754033/10000000000 : ℝ)|=(4309754033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_4 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-570738433/2500000000 : ℝ)*x 0 + (5281440517/10000000000 : ℝ)*x 1 + (2640720119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (570738433/2500000000 : ℝ)^8359 ≤ (14135827580861/100000000000000 : ℝ)^6311 := by
    have hnat : (570738433 : ℕ)^8359*100000000000000^6311 ≤ 14135827580861^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570738433 2500000000 14135827580861 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281440517/10000000000 : ℝ)^8359 ≤ (670813870381/1562500000000 : ℝ)^6311 := by
    have hnat : (5281440517 : ℕ)^8359*1562500000000^6311 ≤ 670813870381^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281440517 10000000000 670813870381 1562500000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2640720119/5000000000 : ℝ)^8359 ≤ (42932084700453/100000000000000 : ℝ)^6311 := by
    have hnat : (2640720119 : ℕ)^8359*100000000000000^6311 ≤ 42932084700453^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640720119 5000000000 42932084700453 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-570738433/2500000000 : ℝ), (5281440517/10000000000 : ℝ), (2640720119/5000000000 : ℝ)] ![(14135827580861/100000000000000 : ℝ), (670813870381/1562500000000 : ℝ), (42932084700453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-570738433/2500000000 : ℝ)|^8359 ≤ (14135827580861/100000000000000 : ℝ)^6311
        have hw : |(-570738433/2500000000 : ℝ)|=(570738433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281440517/10000000000 : ℝ)|^8359 ≤ (670813870381/1562500000000 : ℝ)^6311
        have hw : |(5281440517/10000000000 : ℝ)|=(5281440517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2640720119/5000000000 : ℝ)|^8359 ≤ (42932084700453/100000000000000 : ℝ)^6311
        have hw : |(2640720119/5000000000 : ℝ)|=(2640720119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_5 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072589453/2000000000 : ℝ)*x 0 + (-2174843507/10000000000 : ℝ)*x 1 + (5281440023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072589453/2000000000 : ℝ)^8359 ≤ (10952960662151/25000000000000 : ℝ)^6311 := by
    have hnat : (1072589453 : ℕ)^8359*25000000000000^6311 ≤ 10952960662151^6311*2000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072589453 2000000000 10952960662151 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2174843507/10000000000 : ℝ)^8359 ≤ (3314018737229/25000000000000 : ℝ)^6311 := by
    have hnat : (2174843507 : ℕ)^8359*25000000000000^6311 ≤ 3314018737229^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174843507 10000000000 3314018737229 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281440023/10000000000 : ℝ)^8359 ≤ (10733020596399/25000000000000 : ℝ)^6311 := by
    have hnat : (5281440023 : ℕ)^8359*25000000000000^6311 ≤ 10733020596399^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281440023 10000000000 10733020596399 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072589453/2000000000 : ℝ), (-2174843507/10000000000 : ℝ), (5281440023/10000000000 : ℝ)] ![(10952960662151/25000000000000 : ℝ), (3314018737229/25000000000000 : ℝ), (10733020596399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072589453/2000000000 : ℝ)|^8359 ≤ (10952960662151/25000000000000 : ℝ)^6311
        have hw : |(1072589453/2000000000 : ℝ)|=(1072589453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2174843507/10000000000 : ℝ)|^8359 ≤ (3314018737229/25000000000000 : ℝ)^6311
        have hw : |(-2174843507/10000000000 : ℝ)|=(2174843507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281440023/10000000000 : ℝ)|^8359 ≤ (10733020596399/25000000000000 : ℝ)^6311
        have hw : |(5281440023/10000000000 : ℝ)|=(5281440023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_6 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681473311/5000000000 : ℝ)*x 0 + (5281440231/10000000000 : ℝ)*x 1 + (-2174844093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681473311/5000000000 : ℝ)^8359 ≤ (21905917845537/50000000000000 : ℝ)^6311 := by
    have hnat : (2681473311 : ℕ)^8359*50000000000000^6311 ≤ 21905917845537^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681473311 5000000000 21905917845537 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281440231/10000000000 : ℝ)^8359 ≤ (21466042312543/50000000000000 : ℝ)^6311 := by
    have hnat : (5281440231 : ℕ)^8359*50000000000000^6311 ≤ 21466042312543^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281440231 10000000000 21466042312543 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2174844093/10000000000 : ℝ)^8359 ≤ (13256079679783/100000000000000 : ℝ)^6311 := by
    have hnat : (2174844093 : ℕ)^8359*100000000000000^6311 ≤ 13256079679783^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174844093 10000000000 13256079679783 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681473311/5000000000 : ℝ), (5281440231/10000000000 : ℝ), (-2174844093/10000000000 : ℝ)] ![(21905917845537/50000000000000 : ℝ), (21466042312543/50000000000000 : ℝ), (13256079679783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681473311/5000000000 : ℝ)|^8359 ≤ (21905917845537/50000000000000 : ℝ)^6311
        have hw : |(2681473311/5000000000 : ℝ)|=(2681473311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281440231/10000000000 : ℝ)|^8359 ≤ (21466042312543/50000000000000 : ℝ)^6311
        have hw : |(5281440231/10000000000 : ℝ)|=(5281440231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2174844093/10000000000 : ℝ)|^8359 ≤ (13256079679783/100000000000000 : ℝ)^6311
        have hw : |(-2174844093/10000000000 : ℝ)|=(2174844093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_7 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2126822621/5000000000 : ℝ)*x 0 + (552150737/1250000000 : ℝ)*x 1 + (4417206637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126822621/5000000000 : ℝ)^8359 ≤ (32232171276373/100000000000000 : ℝ)^6311 := by
    have hnat : (2126822621 : ℕ)^8359*100000000000000^6311 ≤ 32232171276373^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126822621 5000000000 32232171276373 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552150737/1250000000 : ℝ)^8359 ≤ (6776782117729/20000000000000 : ℝ)^6311 := by
    have hnat : (552150737 : ℕ)^8359*20000000000000^6311 ≤ 6776782117729^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552150737 1250000000 6776782117729 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417206637/10000000000 : ℝ)^8359 ≤ (677678362347/2000000000000 : ℝ)^6311 := by
    have hnat : (4417206637 : ℕ)^8359*2000000000000^6311 ≤ 677678362347^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417206637 10000000000 677678362347 2000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126822621/5000000000 : ℝ), (552150737/1250000000 : ℝ), (4417206637/10000000000 : ℝ)] ![(32232171276373/100000000000000 : ℝ), (6776782117729/20000000000000 : ℝ), (677678362347/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126822621/5000000000 : ℝ)|^8359 ≤ (32232171276373/100000000000000 : ℝ)^6311
        have hw : |(2126822621/5000000000 : ℝ)|=(2126822621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552150737/1250000000 : ℝ)|^8359 ≤ (6776782117729/20000000000000 : ℝ)^6311
        have hw : |(552150737/1250000000 : ℝ)|=(552150737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417206637/10000000000 : ℝ)|^8359 ≤ (677678362347/2000000000000 : ℝ)^6311
        have hw : |(4417206637/10000000000 : ℝ)|=(4417206637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_8 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2229896133/10000000000 : ℝ)*x 0 + (2608554519/5000000000 : ℝ)*x 1 + (1346393573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2229896133/10000000000 : ℝ)^8359 ≤ (13702338286723/100000000000000 : ℝ)^6311 := by
    have hnat : (2229896133 : ℕ)^8359*100000000000000^6311 ≤ 13702338286723^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229896133 10000000000 13702338286723 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608554519/5000000000 : ℝ)^8359 ≤ (42240817655751/100000000000000 : ℝ)^6311 := by
    have hnat : (2608554519 : ℕ)^8359*100000000000000^6311 ≤ 42240817655751^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608554519 5000000000 42240817655751 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346393573/2500000000 : ℝ)^8359 ≤ (44056844045073/100000000000000 : ℝ)^6311 := by
    have hnat : (1346393573 : ℕ)^8359*100000000000000^6311 ≤ 44056844045073^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346393573 2500000000 44056844045073 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2229896133/10000000000 : ℝ), (2608554519/5000000000 : ℝ), (1346393573/2500000000 : ℝ)] ![(13702338286723/100000000000000 : ℝ), (42240817655751/100000000000000 : ℝ), (44056844045073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2229896133/10000000000 : ℝ)|^8359 ≤ (13702338286723/100000000000000 : ℝ)^6311
        have hw : |(-2229896133/10000000000 : ℝ)|=(2229896133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608554519/5000000000 : ℝ)|^8359 ≤ (42240817655751/100000000000000 : ℝ)^6311
        have hw : |(2608554519/5000000000 : ℝ)|=(2608554519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346393573/2500000000 : ℝ)|^8359 ≤ (44056844045073/100000000000000 : ℝ)^6311
        have hw : |(1346393573/2500000000 : ℝ)|=(1346393573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_9 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322353157/2500000000 : ℝ)*x 0 + (-2133734299/10000000000 : ℝ)*x 1 + (673196751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322353157/2500000000 : ℝ)^8359 ≤ (43017942669279/100000000000000 : ℝ)^6311 := by
    have hnat : (1322353157 : ℕ)^8359*100000000000000^6311 ≤ 43017942669279^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322353157 2500000000 43017942669279 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133734299/10000000000 : ℝ)^8359 ≤ (12925216342349/100000000000000 : ℝ)^6311 := by
    have hnat : (2133734299 : ℕ)^8359*100000000000000^6311 ≤ 12925216342349^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133734299 10000000000 12925216342349 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673196751/1250000000 : ℝ)^8359 ≤ (688388140123/1562500000000 : ℝ)^6311 := by
    have hnat : (673196751 : ℕ)^8359*1562500000000^6311 ≤ 688388140123^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673196751 1250000000 688388140123 1562500000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322353157/2500000000 : ℝ), (-2133734299/10000000000 : ℝ), (673196751/1250000000 : ℝ)] ![(43017942669279/100000000000000 : ℝ), (12925216342349/100000000000000 : ℝ), (688388140123/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322353157/2500000000 : ℝ)|^8359 ≤ (43017942669279/100000000000000 : ℝ)^6311
        have hw : |(1322353157/2500000000 : ℝ)|=(1322353157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2133734299/10000000000 : ℝ)|^8359 ≤ (12925216342349/100000000000000 : ℝ)^6311
        have hw : |(-2133734299/10000000000 : ℝ)|=(2133734299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673196751/1250000000 : ℝ)|^8359 ≤ (688388140123/1562500000000 : ℝ)^6311
        have hw : |(673196751/1250000000 : ℝ)|=(673196751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_10 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289412487/10000000000 : ℝ)*x 0 + (269278697/500000000 : ℝ)*x 1 + (-2133734581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289412487/10000000000 : ℝ)^8359 ≤ (2150897057521/5000000000000 : ℝ)^6311 := by
    have hnat : (5289412487 : ℕ)^8359*5000000000000^6311 ≤ 2150897057521^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289412487 10000000000 2150897057521 5000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269278697/500000000 : ℝ)^8359 ≤ (22028420115539/50000000000000 : ℝ)^6311 := by
    have hnat : (269278697 : ℕ)^8359*50000000000000^6311 ≤ 22028420115539^6311*500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269278697 500000000 22028420115539 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133734581/10000000000 : ℝ)^8359 ≤ (12925218604923/100000000000000 : ℝ)^6311 := by
    have hnat : (2133734581 : ℕ)^8359*100000000000000^6311 ≤ 12925218604923^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133734581 10000000000 12925218604923 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289412487/10000000000 : ℝ), (269278697/500000000 : ℝ), (-2133734581/10000000000 : ℝ)] ![(2150897057521/5000000000000 : ℝ), (22028420115539/50000000000000 : ℝ), (12925218604923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289412487/10000000000 : ℝ)|^8359 ≤ (2150897057521/5000000000000 : ℝ)^6311
        have hw : |(5289412487/10000000000 : ℝ)|=(5289412487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269278697/500000000 : ℝ)|^8359 ≤ (22028420115539/50000000000000 : ℝ)^6311
        have hw : |(269278697/500000000 : ℝ)|=(269278697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133734581/10000000000 : ℝ)|^8359 ≤ (12925218604923/100000000000000 : ℝ)^6311
        have hw : |(-2133734581/10000000000 : ℝ)|=(2133734581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_11 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4490175317/10000000000 : ℝ)*x 0 + (1074705323/2500000000 : ℝ)*x 1 + (134338169/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490175317/10000000000 : ℝ)^8359 ≤ (17313636976691/50000000000000 : ℝ)^6311 := by
    have hnat : (4490175317 : ℕ)^8359*50000000000000^6311 ≤ 17313636976691^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490175317 10000000000 17313636976691 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074705323/2500000000 : ℝ)^8359 ≤ (6537272486201/20000000000000 : ℝ)^6311 := by
    have hnat : (1074705323 : ℕ)^8359*20000000000000^6311 ≤ 6537272486201^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074705323 2500000000 6537272486201 20000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134338169/312500000 : ℝ)^8359 ≤ (32686363599243/100000000000000 : ℝ)^6311 := by
    have hnat : (134338169 : ℕ)^8359*100000000000000^6311 ≤ 32686363599243^6311*312500000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134338169 312500000 32686363599243 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490175317/10000000000 : ℝ), (1074705323/2500000000 : ℝ), (134338169/312500000 : ℝ)] ![(17313636976691/50000000000000 : ℝ), (6537272486201/20000000000000 : ℝ), (32686363599243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490175317/10000000000 : ℝ)|^8359 ≤ (17313636976691/50000000000000 : ℝ)^6311
        have hw : |(4490175317/10000000000 : ℝ)|=(4490175317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074705323/2500000000 : ℝ)|^8359 ≤ (6537272486201/20000000000000 : ℝ)^6311
        have hw : |(1074705323/2500000000 : ℝ)|=(1074705323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134338169/312500000 : ℝ)|^8359 ≤ (32686363599243/100000000000000 : ℝ)^6311
        have hw : |(134338169/312500000 : ℝ)|=(134338169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_12 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082722259/10000000000 : ℝ)*x 0 + (543903467/1000000000 : ℝ)*x 1 + (5273391131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082722259/10000000000 : ℝ)^8359 ≤ (12517527183681/100000000000000 : ℝ)^6311 := by
    have hnat : (2082722259 : ℕ)^8359*100000000000000^6311 ≤ 12517527183681^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082722259 10000000000 12517527183681 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543903467/1000000000 : ℝ)^8359 ≤ (44637029601603/100000000000000 : ℝ)^6311 := by
    have hnat : (543903467 : ℕ)^8359*100000000000000^6311 ≤ 44637029601603^6311*1000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543903467 1000000000 44637029601603 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273391131/10000000000 : ℝ)^8359 ≤ (10711360797803/25000000000000 : ℝ)^6311 := by
    have hnat : (5273391131 : ℕ)^8359*25000000000000^6311 ≤ 10711360797803^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273391131 10000000000 10711360797803 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082722259/10000000000 : ℝ), (543903467/1000000000 : ℝ), (5273391131/10000000000 : ℝ)] ![(12517527183681/100000000000000 : ℝ), (44637029601603/100000000000000 : ℝ), (10711360797803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082722259/10000000000 : ℝ)|^8359 ≤ (12517527183681/100000000000000 : ℝ)^6311
        have hw : |(-2082722259/10000000000 : ℝ)|=(2082722259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543903467/1000000000 : ℝ)|^8359 ≤ (44637029601603/100000000000000 : ℝ)^6311
        have hw : |(543903467/1000000000 : ℝ)|=(543903467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273391131/10000000000 : ℝ)|^8359 ≤ (10711360797803/25000000000000 : ℝ)^6311
        have hw : |(5273391131/10000000000 : ℝ)|=(5273391131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_13 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368627971/10000000000 : ℝ)*x 0 + (-1088979849/5000000000 : ℝ)*x 1 + (1318347729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368627971/10000000000 : ℝ)^8359 ≤ (21936660419047/50000000000000 : ℝ)^6311 := by
    have hnat : (5368627971 : ℕ)^8359*50000000000000^6311 ≤ 21936660419047^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368627971 10000000000 21936660419047 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088979849/5000000000 : ℝ)^8359 ≤ (13281238276759/100000000000000 : ℝ)^6311 := by
    have hnat : (1088979849 : ℕ)^8359*100000000000000^6311 ≤ 13281238276759^6311*5000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088979849 5000000000 13281238276759 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318347729/2500000000 : ℝ)^8359 ≤ (17138176351/40000000000 : ℝ)^6311 := by
    have hnat : (1318347729 : ℕ)^8359*40000000000^6311 ≤ 17138176351^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318347729 2500000000 17138176351 40000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368627971/10000000000 : ℝ), (-1088979849/5000000000 : ℝ), (1318347729/2500000000 : ℝ)] ![(21936660419047/50000000000000 : ℝ), (13281238276759/100000000000000 : ℝ), (17138176351/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368627971/10000000000 : ℝ)|^8359 ≤ (21936660419047/50000000000000 : ℝ)^6311
        have hw : |(5368627971/10000000000 : ℝ)|=(5368627971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1088979849/5000000000 : ℝ)|^8359 ≤ (13281238276759/100000000000000 : ℝ)^6311
        have hw : |(-1088979849/5000000000 : ℝ)|=(1088979849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318347729/2500000000 : ℝ)|^8359 ≤ (17138176351/40000000000 : ℝ)^6311
        have hw : |(1318347729/2500000000 : ℝ)|=(1318347729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_14 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1342157013/2500000000 : ℝ)*x 0 + (659173931/1250000000 : ℝ)*x 1 + (-13612243/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342157013/2500000000 : ℝ)^8359 ≤ (43873321714849/100000000000000 : ℝ)^6311 := by
    have hnat : (1342157013 : ℕ)^8359*100000000000000^6311 ≤ 43873321714849^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342157013 2500000000 43873321714849 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (659173931/1250000000 : ℝ)^8359 ≤ (1338920206331/3125000000000 : ℝ)^6311 := by
    have hnat : (659173931 : ℕ)^8359*3125000000000^6311 ≤ 1338920206331^6311*1250000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659173931 1250000000 1338920206331 3125000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13612243/62500000 : ℝ)^8359 ≤ (13281231669853/100000000000000 : ℝ)^6311 := by
    have hnat : (13612243 : ℕ)^8359*100000000000000^6311 ≤ 13281231669853^6311*62500000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13612243 62500000 13281231669853 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342157013/2500000000 : ℝ), (659173931/1250000000 : ℝ), (-13612243/62500000 : ℝ)] ![(43873321714849/100000000000000 : ℝ), (1338920206331/3125000000000 : ℝ), (13281231669853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342157013/2500000000 : ℝ)|^8359 ≤ (43873321714849/100000000000000 : ℝ)^6311
        have hw : |(1342157013/2500000000 : ℝ)|=(1342157013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(659173931/1250000000 : ℝ)|^8359 ≤ (1338920206331/3125000000000 : ℝ)^6311
        have hw : |(659173931/1250000000 : ℝ)|=(659173931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13612243/62500000 : ℝ)|^8359 ≤ (13281231669853/100000000000000 : ℝ)^6311
        have hw : |(-13612243/62500000 : ℝ)|=(13612243/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1166_box_15 (p : ℝ) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1058777441/2500000000 : ℝ)*x 0 + (4426351471/10000000000 : ℝ)*x 1 + (4426351871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058777441/2500000000 : ℝ)^8359 ≤ (16023135345667/50000000000000 : ℝ)^6311 := by
    have hnat : (1058777441 : ℕ)^8359*50000000000000^6311 ≤ 16023135345667^6311*2500000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058777441 2500000000 16023135345667 50000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4426351471/10000000000 : ℝ)^8359 ≤ (33976862612501/100000000000000 : ℝ)^6311 := by
    have hnat : (4426351471 : ℕ)^8359*100000000000000^6311 ≤ 33976862612501^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426351471 10000000000 33976862612501 100000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426351871/10000000000 : ℝ)^8359 ≤ (8494216669827/25000000000000 : ℝ)^6311 := by
    have hnat : (4426351871 : ℕ)^8359*25000000000000^6311 ≤ 8494216669827^6311*10000000000^8359 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426351871 10000000000 8494216669827 25000000000000 8359 6311 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8359/2048 : ℝ)) 8359 6311 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058777441/2500000000 : ℝ), (4426351471/10000000000 : ℝ), (4426351871/10000000000 : ℝ)] ![(16023135345667/50000000000000 : ℝ), (33976862612501/100000000000000 : ℝ), (8494216669827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058777441/2500000000 : ℝ)|^8359 ≤ (16023135345667/50000000000000 : ℝ)^6311
        have hw : |(1058777441/2500000000 : ℝ)|=(1058777441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4426351471/10000000000 : ℝ)|^8359 ≤ (33976862612501/100000000000000 : ℝ)^6311
        have hw : |(4426351471/10000000000 : ℝ)|=(4426351471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426351871/10000000000 : ℝ)|^8359 ≤ (8494216669827/25000000000000 : ℝ)^6311
        have hw : |(4426351871/10000000000 : ℝ)|=(4426351871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1166_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31117/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59317/100000 : ℝ) ∧ (79881/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41589/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2277/20000 : ℝ) ^ (4179/1024 : ℝ) ≤ (220122042962687/1562500000000000000 : ℝ) := by
    have hpowers : (2277/20000 : ℝ)^4179 ≤ (220122042962687/1562500000000000000 : ℝ)^1024 := by
      have hnat : (2277 : ℕ)^4179*1562500000000000000^1024 ≤ 220122042962687^1024*20000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 20000 220122042962687 1562500000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/20000 : ℝ)) (X := (220122042962687/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (4179/1024 : ℝ) ≤ (16676449863915843/50000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^4179 ≤ (16676449863915843/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7031 : ℕ)^4179*50000000000000000000^1024 ≤ 16676449863915843^1024*50000^4179 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 16676449863915843 50000000000000000000 4179 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (16676449863915843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781470122042962687/781250000000000000 : ℝ) ≤ (2500172581767737/2500000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (781470122042962687/781250000000000000 : ℝ)^1024 ≤ (2500172581767737/2500000000000000 : ℝ)^4179 := by
      have hnat : (781470122042962687 : ℕ)^1024*2500000000000000^4179 ≤ 2500172581767737^4179*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781470122042962687 781250000000000000 2500172581767737 2500000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500172581767737/2500000000000000 : ℝ)) (X := (781470122042962687/781250000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023720355238721827/50000000000000000000 : ℝ) ≤ (10001162253896667/10000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (50023720355238721827/50000000000000000000 : ℝ)^1024 ≤ (10001162253896667/10000000000000000 : ℝ)^4179 := by
      have hnat : (50023720355238721827 : ℕ)^1024*10000000000000000^4179 ≤ 10001162253896667^4179*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023720355238721827 50000000000000000000 10001162253896667 10000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001162253896667/10000000000000000 : ℝ)) (X := (50023720355238721827/50000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016676449863915843/25000000000000000000 : ℝ) ≤ (5000817090361193/5000000000000000 : ℝ) ^ (4179/1024 : ℝ) := by
    have hpowers : (25016676449863915843/25000000000000000000 : ℝ)^1024 ≤ (5000817090361193/5000000000000000 : ℝ)^4179 := by
      have hnat : (25016676449863915843 : ℕ)^1024*5000000000000000^4179 ≤ 5000817090361193^4179*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016676449863915843 25000000000000000000 5000817090361193 5000000000000000 1024 4179 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000817090361193/5000000000000000 : ℝ)) (X := (25016676449863915843/25000000000000000000 : ℝ)) (by norm_num) 4179 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(220122042962687/1562500000000000000 : ℝ) ≤ ((13380551115873653083/13385000000000000000 : ℝ)+2*(471926825719/267700000000000 : ℝ)*(2277/20000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (13380551115873653083/13385000000000000000 : ℝ)+2*(471926825719/267700000000000 : ℝ)*(2277/20000 : ℝ)=(2500172581767737/2500000000000000 : ℝ) by norm_num, show 1+2*(220122042962687/1562500000000000000 : ℝ)=(781470122042962687/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16676449863915843/50000000000000000000 : ℝ)+(220122042962687/1562500000000000000 : ℝ) ≤ ((13380551115873653083/13385000000000000000 : ℝ)+(471926825719/267700000000000 : ℝ)*((7031/50000 : ℝ)+(2277/20000 : ℝ)))^(4179/1024 : ℝ) := by
    rw [show (13380551115873653083/13385000000000000000 : ℝ)+(471926825719/267700000000000 : ℝ)*((7031/50000 : ℝ)+(2277/20000 : ℝ))=(10001162253896667/10000000000000000 : ℝ) by norm_num, show 1+(16676449863915843/50000000000000000000 : ℝ)+(220122042962687/1562500000000000000 : ℝ)=(50023720355238721827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16676449863915843/50000000000000000000 : ℝ) ≤ ((13380551115873653083/13385000000000000000 : ℝ)+2*(471926825719/267700000000000 : ℝ)*(7031/50000 : ℝ))^(4179/1024 : ℝ) := by
    rw [show (13380551115873653083/13385000000000000000 : ℝ)+2*(471926825719/267700000000000 : ℝ)*(7031/50000 : ℝ)=(5000817090361193/5000000000000000 : ℝ) by norm_num, show 1+2*(16676449863915843/50000000000000000000 : ℝ)=(25016676449863915843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13380551115873653083/13385000000000000000 : ℝ)*(X 1 0+X 2 0)+(471926825719/267700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (13380551115873653083/13385000000000000000 : ℝ)) (alpha := (471926825719/267700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13380551115873653083/13385000000000000000 : ℝ)*(X 0 1+X 2 1)+(471926825719/267700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (13380551115873653083/13385000000000000000 : ℝ)) (alpha := (471926825719/267700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13380551115873653083/13385000000000000000 : ℝ)*(X 0 2+X 1 2)+(471926825719/267700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4179/1024 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (13380551115873653083/13385000000000000000 : ℝ)) (alpha := (471926825719/267700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-507339833/2500000000 : ℝ)*X 0 0+(2687982061/5000000000 : ℝ)*X 0 1+(2687982203/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296202107/10000000000 : ℝ)*X 1 0+(-534397619/2500000000 : ℝ)*X 1 1+(5375963643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648100857/5000000000 : ℝ)*X 2 0+(2687982099/5000000000 : ℝ)*X 2 1+(-427518051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4468593133/10000000000 : ℝ)*X 0 0+(538718991/1250000000 : ℝ)*X 0 1+(4309754033/10000000000 : ℝ)*X 0 2+(4468593133/10000000000 : ℝ)*X 1 0+(538718991/1250000000 : ℝ)*X 1 1+(4309754033/10000000000 : ℝ)*X 1 2+(4468593133/10000000000 : ℝ)*X 2 0+(538718991/1250000000 : ℝ)*X 2 1+(4309754033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-570738433/2500000000 : ℝ)*X 0 0+(5281440517/10000000000 : ℝ)*X 0 1+(2640720119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072589453/2000000000 : ℝ)*X 1 0+(-2174843507/10000000000 : ℝ)*X 1 1+(5281440023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681473311/5000000000 : ℝ)*X 2 0+(5281440231/10000000000 : ℝ)*X 2 1+(-2174844093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2126822621/5000000000 : ℝ)*X 0 0+(552150737/1250000000 : ℝ)*X 0 1+(4417206637/10000000000 : ℝ)*X 0 2+(2126822621/5000000000 : ℝ)*X 1 0+(552150737/1250000000 : ℝ)*X 1 1+(4417206637/10000000000 : ℝ)*X 1 2+(2126822621/5000000000 : ℝ)*X 2 0+(552150737/1250000000 : ℝ)*X 2 1+(4417206637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2229896133/10000000000 : ℝ)*X 0 0+(2608554519/5000000000 : ℝ)*X 0 1+(1346393573/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322353157/2500000000 : ℝ)*X 1 0+(-2133734299/10000000000 : ℝ)*X 1 1+(673196751/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289412487/10000000000 : ℝ)*X 2 0+(269278697/500000000 : ℝ)*X 2 1+(-2133734581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4490175317/10000000000 : ℝ)*X 0 0+(1074705323/2500000000 : ℝ)*X 0 1+(134338169/312500000 : ℝ)*X 0 2+(4490175317/10000000000 : ℝ)*X 1 0+(1074705323/2500000000 : ℝ)*X 1 1+(134338169/312500000 : ℝ)*X 1 2+(4490175317/10000000000 : ℝ)*X 2 0+(1074705323/2500000000 : ℝ)*X 2 1+(134338169/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2082722259/10000000000 : ℝ)*X 0 0+(543903467/1000000000 : ℝ)*X 0 1+(5273391131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368627971/10000000000 : ℝ)*X 1 0+(-1088979849/5000000000 : ℝ)*X 1 1+(1318347729/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1342157013/2500000000 : ℝ)*X 2 0+(659173931/1250000000 : ℝ)*X 2 1+(-13612243/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1058777441/2500000000 : ℝ)*X 0 0+(4426351471/10000000000 : ℝ)*X 0 1+(4426351871/10000000000 : ℝ)*X 0 2+(1058777441/2500000000 : ℝ)*X 1 0+(4426351471/10000000000 : ℝ)*X 1 1+(4426351871/10000000000 : ℝ)*X 1 2+(1058777441/2500000000 : ℝ)*X 2 0+(4426351471/10000000000 : ℝ)*X 2 1+(4426351871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1166_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31117/50000 : ℝ) ≤ (-52060617620450068135956214691697/83656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69742369/100000000000000 : ℝ)*(lower0) + (9134329/25000000000000 : ℝ)*(lower3) + (242203371/50000000000000 : ℝ)*(lower4) + (985138160432697/25000000000000 : ℝ)*(major0) + (985138160432697/25000000000000 : ℝ)*(major1) + (985138160432697/25000000000000 : ℝ)*(major2) + (195279513/2500000000000 : ℝ)*(sp1) + (29580858703/100000000000000 : ℝ)*(sp2) + (2356904383/100000000000000 : ℝ)*(sp3) + (5273797510313911/100000000000000 : ℝ)*(sp4) + (5273793445270351/100000000000000 : ℝ)*(sp5) + (5273771675592169/100000000000000 : ℝ)*(sp6) + (657011383669817/25000000000000 : ℝ)*(sp7) + (3746136961/100000000000000 : ℝ)*(sp12) + (2628047891583651/100000000000000 : ℝ)*(f.failure) + (5273801256450871/100000000000000 : ℝ)*(f.sum) + (2737227824523/836562500000000000000000000 : ℝ)*base66 + (2068263228056420149/334625000000000000000000000000000 : ℝ)*base68 + (330133190860795149/334625000000000000000000000000000 : ℝ)*base70 + (3481219312026045149/334625000000000000000000000000000 : ℝ)*base72 + (820414749772697/13385000000000000000000000000 : ℝ)*base73 + (678561045129295149/334625000000000000000000000000000 : ℝ)*base76 + (4400174653549170149/334625000000000000000000000000000 : ℝ)*base78 + (4243334347124579851/334625000000000000000000000000000 : ℝ)*base79 + (9325486641033/13385000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (73886643/10000000000000000000000 : ℝ)*base89 + (73886643/10000000000000000000000 : ℝ)*base91 + (73886643/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59317/100000 : ℝ) ≤ (49624556391118644065959833083697/83656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13323511/10000000000000 : ℝ)*(upper0) + (249601019/100000000000000 : ℝ)*(lower1) + (59648949/50000000000000 : ℝ)*(upper2) + (245993169/100000000000000 : ℝ)*(lower3) + (1001276674237803/25000000000000 : ℝ)*(major0) + (1001276674237803/25000000000000 : ℝ)*(major1) + (1001276674237803/25000000000000 : ℝ)*(major2) + (1329828034476091/25000000000000 : ℝ)*(sp0) + (265960373974771/5000000000000 : ℝ)*(sp1) + (531933967248219/10000000000000 : ℝ)*(sp2) + (166937871171387/6250000000000 : ℝ)*(sp3) + (13219298677/10000000000000 : ℝ)*(sp9) + (94581277021/100000000000000 : ℝ)*(sp11) + (13767288913/50000000000000 : ℝ)*(sp12) + (2671100520019213/100000000000000 : ℝ)*(f.failure) + (531933967248219/10000000000000 : ℝ)*(f.sum) + (30036872719807/13385000000000000000000000000 : ℝ)*base66 + (369002752100053351/334625000000000000000000000000000 : ℝ)*base68 + (1325263267129196649/334625000000000000000000000000000 : ℝ)*base69 + (1606414733736178351/334625000000000000000000000000000 : ℝ)*base72 + (16201214500799/6692500000000000000000000000 : ℝ)*base73 + (866918724834553351/334625000000000000000000000000000 : ℝ)*base76 + (380580347776178351/334625000000000000000000000000000 : ℝ)*base78 + (1263849495748053351/334625000000000000000000000000000 : ℝ)*base80 + (16961691025181/6692500000000000000000000000 : ℝ)*base82 + (645891/10000000000000000000000 : ℝ)*base90 + (645891/10000000000000000000000 : ℝ)*base92 + (645891/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79881/100000 : ℝ) ≤ (33413925039078949058144306323083/41828125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (101816113/50000000000000 : ℝ)*(upper0) + (49888609/50000000000000 : ℝ)*(upper1) + (9103287/10000000000000 : ℝ)*(upper2) + (46494983/20000000000000 : ℝ)*(lower5) + (559097728540833/12500000000000 : ℝ)*(major0) + (559097728540833/12500000000000 : ℝ)*(major1) + (559097728540833/12500000000000 : ℝ)*(major2) + (1350662347/12500000000000 : ℝ)*(sp1) + (19103426533/100000000000000 : ℝ)*(sp3) + (760438313/10000000000000 : ℝ)*(sp4) + (5935923953216979/100000000000000 : ℝ)*(sp8) + (1483980188075333/25000000000000 : ℝ)*(sp9) + (5935931557600109/100000000000000 : ℝ)*(sp10) + (2982985038927623/100000000000000 : ℝ)*(sp11) + (745751035588539/25000000000000 : ℝ)*(f.failure) + (5935931557600109/100000000000000 : ℝ)*(f.sum) + (11843750462589/13385000000000000000000000000 : ℝ)*base66 + (530928012256688139/167312500000000000000000000000000 : ℝ)*base67 + (428631371392125639/167312500000000000000000000000000 : ℝ)*base69 + (1537290621868438139/167312500000000000000000000000000 : ℝ)*base71 + (16394897271443/1673125000000000000000000000 : ℝ)*base74 + (2004599539240125639/167312500000000000000000000000000 : ℝ)*base75 + (443163987572500639/167312500000000000000000000000000 : ℝ)*base77 + (486720997336811861/167312500000000000000000000000000 : ℝ)*base80 + (898795764131/3346250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (16673973/2500000000000000000000 : ℝ)*base90 + (16673973/2500000000000000000000 : ℝ)*base92 + (16673973/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-41589/50000 : ℝ) ≤ (-278326198924254360774362576270319/334625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6239113/100000000000000 : ℝ)*(lower0) + (1854521/100000000000000 : ℝ)*(lower1) + (129167209/50000000000000 : ℝ)*(lower2) + (503588991/100000000000000 : ℝ)*(upper5) + (4507860317916431/100000000000000 : ℝ)*(major0) + (4507860317916431/100000000000000 : ℝ)*(major1) + (4507860317916431/100000000000000 : ℝ)*(major2) + (16095879587/100000000000000 : ℝ)*(sp0) + (92169149767/25000000000000 : ℝ)*(sp5) + (8564042231/6250000000000 : ℝ)*(sp7) + (6037030906833851/100000000000000 : ℝ)*(sp12) + (6036678326114369/100000000000000 : ℝ)*(sp13) + (6037047002713437/100000000000000 : ℝ)*(sp14) + (3006261793245041/100000000000000 : ℝ)*(sp15) + (1503199408960369/50000000000000 : ℝ)*(f.failure) + (6037047002713437/100000000000000 : ℝ)*(f.sum) + (48506059343317/6692500000000000000000000000 : ℝ)*base65 + (2634642887850456773/1338500000000000000000000000000000 : ℝ)*base67 + (746459546882956773/1338500000000000000000000000000000 : ℝ)*base69 + (4163233493636456773/1338500000000000000000000000000000 : ℝ)*base71 + (21325049191203/1673125000000000000000000000 : ℝ)*base73 + (13872573883930456773/1338500000000000000000000000000000 : ℝ)*base75 + (10045980606543956773/1338500000000000000000000000000000 : ℝ)*base77 + (2997356858941543227/1338500000000000000000000000000000 : ℝ)*base80 + (12512642965617/6692500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (27949217/5000000000000000000000 : ℝ)*base89 + (27949217/5000000000000000000000 : ℝ)*base91 + (27949217/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1166_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59317/100000 : ℝ) else (79881/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41589/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1166_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1166_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59317/100000 : ℝ) else (79881/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41589/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1166_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4179/1024 : ℝ) ≤ p) (hpb : p ≤ (8359/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149942193/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31117/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59317/100000 : ℝ) else (79881/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41589/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1166_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

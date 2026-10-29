-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1560_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:35.580127+00:00
-- url     : https://prove2.me/submissions/aeac3b6e-c2ad-4daa-8eda-6df035b3e164

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
theorem support_rectangle_w1560_s6_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179936743/1000000000 : ℝ)*x 0 + (2713528177/5000000000 : ℝ)*x 1 + (2609857447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179936743/1000000000 : ℝ)^4617 ≤ (11036466526587/100000000000000 : ℝ)^3593 := by
    have hnat : (179936743 : ℕ)^4617*100000000000000^3593 ≤ 11036466526587^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179936743 1000000000 11036466526587 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713528177/5000000000 : ℝ)^4617 ≤ (2849676443773/6250000000000 : ℝ)^3593 := by
    have hnat : (2713528177 : ℕ)^4617*6250000000000^3593 ≤ 2849676443773^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713528177 5000000000 2849676443773 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609857447/5000000000 : ℝ)^4617 ≤ (21684355179137/50000000000000 : ℝ)^3593 := by
    have hnat : (2609857447 : ℕ)^4617*50000000000000^3593 ≤ 21684355179137^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609857447 5000000000 21684355179137 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179936743/1000000000 : ℝ), (2713528177/5000000000 : ℝ), (2609857447/5000000000 : ℝ)] ![(11036466526587/100000000000000 : ℝ), (2849676443773/6250000000000 : ℝ), (21684355179137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179936743/1000000000 : ℝ)|^4617 ≤ (11036466526587/100000000000000 : ℝ)^3593
        have hw : |(-179936743/1000000000 : ℝ)|=(179936743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713528177/5000000000 : ℝ)|^4617 ≤ (2849676443773/6250000000000 : ℝ)^3593
        have hw : |(2713528177/5000000000 : ℝ)|=(2713528177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609857447/5000000000 : ℝ)|^4617 ≤ (21684355179137/50000000000000 : ℝ)^3593
        have hw : |(2609857447/5000000000 : ℝ)|=(2609857447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534879783/1000000000 : ℝ)*x 0 + (-1905459693/10000000000 : ℝ)*x 1 + (5219716437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534879783/1000000000 : ℝ)^4617 ≤ (22375851839739/50000000000000 : ℝ)^3593 := by
    have hnat : (534879783 : ℕ)^4617*50000000000000^3593 ≤ 22375851839739^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534879783 1000000000 22375851839739 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1905459693/10000000000 : ℝ)^4617 ≤ (2375913895023/20000000000000 : ℝ)^3593 := by
    have hnat : (1905459693 : ℕ)^4617*20000000000000^3593 ≤ 2375913895023^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905459693 10000000000 2375913895023 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219716437/10000000000 : ℝ)^4617 ≤ (21684363416123/50000000000000 : ℝ)^3593 := by
    have hnat : (5219716437 : ℕ)^4617*50000000000000^3593 ≤ 21684363416123^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219716437 10000000000 21684363416123 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534879783/1000000000 : ℝ), (-1905459693/10000000000 : ℝ), (5219716437/10000000000 : ℝ)] ![(22375851839739/50000000000000 : ℝ), (2375913895023/20000000000000 : ℝ), (21684363416123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534879783/1000000000 : ℝ)|^4617 ≤ (22375851839739/50000000000000 : ℝ)^3593
        have hw : |(534879783/1000000000 : ℝ)|=(534879783/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1905459693/10000000000 : ℝ)|^4617 ≤ (2375913895023/20000000000000 : ℝ)^3593
        have hw : |(-1905459693/10000000000 : ℝ)|=(1905459693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219716437/10000000000 : ℝ)|^4617 ≤ (21684363416123/50000000000000 : ℝ)^3593
        have hw : |(5219716437/10000000000 : ℝ)|=(5219716437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6685997/12500000 : ℝ)*x 0 + (5219716909/10000000000 : ℝ)*x 1 + (-1905459373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6685997/12500000 : ℝ)^4617 ≤ (44751701206707/100000000000000 : ℝ)^3593 := by
    have hnat : (6685997 : ℕ)^4617*100000000000000^3593 ≤ 44751701206707^3593*12500000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6685997 12500000 44751701206707 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219716909/10000000000 : ℝ)^4617 ≤ (8673746374319/20000000000000 : ℝ)^3593 := by
    have hnat : (5219716909 : ℕ)^4617*20000000000000^3593 ≤ 8673746374319^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219716909 10000000000 8673746374319 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1905459373/10000000000 : ℝ)^4617 ≤ (1484945863937/12500000000000 : ℝ)^3593 := by
    have hnat : (1905459373 : ℕ)^4617*12500000000000^3593 ≤ 1484945863937^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905459373 10000000000 1484945863937 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6685997/12500000 : ℝ), (5219716909/10000000000 : ℝ), (-1905459373/10000000000 : ℝ)] ![(44751701206707/100000000000000 : ℝ), (8673746374319/20000000000000 : ℝ), (1484945863937/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6685997/12500000 : ℝ)|^4617 ≤ (44751701206707/100000000000000 : ℝ)^3593
        have hw : |(6685997/12500000 : ℝ)|=(6685997/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219716909/10000000000 : ℝ)|^4617 ≤ (8673746374319/20000000000000 : ℝ)^3593
        have hw : |(5219716909/10000000000 : ℝ)|=(5219716909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1905459373/10000000000 : ℝ)|^4617 ≤ (1484945863937/12500000000000 : ℝ)^3593
        have hw : |(-1905459373/10000000000 : ℝ)|=(1905459373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265495683/625000000 : ℝ)*x 0 + (4010555051/10000000000 : ℝ)*x 1 + (2248330071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265495683/625000000 : ℝ)^4617 ≤ (33281932548953/100000000000000 : ℝ)^3593 := by
    have hnat : (265495683 : ℕ)^4617*100000000000000^3593 ≤ 33281932548953^3593*625000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265495683 625000000 33281932548953 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010555051/10000000000 : ℝ)^4617 ≤ (30911374135847/100000000000000 : ℝ)^3593 := by
    have hnat : (4010555051 : ℕ)^4617*100000000000000^3593 ≤ 30911374135847^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010555051 10000000000 30911374135847 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248330071/5000000000 : ℝ)^4617 ≤ (35806693295033/100000000000000 : ℝ)^3593 := by
    have hnat : (2248330071 : ℕ)^4617*100000000000000^3593 ≤ 35806693295033^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248330071 5000000000 35806693295033 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265495683/625000000 : ℝ), (4010555051/10000000000 : ℝ), (2248330071/5000000000 : ℝ)] ![(33281932548953/100000000000000 : ℝ), (30911374135847/100000000000000 : ℝ), (35806693295033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265495683/625000000 : ℝ)|^4617 ≤ (33281932548953/100000000000000 : ℝ)^3593
        have hw : |(265495683/625000000 : ℝ)|=(265495683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010555051/10000000000 : ℝ)|^4617 ≤ (30911374135847/100000000000000 : ℝ)^3593
        have hw : |(4010555051/10000000000 : ℝ)|=(4010555051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248330071/5000000000 : ℝ)|^4617 ≤ (35806693295033/100000000000000 : ℝ)^3593
        have hw : |(2248330071/5000000000 : ℝ)|=(2248330071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-899697881/5000000000 : ℝ)*x 0 + (1044158647/2000000000 : ℝ)*x 1 + (1356492293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899697881/5000000000 : ℝ)^4617 ≤ (2759172456947/25000000000000 : ℝ)^3593 := by
    have hnat : (899697881 : ℕ)^4617*25000000000000^3593 ≤ 2759172456947^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899697881 5000000000 2759172456947 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044158647/2000000000 : ℝ)^4617 ≤ (21690111848547/50000000000000 : ℝ)^3593 := by
    have hnat : (1044158647 : ℕ)^4617*50000000000000^3593 ≤ 21690111848547^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044158647 2000000000 21690111848547 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356492293/2500000000 : ℝ)^4617 ≤ (4558308646219/10000000000000 : ℝ)^3593 := by
    have hnat : (1356492293 : ℕ)^4617*10000000000000^3593 ≤ 4558308646219^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356492293 2500000000 4558308646219 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899697881/5000000000 : ℝ), (1044158647/2000000000 : ℝ), (1356492293/2500000000 : ℝ)] ![(2759172456947/25000000000000 : ℝ), (21690111848547/50000000000000 : ℝ), (4558308646219/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899697881/5000000000 : ℝ)|^4617 ≤ (2759172456947/25000000000000 : ℝ)^3593
        have hw : |(-899697881/5000000000 : ℝ)|=(899697881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044158647/2000000000 : ℝ)|^4617 ≤ (21690111848547/50000000000000 : ℝ)^3593
        have hw : |(1044158647/2000000000 : ℝ)|=(1044158647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356492293/2500000000 : ℝ)|^4617 ≤ (4558308646219/10000000000000 : ℝ)^3593
        have hw : |(1356492293/2500000000 : ℝ)|=(1356492293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247994523/10000000000 : ℝ)*x 0 + (1123533337/2500000000 : ℝ)*x 1 + (2006550253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247994523/10000000000 : ℝ)^4617 ≤ (33282572810833/100000000000000 : ℝ)^3593 := by
    have hnat : (4247994523 : ℕ)^4617*100000000000000^3593 ≤ 33282572810833^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247994523 10000000000 33282572810833 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123533337/2500000000 : ℝ)^4617 ≤ (35780840240397/100000000000000 : ℝ)^3593 := by
    have hnat : (1123533337 : ℕ)^4617*100000000000000^3593 ≤ 35780840240397^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123533337 2500000000 35780840240397 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006550253/5000000000 : ℝ)^4617 ≤ (15468293470911/50000000000000 : ℝ)^3593 := by
    have hnat : (2006550253 : ℕ)^4617*50000000000000^3593 ≤ 15468293470911^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006550253 5000000000 15468293470911 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247994523/10000000000 : ℝ), (1123533337/2500000000 : ℝ), (2006550253/5000000000 : ℝ)] ![(33282572810833/100000000000000 : ℝ), (35780840240397/100000000000000 : ℝ), (15468293470911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247994523/10000000000 : ℝ)|^4617 ≤ (33282572810833/100000000000000 : ℝ)^3593
        have hw : |(4247994523/10000000000 : ℝ)|=(4247994523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123533337/2500000000 : ℝ)|^4617 ≤ (35780840240397/100000000000000 : ℝ)^3593
        have hw : |(1123533337/2500000000 : ℝ)|=(1123533337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006550253/5000000000 : ℝ)|^4617 ≤ (15468293470911/50000000000000 : ℝ)^3593
        have hw : |(2006550253/5000000000 : ℝ)|=(2006550253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6881843051/10000000000 : ℝ)*x 0 + (1377154163/5000000000 : ℝ)*x 1 + (550599881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6881843051/10000000000 : ℝ)^4617 ≤ (61865830490501/100000000000000 : ℝ)^3593 := by
    have hnat : (6881843051 : ℕ)^4617*100000000000000^3593 ≤ 61865830490501^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6881843051 10000000000 61865830490501 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377154163/5000000000 : ℝ)^4617 ≤ (4768226983053/25000000000000 : ℝ)^3593 := by
    have hnat : (1377154163 : ℕ)^4617*25000000000000^3593 ≤ 4768226983053^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377154163 5000000000 4768226983053 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550599881/2000000000 : ℝ)^4617 ≤ (19061261550081/100000000000000 : ℝ)^3593 := by
    have hnat : (550599881 : ℕ)^4617*100000000000000^3593 ≤ 19061261550081^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550599881 2000000000 19061261550081 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6881843051/10000000000 : ℝ), (1377154163/5000000000 : ℝ), (550599881/2000000000 : ℝ)] ![(61865830490501/100000000000000 : ℝ), (4768226983053/25000000000000 : ℝ), (19061261550081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6881843051/10000000000 : ℝ)|^4617 ≤ (61865830490501/100000000000000 : ℝ)^3593
        have hw : |(-6881843051/10000000000 : ℝ)|=(6881843051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377154163/5000000000 : ℝ)|^4617 ≤ (4768226983053/25000000000000 : ℝ)^3593
        have hw : |(1377154163/5000000000 : ℝ)|=(1377154163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550599881/2000000000 : ℝ)|^4617 ≤ (19061261550081/100000000000000 : ℝ)^3593
        have hw : |(550599881/2000000000 : ℝ)|=(550599881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8361214507/10000000000 : ℝ)*x 0 + (-625879913/10000000000 : ℝ)*x 1 + (2599295629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8361214507/10000000000 : ℝ)^4617 ≤ (79454087207199/100000000000000 : ℝ)^3593 := by
    have hnat : (8361214507 : ℕ)^4617*100000000000000^3593 ≤ 79454087207199^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8361214507 10000000000 79454087207199 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625879913/10000000000 : ℝ)^4617 ≤ (177571246987/6250000000000 : ℝ)^3593 := by
    have hnat : (625879913 : ℕ)^4617*6250000000000^3593 ≤ 177571246987^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625879913 10000000000 177571246987 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599295629/10000000000 : ℝ)^4617 ≤ (17704772824353/100000000000000 : ℝ)^3593 := by
    have hnat : (2599295629 : ℕ)^4617*100000000000000^3593 ≤ 17704772824353^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599295629 10000000000 17704772824353 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8361214507/10000000000 : ℝ), (-625879913/10000000000 : ℝ), (2599295629/10000000000 : ℝ)] ![(79454087207199/100000000000000 : ℝ), (177571246987/6250000000000 : ℝ), (17704772824353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8361214507/10000000000 : ℝ)|^4617 ≤ (79454087207199/100000000000000 : ℝ)^3593
        have hw : |(8361214507/10000000000 : ℝ)|=(8361214507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-625879913/10000000000 : ℝ)|^4617 ≤ (177571246987/6250000000000 : ℝ)^3593
        have hw : |(-625879913/10000000000 : ℝ)|=(625879913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599295629/10000000000 : ℝ)|^4617 ≤ (17704772824353/100000000000000 : ℝ)^3593
        have hw : |(2599295629/10000000000 : ℝ)|=(2599295629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s6_8 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4189410643/5000000000 : ℝ)*x 0 + (2488029147/10000000000 : ℝ)*x 1 + (-751502199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189410643/5000000000 : ℝ)^4617 ≤ (19917286806787/25000000000000 : ℝ)^3593 := by
    have hnat : (4189410643 : ℕ)^4617*25000000000000^3593 ≤ 19917286806787^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189410643 5000000000 19917286806787 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2488029147/10000000000 : ℝ)^4617 ≤ (8368451741039/50000000000000 : ℝ)^3593 := by
    have hnat : (2488029147 : ℕ)^4617*50000000000000^3593 ≤ 8368451741039^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2488029147 10000000000 8368451741039 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751502199/10000000000 : ℝ)^4617 ≤ (3593949272351/100000000000000 : ℝ)^3593 := by
    have hnat : (751502199 : ℕ)^4617*100000000000000^3593 ≤ 3593949272351^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751502199 10000000000 3593949272351 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189410643/5000000000 : ℝ), (2488029147/10000000000 : ℝ), (-751502199/10000000000 : ℝ)] ![(19917286806787/25000000000000 : ℝ), (8368451741039/50000000000000 : ℝ), (3593949272351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189410643/5000000000 : ℝ)|^4617 ≤ (19917286806787/25000000000000 : ℝ)^3593
        have hw : |(4189410643/5000000000 : ℝ)|=(4189410643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2488029147/10000000000 : ℝ)|^4617 ≤ (8368451741039/50000000000000 : ℝ)^3593
        have hw : |(2488029147/10000000000 : ℝ)|=(2488029147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-751502199/10000000000 : ℝ)|^4617 ≤ (3593949272351/100000000000000 : ℝ)^3593
        have hw : |(-751502199/10000000000 : ℝ)|=(751502199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11089/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (693/6250 : ℝ) ^ (4615/1024 : ℝ) ≤ (4958041458883121/100000000000000000000 : ℝ) := by
    have hpowers : (693/6250 : ℝ)^4615 ≤ (4958041458883121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (693 : ℕ)^4615*100000000000000000000^1024 ≤ 4958041458883121^1024*6250^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 6250 4958041458883121 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/6250 : ℝ)) (X := (4958041458883121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4615/1024 : ℝ) ≤ (1396184282435981/6250000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4615 ≤ (1396184282435981/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4615*6250000000000000000^1024 ≤ 1396184282435981^1024*20000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 1396184282435981 6250000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (1396184282435981/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004958041458883121/50000000000000000000 : ℝ) ≤ (1250027501834221/1250000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50004958041458883121/50000000000000000000 : ℝ)^1024 ≤ (1250027501834221/1250000000000000 : ℝ)^4615 := by
      have hnat : (50004958041458883121 : ℕ)^1024*1250000000000000^4615 ≤ 1250027501834221^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004958041458883121 50000000000000000000 1250027501834221 1250000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250027501834221/1250000000000000 : ℝ)) (X := (50004958041458883121/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027296989977858817/100000000000000000000 : ℝ) ≤ (10000605615377587/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (100027296989977858817/100000000000000000000 : ℝ)^1024 ≤ (10000605615377587/10000000000000000 : ℝ)^4615 := by
      have hnat : (100027296989977858817 : ℕ)^1024*10000000000000000^4615 ≤ 10000605615377587^4615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027296989977858817 100000000000000000000 10000605615377587 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000605615377587/10000000000000000 : ℝ)) (X := (100027296989977858817/100000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126396184282435981/3125000000000000000 : ℝ) ≤ (5000495608040703/5000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (3126396184282435981/3125000000000000000 : ℝ)^1024 ≤ (5000495608040703/5000000000000000 : ℝ)^4615 := by
      have hnat : (3126396184282435981 : ℕ)^1024*5000000000000000^4615 ≤ 5000495608040703^4615*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126396184282435981 3125000000000000000 5000495608040703 5000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000495608040703/5000000000000000 : ℝ)) (X := (3126396184282435981/3125000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4958041458883121/100000000000000000000 : ℝ) ≤ ((5495302040414083469/5496250000000000000 : ℝ)+2*(385600703819/439700000000000 : ℝ)*(693/6250 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (5495302040414083469/5496250000000000000 : ℝ)+2*(385600703819/439700000000000 : ℝ)*(693/6250 : ℝ)=(1250027501834221/1250000000000000 : ℝ) by norm_num, show 1+2*(4958041458883121/100000000000000000000 : ℝ)=(50004958041458883121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1396184282435981/6250000000000000000 : ℝ)+(4958041458883121/100000000000000000000 : ℝ) ≤ ((5495302040414083469/5496250000000000000 : ℝ)+(385600703819/439700000000000 : ℝ)*((3097/20000 : ℝ)+(693/6250 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (5495302040414083469/5496250000000000000 : ℝ)+(385600703819/439700000000000 : ℝ)*((3097/20000 : ℝ)+(693/6250 : ℝ))=(10000605615377587/10000000000000000 : ℝ) by norm_num, show 1+(1396184282435981/6250000000000000000 : ℝ)+(4958041458883121/100000000000000000000 : ℝ)=(100027296989977858817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1396184282435981/6250000000000000000 : ℝ) ≤ ((5495302040414083469/5496250000000000000 : ℝ)+2*(385600703819/439700000000000 : ℝ)*(3097/20000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (5495302040414083469/5496250000000000000 : ℝ)+2*(385600703819/439700000000000 : ℝ)*(3097/20000 : ℝ)=(5000495608040703/5000000000000000 : ℝ) by norm_num, show 1+2*(1396184282435981/6250000000000000000 : ℝ)=(3126396184282435981/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5495302040414083469/5496250000000000000 : ℝ)*(X 1 0+X 2 0)+(385600703819/439700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5495302040414083469/5496250000000000000 : ℝ)) (alpha := (385600703819/439700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5495302040414083469/5496250000000000000 : ℝ)*(X 0 1+X 2 1)+(385600703819/439700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5495302040414083469/5496250000000000000 : ℝ)) (alpha := (385600703819/439700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5495302040414083469/5496250000000000000 : ℝ)*(X 0 2+X 1 2)+(385600703819/439700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (5495302040414083469/5496250000000000000 : ℝ)) (alpha := (385600703819/439700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-179936743/1000000000 : ℝ)*X 0 0+(2713528177/5000000000 : ℝ)*X 0 1+(2609857447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534879783/1000000000 : ℝ)*X 1 0+(-1905459693/10000000000 : ℝ)*X 1 1+(5219716437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((6685997/12500000 : ℝ)*X 2 0+(5219716909/10000000000 : ℝ)*X 2 1+(-1905459373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((265495683/625000000 : ℝ)*X 0 0+(4010555051/10000000000 : ℝ)*X 0 1+(2248330071/5000000000 : ℝ)*X 0 2+(265495683/625000000 : ℝ)*X 1 0+(4010555051/10000000000 : ℝ)*X 1 1+(2248330071/5000000000 : ℝ)*X 1 2+(265495683/625000000 : ℝ)*X 2 0+(4010555051/10000000000 : ℝ)*X 2 1+(2248330071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-899697881/5000000000 : ℝ)*X 0 0+(1044158647/2000000000 : ℝ)*X 0 1+(1356492293/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4247994523/10000000000 : ℝ)*X 0 0+(1123533337/2500000000 : ℝ)*X 0 1+(2006550253/5000000000 : ℝ)*X 0 2+(4247994523/10000000000 : ℝ)*X 1 0+(1123533337/2500000000 : ℝ)*X 1 1+(2006550253/5000000000 : ℝ)*X 1 2+(4247994523/10000000000 : ℝ)*X 2 0+(1123533337/2500000000 : ℝ)*X 2 1+(2006550253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-6881843051/10000000000 : ℝ)*X 0 0+(1377154163/5000000000 : ℝ)*X 0 1+(550599881/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8361214507/10000000000 : ℝ)*X 1 0+(-625879913/10000000000 : ℝ)*X 1 1+(2599295629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_7 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((4189410643/5000000000 : ℝ)*X 2 0+(2488029147/10000000000 : ℝ)*X 2 1+(-751502199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s6_8 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9762540310274870512263573/5496250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (355722941/100000000000000 : ℝ)*(lower2) + (45058123/25000000000000 : ℝ)*(lower3) + (68801989153639/2000000000000 : ℝ)*(major0) + (68801989153639/2000000000000 : ℝ)*(major1) + (68801989153639/2000000000000 : ℝ)*(major2) + (301436471727301/6250000000000 : ℝ)*(sp0) + (3858418779559/80000000000 : ℝ)*(sp1) + (4823021938995689/100000000000000 : ℝ)*(sp2) + (2057169981290741/100000000000000 : ℝ)*(sp3) + (10064605477/25000000000000 : ℝ)*(sp4) + (4601536751/100000000000000 : ℝ)*(sp5) + (46727039/10000000000000 : ℝ)*(sp6) + (199720091/25000000000000 : ℝ)*(sp7) + (93373337/4000000000000 : ℝ)*(sp8) + (514293645706873/25000000000000 : ℝ)*(f.failure) + (2411512136664557/50000000000000 : ℝ)*(f.sum) + (678348102347/175880000000000000000000000 : ℝ)*base65 + (261009286626278691/10992500000000000000000000000000 : ℝ)*base67 + (51604653241291191/10992500000000000000000000000000 : ℝ)*base69 + (119681455815126309/10992500000000000000000000000000 : ℝ)*base72 + (14759748598219/4397000000000000000000000000 : ℝ)*base74 + (50941708916638809/10992500000000000000000000000000 : ℝ)*base76 + (608456129902861309/10992500000000000000000000000000 : ℝ)*base78 + (243306336520281309/10992500000000000000000000000000 : ℝ)*base80 + (9353121138489/2198500000000000000000000000 : ℝ)*base81 + (14218647/1250000000000000000000 : ℝ)*base89 + (14218647/1250000000000000000000 : ℝ)*base91 + (14218647/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1560_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1560_box_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-796971971/5000000000 : ℝ)*x 0 + (5397663463/10000000000 : ℝ)*x 1 + (5397663601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (796971971/5000000000 : ℝ)^4617 ≤ (9444499994519/100000000000000 : ℝ)^3593 := by
    have hnat : (796971971 : ℕ)^4617*100000000000000^3593 ≤ 9444499994519^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796971971 5000000000 9444499994519 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397663463/10000000000 : ℝ)^4617 ≤ (9055549850329/20000000000000 : ℝ)^3593 := by
    have hnat : (5397663463 : ℕ)^4617*20000000000000^3593 ≤ 9055549850329^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397663463 10000000000 9055549850329 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397663601/10000000000 : ℝ)^4617 ≤ (22638875369579/50000000000000 : ℝ)^3593 := by
    have hnat : (5397663601 : ℕ)^4617*50000000000000^3593 ≤ 22638875369579^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397663601 10000000000 22638875369579 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-796971971/5000000000 : ℝ), (5397663463/10000000000 : ℝ), (5397663601/10000000000 : ℝ)] ![(9444499994519/100000000000000 : ℝ), (9055549850329/20000000000000 : ℝ), (22638875369579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-796971971/5000000000 : ℝ)|^4617 ≤ (9444499994519/100000000000000 : ℝ)^3593
        have hw : |(-796971971/5000000000 : ℝ)|=(796971971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397663463/10000000000 : ℝ)|^4617 ≤ (9055549850329/20000000000000 : ℝ)^3593
        have hw : |(5397663463/10000000000 : ℝ)|=(5397663463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397663601/10000000000 : ℝ)|^4617 ≤ (22638875369579/50000000000000 : ℝ)^3593
        have hw : |(5397663601/10000000000 : ℝ)|=(5397663601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054226591/2000000000 : ℝ)*x 0 + (-884889133/5000000000 : ℝ)*x 1 + (5397663113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054226591/2000000000 : ℝ)^4617 ≤ (10979612120887/25000000000000 : ℝ)^3593 := by
    have hnat : (1054226591 : ℕ)^4617*25000000000000^3593 ≤ 10979612120887^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054226591 2000000000 10979612120887 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884889133/5000000000 : ℝ)^4617 ≤ (168809469223/1562500000000 : ℝ)^3593 := by
    have hnat : (884889133 : ℕ)^4617*1562500000000^3593 ≤ 168809469223^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884889133 5000000000 168809469223 1562500000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397663113/10000000000 : ℝ)^4617 ≤ (45277745478967/100000000000000 : ℝ)^3593 := by
    have hnat : (5397663113 : ℕ)^4617*100000000000000^3593 ≤ 45277745478967^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397663113 10000000000 45277745478967 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054226591/2000000000 : ℝ), (-884889133/5000000000 : ℝ), (5397663113/10000000000 : ℝ)] ![(10979612120887/25000000000000 : ℝ), (168809469223/1562500000000 : ℝ), (45277745478967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054226591/2000000000 : ℝ)|^4617 ≤ (10979612120887/25000000000000 : ℝ)^3593
        have hw : |(1054226591/2000000000 : ℝ)|=(1054226591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-884889133/5000000000 : ℝ)|^4617 ≤ (168809469223/1562500000000 : ℝ)^3593
        have hw : |(-884889133/5000000000 : ℝ)|=(884889133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397663113/10000000000 : ℝ)|^4617 ≤ (45277745478967/100000000000000 : ℝ)^3593
        have hw : |(5397663113/10000000000 : ℝ)|=(5397663113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635565869/5000000000 : ℝ)*x 0 + (2698832083/5000000000 : ℝ)*x 1 + (-1769778479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635565869/5000000000 : ℝ)^4617 ≤ (43918435453793/100000000000000 : ℝ)^3593 := by
    have hnat : (2635565869 : ℕ)^4617*100000000000000^3593 ≤ 43918435453793^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635565869 5000000000 43918435453793 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698832083/5000000000 : ℝ)^4617 ≤ (22638878414669/50000000000000 : ℝ)^3593 := by
    have hnat : (2698832083 : ℕ)^4617*50000000000000^3593 ≤ 22638878414669^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698832083 5000000000 22638878414669 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769778479/10000000000 : ℝ)^4617 ≤ (2700951925283/25000000000000 : ℝ)^3593 := by
    have hnat : (1769778479 : ℕ)^4617*25000000000000^3593 ≤ 2700951925283^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769778479 10000000000 2700951925283 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635565869/5000000000 : ℝ), (2698832083/5000000000 : ℝ), (-1769778479/10000000000 : ℝ)] ![(43918435453793/100000000000000 : ℝ), (22638878414669/50000000000000 : ℝ), (2700951925283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635565869/5000000000 : ℝ)|^4617 ≤ (43918435453793/100000000000000 : ℝ)^3593
        have hw : |(2635565869/5000000000 : ℝ)|=(2635565869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698832083/5000000000 : ℝ)|^4617 ≤ (22638878414669/50000000000000 : ℝ)^3593
        have hw : |(2698832083/5000000000 : ℝ)|=(2698832083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769778479/10000000000 : ℝ)|^4617 ≤ (2700951925283/25000000000000 : ℝ)^3593
        have hw : |(-1769778479/10000000000 : ℝ)|=(1769778479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (111224809/250000000 : ℝ)*x 0 + (830818199/2000000000 : ℝ)*x 1 + (4154090797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111224809/250000000 : ℝ)^4617 ≤ (35319676938501/100000000000000 : ℝ)^3593 := by
    have hnat : (111224809 : ℕ)^4617*100000000000000^3593 ≤ 35319676938501^3593*250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111224809 250000000 35319676938501 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830818199/2000000000 : ℝ)^4617 ≤ (8085040628643/25000000000000 : ℝ)^3593 := by
    have hnat : (830818199 : ℕ)^4617*25000000000000^3593 ≤ 8085040628643^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830818199 2000000000 8085040628643 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154090797/10000000000 : ℝ)^4617 ≤ (16170080266901/50000000000000 : ℝ)^3593 := by
    have hnat : (4154090797 : ℕ)^4617*50000000000000^3593 ≤ 16170080266901^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154090797 10000000000 16170080266901 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(111224809/250000000 : ℝ), (830818199/2000000000 : ℝ), (4154090797/10000000000 : ℝ)] ![(35319676938501/100000000000000 : ℝ), (8085040628643/25000000000000 : ℝ), (16170080266901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(111224809/250000000 : ℝ)|^4617 ≤ (35319676938501/100000000000000 : ℝ)^3593
        have hw : |(111224809/250000000 : ℝ)|=(111224809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830818199/2000000000 : ℝ)|^4617 ≤ (8085040628643/25000000000000 : ℝ)^3593
        have hw : |(830818199/2000000000 : ℝ)|=(830818199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154090797/10000000000 : ℝ)|^4617 ≤ (16170080266901/50000000000000 : ℝ)^3593
        have hw : |(4154090797/10000000000 : ℝ)|=(4154090797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-402037927/2000000000 : ℝ)*x 0 + (2622434503/5000000000 : ℝ)*x 1 + (524486993/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402037927/2000000000 : ℝ)^4617 ≤ (12725080907413/100000000000000 : ℝ)^3593 := by
    have hnat : (402037927 : ℕ)^4617*100000000000000^3593 ≤ 12725080907413^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402037927 2000000000 12725080907413 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622434503/5000000000 : ℝ)^4617 ≤ (43637454598381/100000000000000 : ℝ)^3593 := by
    have hnat : (2622434503 : ℕ)^4617*100000000000000^3593 ≤ 43637454598381^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622434503 5000000000 43637454598381 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524486993/1000000000 : ℝ)^4617 ≤ (2727341529817/6250000000000 : ℝ)^3593 := by
    have hnat : (524486993 : ℕ)^4617*6250000000000^3593 ≤ 2727341529817^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524486993 1000000000 2727341529817 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402037927/2000000000 : ℝ), (2622434503/5000000000 : ℝ), (524486993/1000000000 : ℝ)] ![(12725080907413/100000000000000 : ℝ), (43637454598381/100000000000000 : ℝ), (2727341529817/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402037927/2000000000 : ℝ)|^4617 ≤ (12725080907413/100000000000000 : ℝ)^3593
        have hw : |(-402037927/2000000000 : ℝ)|=(402037927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622434503/5000000000 : ℝ)|^4617 ≤ (43637454598381/100000000000000 : ℝ)^3593
        have hw : |(2622434503/5000000000 : ℝ)|=(2622434503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524486993/1000000000 : ℝ)|^4617 ≤ (2727341529817/6250000000000 : ℝ)^3593
        have hw : |(524486993/1000000000 : ℝ)|=(524486993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377124919/10000000000 : ℝ)*x 0 + (-366696299/2000000000 : ℝ)*x 1 + (104897381/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377124919/10000000000 : ℝ)^4617 ≤ (45056482798073/100000000000000 : ℝ)^3593 := by
    have hnat : (5377124919 : ℕ)^4617*100000000000000^3593 ≤ 45056482798073^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377124919 10000000000 45056482798073 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366696299/2000000000 : ℝ)^4617 ≤ (11306062128293/100000000000000 : ℝ)^3593 := by
    have hnat : (366696299 : ℕ)^4617*100000000000000^3593 ≤ 11306062128293^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366696299 2000000000 11306062128293 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104897381/200000000 : ℝ)^4617 ≤ (8727491013759/20000000000000 : ℝ)^3593 := by
    have hnat : (104897381 : ℕ)^4617*20000000000000^3593 ≤ 8727491013759^3593*200000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104897381 200000000 8727491013759 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377124919/10000000000 : ℝ), (-366696299/2000000000 : ℝ), (104897381/200000000 : ℝ)] ![(45056482798073/100000000000000 : ℝ), (11306062128293/100000000000000 : ℝ), (8727491013759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377124919/10000000000 : ℝ)|^4617 ≤ (45056482798073/100000000000000 : ℝ)^3593
        have hw : |(5377124919/10000000000 : ℝ)|=(5377124919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366696299/2000000000 : ℝ)|^4617 ≤ (11306062128293/100000000000000 : ℝ)^3593
        have hw : |(-366696299/2000000000 : ℝ)|=(366696299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104897381/200000000 : ℝ)|^4617 ≤ (8727491013759/20000000000000 : ℝ)^3593
        have hw : |(104897381/200000000 : ℝ)|=(104897381/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688562271/5000000000 : ℝ)*x 0 + (52448693/100000000 : ℝ)*x 1 + (-1833481669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688562271/5000000000 : ℝ)^4617 ≤ (11264119684693/25000000000000 : ℝ)^3593 := by
    have hnat : (2688562271 : ℕ)^4617*25000000000000^3593 ≤ 11264119684693^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688562271 5000000000 11264119684693 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52448693/100000000 : ℝ)^4617 ≤ (43637457741601/100000000000000 : ℝ)^3593 := by
    have hnat : (52448693 : ℕ)^4617*100000000000000^3593 ≤ 43637457741601^3593*100000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52448693 100000000 43637457741601 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833481669/10000000000 : ℝ)^4617 ≤ (5653031753523/50000000000000 : ℝ)^3593 := by
    have hnat : (1833481669 : ℕ)^4617*50000000000000^3593 ≤ 5653031753523^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833481669 10000000000 5653031753523 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688562271/5000000000 : ℝ), (52448693/100000000 : ℝ), (-1833481669/10000000000 : ℝ)] ![(11264119684693/25000000000000 : ℝ), (43637457741601/100000000000000 : ℝ), (5653031753523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688562271/5000000000 : ℝ)|^4617 ≤ (11264119684693/25000000000000 : ℝ)^3593
        have hw : |(2688562271/5000000000 : ℝ)|=(2688562271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52448693/100000000 : ℝ)|^4617 ≤ (43637457741601/100000000000000 : ℝ)^3593
        have hw : |(52448693/100000000 : ℝ)|=(52448693/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833481669/10000000000 : ℝ)|^4617 ≤ (5653031753523/50000000000000 : ℝ)^3593
        have hw : |(-1833481669/10000000000 : ℝ)|=(1833481669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4044225093/10000000000 : ℝ)*x 0 + (68067909/156250000 : ℝ)*x 1 + (871269169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4044225093/10000000000 : ℝ)^4617 ≤ (6249048975291/20000000000000 : ℝ)^3593 := by
    have hnat : (4044225093 : ℕ)^4617*20000000000000^3593 ≤ 6249048975291^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4044225093 10000000000 6249048975291 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68067909/156250000 : ℝ)^4617 ≤ (34377379232477/100000000000000 : ℝ)^3593 := by
    have hnat : (68067909 : ℕ)^4617*100000000000000^3593 ≤ 34377379232477^3593*156250000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68067909 156250000 34377379232477 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (871269169/2000000000 : ℝ)^4617 ≤ (34377375876021/100000000000000 : ℝ)^3593 := by
    have hnat : (871269169 : ℕ)^4617*100000000000000^3593 ≤ 34377375876021^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871269169 2000000000 34377375876021 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4044225093/10000000000 : ℝ), (68067909/156250000 : ℝ), (871269169/2000000000 : ℝ)] ![(6249048975291/20000000000000 : ℝ), (34377379232477/100000000000000 : ℝ), (34377375876021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4044225093/10000000000 : ℝ)|^4617 ≤ (6249048975291/20000000000000 : ℝ)^3593
        have hw : |(4044225093/10000000000 : ℝ)|=(4044225093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68067909/156250000 : ℝ)|^4617 ≤ (34377379232477/100000000000000 : ℝ)^3593
        have hw : |(68067909/156250000 : ℝ)|=(68067909/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(871269169/2000000000 : ℝ)|^4617 ≤ (34377375876021/100000000000000 : ℝ)^3593
        have hw : |(871269169/2000000000 : ℝ)|=(871269169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_8 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-480500449/2500000000 : ℝ)*x 0 + (1284330763/2500000000 : ℝ)*x 1 + (1083593217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480500449/2500000000 : ℝ)^4617 ≤ (1501532126777/12500000000000 : ℝ)^3593 := by
    have hnat : (480500449 : ℕ)^4617*12500000000000^3593 ≤ 1501532126777^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480500449 2500000000 1501532126777 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284330763/2500000000 : ℝ)^4617 ≤ (21245516472713/50000000000000 : ℝ)^3593 := by
    have hnat : (1284330763 : ℕ)^4617*50000000000000^3593 ≤ 21245516472713^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284330763 2500000000 21245516472713 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083593217/2000000000 : ℝ)^4617 ≤ (22748355013189/50000000000000 : ℝ)^3593 := by
    have hnat : (1083593217 : ℕ)^4617*50000000000000^3593 ≤ 22748355013189^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083593217 2000000000 22748355013189 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-480500449/2500000000 : ℝ), (1284330763/2500000000 : ℝ), (1083593217/2000000000 : ℝ)] ![(1501532126777/12500000000000 : ℝ), (21245516472713/50000000000000 : ℝ), (22748355013189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-480500449/2500000000 : ℝ)|^4617 ≤ (1501532126777/12500000000000 : ℝ)^3593
        have hw : |(-480500449/2500000000 : ℝ)|=(480500449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284330763/2500000000 : ℝ)|^4617 ≤ (21245516472713/50000000000000 : ℝ)^3593
        have hw : |(1284330763/2500000000 : ℝ)|=(1284330763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083593217/2000000000 : ℝ)|^4617 ≤ (22748355013189/50000000000000 : ℝ)^3593
        have hw : |(1083593217/2000000000 : ℝ)|=(1083593217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_9 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628522527/5000000000 : ℝ)*x 0 + (-1761079393/10000000000 : ℝ)*x 1 + (5417966007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628522527/5000000000 : ℝ)^4617 ≤ (43767674493333/100000000000000 : ℝ)^3593 := by
    have hnat : (2628522527 : ℕ)^4617*100000000000000^3593 ≤ 43767674493333^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628522527 5000000000 43767674493333 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1761079393/10000000000 : ℝ)^4617 ≤ (10735616308669/100000000000000 : ℝ)^3593 := by
    have hnat : (1761079393 : ℕ)^4617*100000000000000^3593 ≤ 10735616308669^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761079393 10000000000 10735616308669 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417966007/10000000000 : ℝ)^4617 ≤ (45496709184709/100000000000000 : ℝ)^3593 := by
    have hnat : (5417966007 : ℕ)^4617*100000000000000^3593 ≤ 45496709184709^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417966007 10000000000 45496709184709 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628522527/5000000000 : ℝ), (-1761079393/10000000000 : ℝ), (5417966007/10000000000 : ℝ)] ![(43767674493333/100000000000000 : ℝ), (10735616308669/100000000000000 : ℝ), (45496709184709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628522527/5000000000 : ℝ)|^4617 ≤ (43767674493333/100000000000000 : ℝ)^3593
        have hw : |(2628522527/5000000000 : ℝ)|=(2628522527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1761079393/10000000000 : ℝ)|^4617 ≤ (10735616308669/100000000000000 : ℝ)^3593
        have hw : |(-1761079393/10000000000 : ℝ)|=(1761079393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417966007/10000000000 : ℝ)|^4617 ≤ (45496709184709/100000000000000 : ℝ)^3593
        have hw : |(5417966007/10000000000 : ℝ)|=(5417966007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_10 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257044737/10000000000 : ℝ)*x 0 + (5417967183/10000000000 : ℝ)*x 1 + (-880539103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257044737/10000000000 : ℝ)^4617 ≤ (21883835550987/50000000000000 : ℝ)^3593 := by
    have hnat : (5257044737 : ℕ)^4617*50000000000000^3593 ≤ 21883835550987^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257044737 10000000000 21883835550987 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417967183/10000000000 : ℝ)^4617 ≤ (22748360937239/50000000000000 : ℝ)^3593 := by
    have hnat : (5417967183 : ℕ)^4617*50000000000000^3593 ≤ 22748360937239^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417967183 10000000000 22748360937239 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880539103/5000000000 : ℝ)^4617 ≤ (670975438151/6250000000000 : ℝ)^3593 := by
    have hnat : (880539103 : ℕ)^4617*6250000000000^3593 ≤ 670975438151^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880539103 5000000000 670975438151 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257044737/10000000000 : ℝ), (5417967183/10000000000 : ℝ), (-880539103/5000000000 : ℝ)] ![(21883835550987/50000000000000 : ℝ), (22748360937239/50000000000000 : ℝ), (670975438151/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257044737/10000000000 : ℝ)|^4617 ≤ (21883835550987/50000000000000 : ℝ)^3593
        have hw : |(5257044737/10000000000 : ℝ)|=(5257044737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417967183/10000000000 : ℝ)|^4617 ≤ (22748360937239/50000000000000 : ℝ)^3593
        have hw : |(5417967183/10000000000 : ℝ)|=(5417967183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-880539103/5000000000 : ℝ)|^4617 ≤ (670975438151/6250000000000 : ℝ)^3593
        have hw : |(-880539103/5000000000 : ℝ)|=(880539103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_11 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1125407957/2500000000 : ℝ)*x 0 + (82543631/200000000 : ℝ)*x 1 + (2063590869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125407957/2500000000 : ℝ)^4617 ≤ (140068646507/390625000000 : ℝ)^3593 := by
    have hnat : (1125407957 : ℕ)^4617*390625000000^3593 ≤ 140068646507^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125407957 2500000000 140068646507 390625000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82543631/200000000 : ℝ)^4617 ≤ (6414242460187/20000000000000 : ℝ)^3593 := by
    have hnat : (82543631 : ℕ)^4617*20000000000000^3593 ≤ 6414242460187^3593*200000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82543631 200000000 6414242460187 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063590869/5000000000 : ℝ)^4617 ≤ (16035607089093/50000000000000 : ℝ)^3593 := by
    have hnat : (2063590869 : ℕ)^4617*50000000000000^3593 ≤ 16035607089093^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063590869 5000000000 16035607089093 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125407957/2500000000 : ℝ), (82543631/200000000 : ℝ), (2063590869/5000000000 : ℝ)] ![(140068646507/390625000000 : ℝ), (6414242460187/20000000000000 : ℝ), (16035607089093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125407957/2500000000 : ℝ)|^4617 ≤ (140068646507/390625000000 : ℝ)^3593
        have hw : |(1125407957/2500000000 : ℝ)|=(1125407957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82543631/200000000 : ℝ)|^4617 ≤ (6414242460187/20000000000000 : ℝ)^3593
        have hw : |(82543631/200000000 : ℝ)|=(82543631/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063590869/5000000000 : ℝ)|^4617 ≤ (16035607089093/50000000000000 : ℝ)^3593
        have hw : |(2063590869/5000000000 : ℝ)|=(2063590869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_12 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-840919953/5000000000 : ℝ)*x 0 + (137547589/250000000 : ℝ)*x 1 + (1307455181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840919953/5000000000 : ℝ)^4617 ≤ (10118924523257/100000000000000 : ℝ)^3593 := by
    have hnat : (840919953 : ℕ)^4617*100000000000000^3593 ≤ 10118924523257^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840919953 5000000000 10118924523257 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137547589/250000000 : ℝ)^4617 ≤ (725069368521/1562500000000 : ℝ)^3593 := by
    have hnat : (137547589 : ℕ)^4617*1562500000000^3593 ≤ 725069368521^3593*250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137547589 250000000 725069368521 1562500000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307455181/2500000000 : ℝ)^4617 ≤ (21738317935149/50000000000000 : ℝ)^3593 := by
    have hnat : (1307455181 : ℕ)^4617*50000000000000^3593 ≤ 21738317935149^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307455181 2500000000 21738317935149 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-840919953/5000000000 : ℝ), (137547589/250000000 : ℝ), (1307455181/2500000000 : ℝ)] ![(10118924523257/100000000000000 : ℝ), (725069368521/1562500000000 : ℝ), (21738317935149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-840919953/5000000000 : ℝ)|^4617 ≤ (10118924523257/100000000000000 : ℝ)^3593
        have hw : |(-840919953/5000000000 : ℝ)|=(840919953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137547589/250000000 : ℝ)|^4617 ≤ (725069368521/1562500000000 : ℝ)^3593
        have hw : |(137547589/250000000 : ℝ)|=(137547589/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307455181/2500000000 : ℝ)|^4617 ≤ (21738317935149/50000000000000 : ℝ)^3593
        have hw : |(1307455181/2500000000 : ℝ)|=(1307455181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_13 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387564529/10000000000 : ℝ)*x 0 + (-459896157/2500000000 : ℝ)*x 1 + (1045964099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387564529/10000000000 : ℝ)^4617 ≤ (45168921072729/100000000000000 : ℝ)^3593 := by
    have hnat : (5387564529 : ℕ)^4617*100000000000000^3593 ≤ 45168921072729^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387564529 10000000000 45168921072729 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459896157/2500000000 : ℝ)^4617 ≤ (5677222749399/50000000000000 : ℝ)^3593 := by
    have hnat : (459896157 : ℕ)^4617*50000000000000^3593 ≤ 5677222749399^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459896157 2500000000 5677222749399 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045964099/2000000000 : ℝ)^4617 ≤ (10869158356003/25000000000000 : ℝ)^3593 := by
    have hnat : (1045964099 : ℕ)^4617*25000000000000^3593 ≤ 10869158356003^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045964099 2000000000 10869158356003 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387564529/10000000000 : ℝ), (-459896157/2500000000 : ℝ), (1045964099/2000000000 : ℝ)] ![(45168921072729/100000000000000 : ℝ), (5677222749399/50000000000000 : ℝ), (10869158356003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387564529/10000000000 : ℝ)|^4617 ≤ (45168921072729/100000000000000 : ℝ)^3593
        have hw : |(5387564529/10000000000 : ℝ)|=(5387564529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-459896157/2500000000 : ℝ)|^4617 ≤ (5677222749399/50000000000000 : ℝ)^3593
        have hw : |(-459896157/2500000000 : ℝ)|=(459896157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045964099/2000000000 : ℝ)|^4617 ≤ (10869158356003/25000000000000 : ℝ)^3593
        have hw : |(1045964099/2000000000 : ℝ)|=(1045964099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_14 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387565917/10000000000 : ℝ)*x 0 + (2614909663/5000000000 : ℝ)*x 1 + (-367916863/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387565917/10000000000 : ℝ)^4617 ≤ (4516893602611/10000000000000 : ℝ)^3593 := by
    have hnat : (5387565917 : ℕ)^4617*10000000000000^3593 ≤ 4516893602611^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387565917 10000000000 4516893602611 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614909663/5000000000 : ℝ)^4617 ≤ (21738310468101/50000000000000 : ℝ)^3593 := by
    have hnat : (2614909663 : ℕ)^4617*50000000000000^3593 ≤ 21738310468101^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614909663 5000000000 21738310468101 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367916863/2000000000 : ℝ)^4617 ≤ (2838610754069/25000000000000 : ℝ)^3593 := by
    have hnat : (367916863 : ℕ)^4617*25000000000000^3593 ≤ 2838610754069^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367916863 2000000000 2838610754069 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387565917/10000000000 : ℝ), (2614909663/5000000000 : ℝ), (-367916863/2000000000 : ℝ)] ![(4516893602611/10000000000000 : ℝ), (21738310468101/50000000000000 : ℝ), (2838610754069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387565917/10000000000 : ℝ)|^4617 ≤ (4516893602611/10000000000000 : ℝ)^3593
        have hw : |(5387565917/10000000000 : ℝ)|=(5387565917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614909663/5000000000 : ℝ)|^4617 ≤ (21738310468101/50000000000000 : ℝ)^3593
        have hw : |(2614909663/5000000000 : ℝ)|=(2614909663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367916863/2000000000 : ℝ)|^4617 ≤ (2838610754069/25000000000000 : ℝ)^3593
        have hw : |(-367916863/2000000000 : ℝ)|=(367916863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_box_15 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (400349689/1000000000 : ℝ)*x 0 + (1094060509/2500000000 : ℝ)*x 1 + (875248219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400349689/1000000000 : ℝ)^4617 ≤ (7710371676311/25000000000000 : ℝ)^3593 := by
    have hnat : (400349689 : ℕ)^4617*25000000000000^3593 ≤ 7710371676311^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400349689 1000000000 7710371676311 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094060509/2500000000 : ℝ)^4617 ≤ (17289630709273/50000000000000 : ℝ)^3593 := by
    have hnat : (1094060509 : ℕ)^4617*50000000000000^3593 ≤ 17289630709273^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094060509 2500000000 17289630709273 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875248219/2000000000 : ℝ)^4617 ≤ (1383170074563/4000000000000 : ℝ)^3593 := by
    have hnat : (875248219 : ℕ)^4617*4000000000000^3593 ≤ 1383170074563^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875248219 2000000000 1383170074563 4000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(400349689/1000000000 : ℝ), (1094060509/2500000000 : ℝ), (875248219/2000000000 : ℝ)] ![(7710371676311/25000000000000 : ℝ), (17289630709273/50000000000000 : ℝ), (1383170074563/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(400349689/1000000000 : ℝ)|^4617 ≤ (7710371676311/25000000000000 : ℝ)^3593
        have hw : |(400349689/1000000000 : ℝ)|=(400349689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094060509/2500000000 : ℝ)|^4617 ≤ (17289630709273/50000000000000 : ℝ)^3593
        have hw : |(1094060509/2500000000 : ℝ)|=(1094060509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875248219/2000000000 : ℝ)|^4617 ≤ (1383170074563/4000000000000 : ℝ)^3593
        have hw : |(875248219/2000000000 : ℝ)|=(875248219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63811/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11771/20000 : ℝ) ∧ (4041/5000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17261/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11089/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11089/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11089/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11089/100000 : ℝ) ^ (4615/1024 : ℝ) ≤ (4960057026457651/100000000000000000000 : ℝ) := by
    have hpowers : (11089/100000 : ℝ)^4615 ≤ (4960057026457651/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11089 : ℕ)^4615*100000000000000000000^1024 ≤ 4960057026457651^1024*100000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11089 100000 4960057026457651 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11089/100000 : ℝ)) (X := (4960057026457651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4615/1024 : ℝ) ≤ (1396184282435981/6250000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4615 ≤ (1396184282435981/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4615*6250000000000000000^1024 ≤ 1396184282435981^1024*20000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 1396184282435981 6250000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (1396184282435981/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004960057026457651/50000000000000000000 : ℝ) ≤ (2500055026027943/2500000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50004960057026457651/50000000000000000000 : ℝ)^1024 ≤ (2500055026027943/2500000000000000 : ℝ)^4615 := by
      have hnat : (50004960057026457651 : ℕ)^1024*2500000000000000^4615 ≤ 2500055026027943^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004960057026457651 50000000000000000000 2500055026027943 2500000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500055026027943/2500000000000000 : ℝ)) (X := (50004960057026457651/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027299005545433347/100000000000000000000 : ℝ) ≤ (10000605660090543/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (100027299005545433347/100000000000000000000 : ℝ)^1024 ≤ (10000605660090543/10000000000000000 : ℝ)^4615 := by
      have hnat : (100027299005545433347 : ℕ)^1024*10000000000000000^4615 ≤ 10000605660090543^4615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027299005545433347 100000000000000000000 10000605660090543 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000605660090543/10000000000000000 : ℝ)) (X := (100027299005545433347/100000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126396184282435981/3125000000000000000 : ℝ) ≤ (5000495608034657/5000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (3126396184282435981/3125000000000000000 : ℝ)^1024 ≤ (5000495608034657/5000000000000000 : ℝ)^4615 := by
      have hnat : (3126396184282435981 : ℕ)^1024*5000000000000000^4615 ≤ 5000495608034657^4615*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126396184282435981 3125000000000000000 5000495608034657 5000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000495608034657/5000000000000000 : ℝ)) (X := (3126396184282435981/3125000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4960057026457651/100000000000000000000 : ℝ) ≤ ((21976208358589083237/21980000000000000000 : ℝ)+2*(385555978771/439600000000000 : ℝ)*(11089/100000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (21976208358589083237/21980000000000000000 : ℝ)+2*(385555978771/439600000000000 : ℝ)*(11089/100000 : ℝ)=(2500055026027943/2500000000000000 : ℝ) by norm_num, show 1+2*(4960057026457651/100000000000000000000 : ℝ)=(50004960057026457651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1396184282435981/6250000000000000000 : ℝ)+(4960057026457651/100000000000000000000 : ℝ) ≤ ((21976208358589083237/21980000000000000000 : ℝ)+(385555978771/439600000000000 : ℝ)*((3097/20000 : ℝ)+(11089/100000 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (21976208358589083237/21980000000000000000 : ℝ)+(385555978771/439600000000000 : ℝ)*((3097/20000 : ℝ)+(11089/100000 : ℝ))=(10000605660090543/10000000000000000 : ℝ) by norm_num, show 1+(1396184282435981/6250000000000000000 : ℝ)+(4960057026457651/100000000000000000000 : ℝ)=(100027299005545433347/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1396184282435981/6250000000000000000 : ℝ) ≤ ((21976208358589083237/21980000000000000000 : ℝ)+2*(385555978771/439600000000000 : ℝ)*(3097/20000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (21976208358589083237/21980000000000000000 : ℝ)+2*(385555978771/439600000000000 : ℝ)*(3097/20000 : ℝ)=(5000495608034657/5000000000000000 : ℝ) by norm_num, show 1+2*(1396184282435981/6250000000000000000 : ℝ)=(3126396184282435981/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21976208358589083237/21980000000000000000 : ℝ)*(X 1 0+X 2 0)+(385555978771/439600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21976208358589083237/21980000000000000000 : ℝ)) (alpha := (385555978771/439600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21976208358589083237/21980000000000000000 : ℝ)*(X 0 1+X 2 1)+(385555978771/439600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21976208358589083237/21980000000000000000 : ℝ)) (alpha := (385555978771/439600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21976208358589083237/21980000000000000000 : ℝ)*(X 0 2+X 1 2)+(385555978771/439600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (11089/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (21976208358589083237/21980000000000000000 : ℝ)) (alpha := (385555978771/439600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-796971971/5000000000 : ℝ)*X 0 0+(5397663463/10000000000 : ℝ)*X 0 1+(5397663601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054226591/2000000000 : ℝ)*X 1 0+(-884889133/5000000000 : ℝ)*X 1 1+(5397663113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635565869/5000000000 : ℝ)*X 2 0+(2698832083/5000000000 : ℝ)*X 2 1+(-1769778479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((111224809/250000000 : ℝ)*X 0 0+(830818199/2000000000 : ℝ)*X 0 1+(4154090797/10000000000 : ℝ)*X 0 2+(111224809/250000000 : ℝ)*X 1 0+(830818199/2000000000 : ℝ)*X 1 1+(4154090797/10000000000 : ℝ)*X 1 2+(111224809/250000000 : ℝ)*X 2 0+(830818199/2000000000 : ℝ)*X 2 1+(4154090797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-402037927/2000000000 : ℝ)*X 0 0+(2622434503/5000000000 : ℝ)*X 0 1+(524486993/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5377124919/10000000000 : ℝ)*X 1 0+(-366696299/2000000000 : ℝ)*X 1 1+(104897381/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2688562271/5000000000 : ℝ)*X 2 0+(52448693/100000000 : ℝ)*X 2 1+(-1833481669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4044225093/10000000000 : ℝ)*X 0 0+(68067909/156250000 : ℝ)*X 0 1+(871269169/2000000000 : ℝ)*X 0 2+(4044225093/10000000000 : ℝ)*X 1 0+(68067909/156250000 : ℝ)*X 1 1+(871269169/2000000000 : ℝ)*X 1 2+(4044225093/10000000000 : ℝ)*X 2 0+(68067909/156250000 : ℝ)*X 2 1+(871269169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-480500449/2500000000 : ℝ)*X 0 0+(1284330763/2500000000 : ℝ)*X 0 1+(1083593217/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628522527/5000000000 : ℝ)*X 1 0+(-1761079393/10000000000 : ℝ)*X 1 1+(5417966007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257044737/10000000000 : ℝ)*X 2 0+(5417967183/10000000000 : ℝ)*X 2 1+(-880539103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1125407957/2500000000 : ℝ)*X 0 0+(82543631/200000000 : ℝ)*X 0 1+(2063590869/5000000000 : ℝ)*X 0 2+(1125407957/2500000000 : ℝ)*X 1 0+(82543631/200000000 : ℝ)*X 1 1+(2063590869/5000000000 : ℝ)*X 1 2+(1125407957/2500000000 : ℝ)*X 2 0+(82543631/200000000 : ℝ)*X 2 1+(2063590869/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-840919953/5000000000 : ℝ)*X 0 0+(137547589/250000000 : ℝ)*X 0 1+(1307455181/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5387564529/10000000000 : ℝ)*X 1 0+(-459896157/2500000000 : ℝ)*X 1 1+(1045964099/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5387565917/10000000000 : ℝ)*X 2 0+(2614909663/5000000000 : ℝ)*X 2 1+(-367916863/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((400349689/1000000000 : ℝ)*X 0 0+(1094060509/2500000000 : ℝ)*X 0 1+(875248219/2000000000 : ℝ)*X 0 2+(400349689/1000000000 : ℝ)*X 1 0+(1094060509/2500000000 : ℝ)*X 1 1+(875248219/2000000000 : ℝ)*X 1 2+(400349689/1000000000 : ℝ)*X 2 0+(1094060509/2500000000 : ℝ)*X 2 1+(875248219/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63811/100000 : ℝ) ≤ (-701259714831529206951085683638763/1099000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30201991/25000000000000 : ℝ)*(upper1) + (62791643/50000000000000 : ℝ)*(lower4) + (5308839/25000000000000 : ℝ)*(upper5) + (2293415456635333/100000000000000 : ℝ)*(major0) + (2293415456635333/100000000000000 : ℝ)*(major1) + (2293415456635333/100000000000000 : ℝ)*(major2) + (4927282439/50000000000000 : ℝ)*(sp1) + (10190538537/100000000000000 : ℝ)*(sp2) + (1122274197/50000000000000 : ℝ)*(sp3) + (323663242880833/10000000000000 : ℝ)*(sp4) + (1618315753993857/50000000000000 : ℝ)*(sp5) + (1618315586007027/50000000000000 : ℝ)*(sp6) + (17143211707327/1250000000000 : ℝ)*(sp7) + (8933744261/100000000000000 : ℝ)*(sp12) + (685729590567277/50000000000000 : ℝ)*(f.failure) + (3236641362552591/100000000000000 : ℝ)*(f.sum) + (8471948098177/21980000000000000000000000000 : ℝ)*base66 + (3303809339539362921/2198000000000000000000000000000000 : ℝ)*base67 + (11576879668643362921/2198000000000000000000000000000000 : ℝ)*base69 + (3757610847568637079/2198000000000000000000000000000000 : ℝ)*base72 + (43816306695983/21980000000000000000000000000 : ℝ)*base73 + (12030552611256637079/2198000000000000000000000000000000 : ℝ)*base76 + (11807524134667362921/2198000000000000000000000000000000 : ℝ)*base77 + (5187455331543362921/2198000000000000000000000000000000 : ℝ)*base79 + (40256570324877/21980000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14896797/2500000000000000000000 : ℝ)*base90 + (14896797/2500000000000000000000 : ℝ)*base92 + (14896797/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11771/20000 : ℝ) ≤ (323421096417140834248446850975173/549500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1982641/6250000000000 : ℝ)*(lower0) + (126886869/100000000000000 : ℝ)*(upper1) + (141556681/50000000000000 : ℝ)*(upper2) + (11680673/100000000000000 : ℝ)*(upper3) + (2372945137973357/100000000000000 : ℝ)*(major0) + (2372945137973357/100000000000000 : ℝ)*(major1) + (2372945137973357/100000000000000 : ℝ)*(major2) + (3307250592512821/100000000000000 : ℝ)*(sp0) + (413406668044793/12500000000000 : ℝ)*(sp1) + (330724208138897/10000000000000 : ℝ)*(sp2) + (7095073816773/500000000000 : ℝ)*(sp3) + (18020751/160000000000 : ℝ)*(sp6) + (3054104729/100000000000000 : ℝ)*(sp7) + (2751845523/100000000000000 : ℝ)*(sp12) + (141901781745933/10000000000000 : ℝ)*(f.failure) + (413406668044793/12500000000000 : ℝ)*(f.sum) + (15134934901787/21980000000000000000000000000 : ℝ)*base65 + (15412902896187666609/2198000000000000000000000000000000 : ℝ)*base67 + (511232259929666609/2198000000000000000000000000000000 : ℝ)*base69 + (16092891540207666609/2198000000000000000000000000000000 : ℝ)*base71 + (48455686840247/21980000000000000000000000000 : ℝ)*base73 + (5801779137727666609/2198000000000000000000000000000000 : ℝ)*base75 + (7226579748612333391/2198000000000000000000000000000000 : ℝ)*base78 + (2620948389821666609/2198000000000000000000000000000000 : ℝ)*base79 + (34391590721753/21980000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2273987/500000000000000000000 : ℝ)*base89 + (2273987/500000000000000000000 : ℝ)*base91 + (2273987/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (4041/5000 : ℝ) ≤ (177646931420004560936905272109851/219800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (338081917/100000000000000 : ℝ)*(lower3) + (6222551/3125000000000 : ℝ)*(upper4) + (9889407/12500000000000 : ℝ)*(lower5) + (512156921921753/20000000000000 : ℝ)*(major0) + (512156921921753/20000000000000 : ℝ)*(major1) + (512156921921753/20000000000000 : ℝ)*(major2) + (13617379951/50000000000000 : ℝ)*(sp0) + (180063806283/100000000000000 : ℝ)*(sp1) + (401611251281/100000000000000 : ℝ)*(sp2) + (87955133351/50000000000000 : ℝ)*(sp3) + (3563255736855461/100000000000000 : ℝ)*(sp8) + (3563102907809079/100000000000000 : ℝ)*(sp9) + (3562881360364081/100000000000000 : ℝ)*(sp10) + (1531169644065819/100000000000000 : ℝ)*(sp11) + (1531345554332521/100000000000000 : ℝ)*(f.failure) + (1781641485807681/50000000000000 : ℝ)*(f.sum) + (13533780821611/4396000000000000000000000000 : ℝ)*base65 + (2533459329291304461/439600000000000000000000000000000 : ℝ)*base67 + (2458205671357304461/439600000000000000000000000000000 : ℝ)*base69 + (1413468497429304461/439600000000000000000000000000000 : ℝ)*base71 + (7158387734023/4396000000000000000000000000 : ℝ)*base73 + (3447327983255304461/439600000000000000000000000000000 : ℝ)*base75 + (1498510636686904461/439600000000000000000000000000000 : ℝ)*base77 + (3731368067199704461/439600000000000000000000000000000 : ℝ)*base79 + (20807435747687/4396000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18675481/5000000000000000000000 : ℝ)*base90 + (18675481/5000000000000000000000 : ℝ)*base92 + (18675481/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-17261/20000 : ℝ) ≤ (-237115145546282080452475583584827/274750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173577369/50000000000000 : ℝ)*(lower2) + (141541983/100000000000000 : ℝ)*(upper3) + (102722731/50000000000000 : ℝ)*(upper5) + (1300491030066643/50000000000000 : ℝ)*(major0) + (1300491030066643/50000000000000 : ℝ)*(major1) + (1300491030066643/50000000000000 : ℝ)*(major2) + (6154485607/100000000000000 : ℝ)*(sp0) + (218629701003/100000000000000 : ℝ)*(sp5) + (187343350587/50000000000000 : ℝ)*(sp6) + (20764147847/100000000000000 : ℝ)*(sp7) + (1837670887568167/50000000000000 : ℝ)*(sp12) + (1837564649960469/50000000000000 : ℝ)*(sp13) + (3674973242920767/100000000000000 : ℝ)*(sp14) + (777681404212677/50000000000000 : ℝ)*(sp15) + (1555383572573201/100000000000000 : ℝ)*(f.failure) + (3675347929621941/100000000000000 : ℝ)*(f.sum) + (71951328662917/10990000000000000000000000000 : ℝ)*base66 + (10991148418631186609/1099000000000000000000000000000000 : ℝ)*base68 + (639837758339813391/1099000000000000000000000000000000 : ℝ)*base69 + (4796399615038186609/1099000000000000000000000000000000 : ℝ)*base72 + (84662327868577/10990000000000000000000000000 : ℝ)*base74 + (3272387757523186609/1099000000000000000000000000000000 : ℝ)*base76 + (9997426663150186609/1099000000000000000000000000000000 : ℝ)*base78 + (6316744420570186609/1099000000000000000000000000000000 : ℝ)*base80 + (8624791755093/10990000000000000000000000000 : ℝ)*base81 + (27007039/5000000000000000000000 : ℝ)*base89 + (27007039/5000000000000000000000 : ℝ)*base91 + (27007039/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1560_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11089/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63811/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11771/20000 : ℝ) else (4041/5000 : ℝ) ≤ X j i ∧ X j i ≤ (17261/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1560_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1560_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63811/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11771/20000 : ℝ) else (4041/5000 : ℝ) ≤ X j i ∧ X j i ≤ (17261/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1560_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1560_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63811/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11771/20000 : ℝ) else (4041/5000 : ℝ) ≤ X j i ∧ X j i ≤ (17261/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1560_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

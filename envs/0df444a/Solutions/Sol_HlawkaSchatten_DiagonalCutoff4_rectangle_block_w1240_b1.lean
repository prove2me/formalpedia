-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1240_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:18:44.254718+00:00
-- url     : https://prove2.me/submissions/f6971695-89e0-4acd-99fb-dc4a458f9ff6

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
theorem support_rectangle_w1240_s3_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529505883/2500000000 : ℝ)*x 0 + (5419832503/10000000000 : ℝ)*x 1 + (1310116297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529505883/2500000000 : ℝ)^8433 ≤ (12874248607341/100000000000000 : ℝ)^6385 := by
    have hnat : (529505883 : ℕ)^8433*100000000000000^6385 ≤ 12874248607341^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529505883 2500000000 12874248607341 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419832503/10000000000 : ℝ)^8433 ≤ (44530888724339/100000000000000 : ℝ)^6385 := by
    have hnat : (5419832503 : ℕ)^8433*100000000000000^6385 ≤ 44530888724339^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419832503 10000000000 44530888724339 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310116297/2500000000 : ℝ)^8433 ≤ (8518972530217/20000000000000 : ℝ)^6385 := by
    have hnat : (1310116297 : ℕ)^8433*20000000000000^6385 ≤ 8518972530217^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310116297 2500000000 8518972530217 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529505883/2500000000 : ℝ), (5419832503/10000000000 : ℝ), (1310116297/2500000000 : ℝ)] ![(12874248607341/100000000000000 : ℝ), (44530888724339/100000000000000 : ℝ), (8518972530217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529505883/2500000000 : ℝ)|^8433 ≤ (12874248607341/100000000000000 : ℝ)^6385
        have hw : |(-529505883/2500000000 : ℝ)|=(529505883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419832503/10000000000 : ℝ)|^8433 ≤ (44530888724339/100000000000000 : ℝ)^6385
        have hw : |(5419832503/10000000000 : ℝ)|=(5419832503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310116297/2500000000 : ℝ)|^8433 ≤ (8518972530217/20000000000000 : ℝ)^6385
        have hw : |(1310116297/2500000000 : ℝ)|=(1310116297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351533379/10000000000 : ℝ)*x 0 + (-138095569/625000000 : ℝ)*x 1 + (5240465319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351533379/10000000000 : ℝ)^8433 ≤ (8758246231119/20000000000000 : ℝ)^6385 := by
    have hnat : (5351533379 : ℕ)^8433*20000000000000^6385 ≤ 8758246231119^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351533379 10000000000 8758246231119 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138095569/625000000 : ℝ)^8433 ≤ (13613904772371/100000000000000 : ℝ)^6385 := by
    have hnat : (138095569 : ℕ)^8433*100000000000000^6385 ≤ 13613904772371^6385*625000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138095569 625000000 13613904772371 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240465319/10000000000 : ℝ)^8433 ≤ (2662179003587/6250000000000 : ℝ)^6385 := by
    have hnat : (5240465319 : ℕ)^8433*6250000000000^6385 ≤ 2662179003587^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240465319 10000000000 2662179003587 6250000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351533379/10000000000 : ℝ), (-138095569/625000000 : ℝ), (5240465319/10000000000 : ℝ)] ![(8758246231119/20000000000000 : ℝ), (13613904772371/100000000000000 : ℝ), (2662179003587/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351533379/10000000000 : ℝ)|^8433 ≤ (8758246231119/20000000000000 : ℝ)^6385
        have hw : |(5351533379/10000000000 : ℝ)|=(5351533379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-138095569/625000000 : ℝ)|^8433 ≤ (13613904772371/100000000000000 : ℝ)^6385
        have hw : |(-138095569/625000000 : ℝ)|=(138095569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240465319/10000000000 : ℝ)|^8433 ≤ (2662179003587/6250000000000 : ℝ)^6385
        have hw : |(5240465319/10000000000 : ℝ)|=(5240465319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2675766647/5000000000 : ℝ)*x 0 + (5240465749/10000000000 : ℝ)*x 1 + (-44190573/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675766647/5000000000 : ℝ)^8433 ≤ (43791230236947/100000000000000 : ℝ)^6385 := by
    have hnat : (2675766647 : ℕ)^8433*100000000000000^6385 ≤ 43791230236947^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675766647 5000000000 43791230236947 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240465749/10000000000 : ℝ)^8433 ≤ (42594868673511/100000000000000 : ℝ)^6385 := by
    have hnat : (5240465749 : ℕ)^8433*100000000000000^6385 ≤ 42594868673511^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240465749 10000000000 42594868673511 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44190573/200000000 : ℝ)^8433 ≤ (6806950538917/50000000000000 : ℝ)^6385 := by
    have hnat : (44190573 : ℕ)^8433*50000000000000^6385 ≤ 6806950538917^6385*200000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44190573 200000000 6806950538917 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675766647/5000000000 : ℝ), (5240465749/10000000000 : ℝ), (-44190573/200000000 : ℝ)] ![(43791230236947/100000000000000 : ℝ), (42594868673511/100000000000000 : ℝ), (6806950538917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675766647/5000000000 : ℝ)|^8433 ≤ (43791230236947/100000000000000 : ℝ)^6385
        have hw : |(2675766647/5000000000 : ℝ)|=(2675766647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240465749/10000000000 : ℝ)|^8433 ≤ (42594868673511/100000000000000 : ℝ)^6385
        have hw : |(5240465749/10000000000 : ℝ)|=(5240465749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44190573/200000000 : ℝ)|^8433 ≤ (6806950538917/50000000000000 : ℝ)^6385
        have hw : |(-44190573/200000000 : ℝ)|=(44190573/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349339289/10000000000 : ℝ)*x 0 + (1042793767/2500000000 : ℝ)*x 1 + (4534892431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349339289/10000000000 : ℝ)^8433 ≤ (16650103016469/50000000000000 : ℝ)^6385 := by
    have hnat : (4349339289 : ℕ)^8433*50000000000000^6385 ≤ 16650103016469^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349339289 10000000000 16650103016469 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042793767/2500000000 : ℝ)^8433 ≤ (1575526240503/5000000000000 : ℝ)^6385 := by
    have hnat : (1042793767 : ℕ)^8433*5000000000000^6385 ≤ 1575526240503^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042793767 2500000000 1575526240503 5000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4534892431/10000000000 : ℝ)^8433 ≤ (17594634567553/50000000000000 : ℝ)^6385 := by
    have hnat : (4534892431 : ℕ)^8433*50000000000000^6385 ≤ 17594634567553^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534892431 10000000000 17594634567553 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349339289/10000000000 : ℝ), (1042793767/2500000000 : ℝ), (4534892431/10000000000 : ℝ)] ![(16650103016469/50000000000000 : ℝ), (1575526240503/5000000000000 : ℝ), (17594634567553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349339289/10000000000 : ℝ)|^8433 ≤ (16650103016469/50000000000000 : ℝ)^6385
        have hw : |(4349339289/10000000000 : ℝ)|=(4349339289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042793767/2500000000 : ℝ)|^8433 ≤ (1575526240503/5000000000000 : ℝ)^6385
        have hw : |(1042793767/2500000000 : ℝ)|=(1042793767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4534892431/10000000000 : ℝ)|^8433 ≤ (17594634567553/50000000000000 : ℝ)^6385
        have hw : |(4534892431/10000000000 : ℝ)|=(4534892431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059019071/5000000000 : ℝ)*x 0 + (1310279493/2500000000 : ℝ)*x 1 + (2709587947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059019071/5000000000 : ℝ)^8433 ≤ (12874365897887/100000000000000 : ℝ)^6385 := by
    have hnat : (1059019071 : ℕ)^8433*100000000000000^6385 ≤ 12874365897887^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059019071 5000000000 12874365897887 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310279493/2500000000 : ℝ)^8433 ≤ (21300935266357/50000000000000 : ℝ)^6385 := by
    have hnat : (1310279493 : ℕ)^8433*50000000000000^6385 ≤ 21300935266357^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310279493 2500000000 21300935266357 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709587947/5000000000 : ℝ)^8433 ≤ (22261881778331/50000000000000 : ℝ)^6385 := by
    have hnat : (2709587947 : ℕ)^8433*50000000000000^6385 ≤ 22261881778331^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709587947 5000000000 22261881778331 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059019071/5000000000 : ℝ), (1310279493/2500000000 : ℝ), (2709587947/5000000000 : ℝ)] ![(12874365897887/100000000000000 : ℝ), (21300935266357/50000000000000 : ℝ), (22261881778331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059019071/5000000000 : ℝ)|^8433 ≤ (12874365897887/100000000000000 : ℝ)^6385
        have hw : |(-1059019071/5000000000 : ℝ)|=(1059019071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310279493/2500000000 : ℝ)|^8433 ≤ (21300935266357/50000000000000 : ℝ)^6385
        have hw : |(1310279493/2500000000 : ℝ)|=(1310279493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709587947/5000000000 : ℝ)|^8433 ≤ (22261881778331/50000000000000 : ℝ)^6385
        have hw : |(2709587947/5000000000 : ℝ)|=(2709587947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265288951/500000000 : ℝ)*x 0 + (-253852269/1250000000 : ℝ)*x 1 + (5419175817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265288951/500000000 : ℝ)^8433 ≤ (43297414732533/100000000000000 : ℝ)^6385 := by
    have hnat : (265288951 : ℕ)^8433*100000000000000^6385 ≤ 43297414732533^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265288951 500000000 43297414732533 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253852269/1250000000 : ℝ)^8433 ≤ (12178822523343/100000000000000 : ℝ)^6385 := by
    have hnat : (253852269 : ℕ)^8433*100000000000000^6385 ≤ 12178822523343^6385*1250000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253852269 1250000000 12178822523343 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419175817/10000000000 : ℝ)^8433 ≤ (11130940680279/25000000000000 : ℝ)^6385 := by
    have hnat : (5419175817 : ℕ)^8433*25000000000000^6385 ≤ 11130940680279^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419175817 10000000000 11130940680279 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265288951/500000000 : ℝ), (-253852269/1250000000 : ℝ), (5419175817/10000000000 : ℝ)] ![(43297414732533/100000000000000 : ℝ), (12178822523343/100000000000000 : ℝ), (11130940680279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265288951/500000000 : ℝ)|^8433 ≤ (43297414732533/100000000000000 : ℝ)^6385
        have hw : |(265288951/500000000 : ℝ)|=(265288951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253852269/1250000000 : ℝ)|^8433 ≤ (12178822523343/100000000000000 : ℝ)^6385
        have hw : |(-253852269/1250000000 : ℝ)|=(253852269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419175817/10000000000 : ℝ)|^8433 ≤ (11130940680279/25000000000000 : ℝ)^6385
        have hw : |(5419175817/10000000000 : ℝ)|=(5419175817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652889337/5000000000 : ℝ)*x 0 + (2709588059/5000000000 : ℝ)*x 1 + (-507704553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652889337/5000000000 : ℝ)^8433 ≤ (43297411003381/100000000000000 : ℝ)^6385 := by
    have hnat : (2652889337 : ℕ)^8433*100000000000000^6385 ≤ 43297411003381^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652889337 5000000000 43297411003381 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709588059/5000000000 : ℝ)^8433 ≤ (44523765987343/100000000000000 : ℝ)^6385 := by
    have hnat : (2709588059 : ℕ)^8433*100000000000000^6385 ≤ 44523765987343^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709588059 5000000000 44523765987343 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507704553/2500000000 : ℝ)^8433 ≤ (12178822998577/100000000000000 : ℝ)^6385 := by
    have hnat : (507704553 : ℕ)^8433*100000000000000^6385 ≤ 12178822998577^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507704553 2500000000 12178822998577 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652889337/5000000000 : ℝ), (2709588059/5000000000 : ℝ), (-507704553/2500000000 : ℝ)] ![(43297411003381/100000000000000 : ℝ), (44523765987343/100000000000000 : ℝ), (12178822998577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652889337/5000000000 : ℝ)|^8433 ≤ (43297411003381/100000000000000 : ℝ)^6385
        have hw : |(2652889337/5000000000 : ℝ)|=(2652889337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709588059/5000000000 : ℝ)|^8433 ≤ (44523765987343/100000000000000 : ℝ)^6385
        have hw : |(2709588059/5000000000 : ℝ)|=(2709588059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507704553/2500000000 : ℝ)|^8433 ≤ (12178822998577/100000000000000 : ℝ)^6385
        have hw : |(-507704553/2500000000 : ℝ)|=(507704553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s3_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349367827/10000000000 : ℝ)*x 0 + (4533569101/10000000000 : ℝ)*x 1 + (417250531/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349367827/10000000000 : ℝ)^8433 ≤ (33300494614661/100000000000000 : ℝ)^6385 := by
    have hnat : (4349367827 : ℕ)^8433*100000000000000^6385 ≤ 33300494614661^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349367827 10000000000 33300494614661 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533569101/10000000000 : ℝ)^8433 ≤ (35175707492747/100000000000000 : ℝ)^6385 := by
    have hnat : (4533569101 : ℕ)^8433*100000000000000^6385 ≤ 35175707492747^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533569101 10000000000 35175707492747 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417250531/1000000000 : ℝ)^8433 ≤ (6304759575391/20000000000000 : ℝ)^6385 := by
    have hnat : (417250531 : ℕ)^8433*20000000000000^6385 ≤ 6304759575391^6385*1000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417250531 1000000000 6304759575391 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349367827/10000000000 : ℝ), (4533569101/10000000000 : ℝ), (417250531/1000000000 : ℝ)] ![(33300494614661/100000000000000 : ℝ), (35175707492747/100000000000000 : ℝ), (6304759575391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349367827/10000000000 : ℝ)|^8433 ≤ (33300494614661/100000000000000 : ℝ)^6385
        have hw : |(4349367827/10000000000 : ℝ)|=(4349367827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533569101/10000000000 : ℝ)|^8433 ≤ (35175707492747/100000000000000 : ℝ)^6385
        have hw : |(4533569101/10000000000 : ℝ)|=(4533569101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417250531/1000000000 : ℝ)|^8433 ≤ (6304759575391/20000000000000 : ℝ)^6385
        have hw : |(417250531/1000000000 : ℝ)|=(417250531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5453/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14703/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4057/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4057/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9491/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4057/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4057/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9491/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4057/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4057/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9491/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9491/100000 : ℝ) ^ (527/128 : ℝ) ≤ (1539365146059709/25000000000000000000 : ℝ) := by
    have hpowers : (9491/100000 : ℝ)^527 ≤ (1539365146059709/25000000000000000000 : ℝ)^128 := by
      have hnat : (9491 : ℕ)^527*25000000000000000000^128 ≤ 1539365146059709^128*100000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9491 100000 1539365146059709 25000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9491/100000 : ℝ)) (X := (1539365146059709/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (4057/25000 : ℝ) ^ (527/128 : ℝ) ≤ (56041909660705909/100000000000000000000 : ℝ) := by
    have hpowers : (4057/25000 : ℝ)^527 ≤ (56041909660705909/100000000000000000000 : ℝ)^128 := by
      have hnat : (4057 : ℕ)^527*100000000000000000000^128 ≤ 56041909660705909^128*25000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4057 25000 56041909660705909 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4057/25000 : ℝ)) (X := (56041909660705909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501539365146059709/12500000000000000000 : ℝ) ≤ (1000029909609653/1000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (12501539365146059709/12500000000000000000 : ℝ)^128 ≤ (1000029909609653/1000000000000000 : ℝ)^527 := by
      have hnat : (12501539365146059709 : ℕ)^128*1000000000000000^527 ≤ 1000029909609653^527*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501539365146059709 12500000000000000000 1000029909609653 1000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000029909609653/1000000000000000 : ℝ)) (X := (12501539365146059709/12500000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012439874048988949/20000000000000000000 : ℝ) ≤ (10001510369155551/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (20012439874048988949/20000000000000000000 : ℝ)^128 ≤ (10001510369155551/10000000000000000 : ℝ)^527 := by
      have hnat : (20012439874048988949 : ℕ)^128*10000000000000000^527 ≤ 10001510369155551^527*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012439874048988949 20000000000000000000 10001510369155551 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001510369155551/10000000000000000 : ℝ)) (X := (20012439874048988949/20000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50056041909660705909/50000000000000000000 : ℝ) ≤ (2500680410553643/2500000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50056041909660705909/50000000000000000000 : ℝ)^128 ≤ (2500680410553643/2500000000000000 : ℝ)^527 := by
      have hnat : (50056041909660705909 : ℕ)^128*2500000000000000^527 ≤ 2500680410553643^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056041909660705909 50000000000000000000 2500680410553643 2500000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500680410553643/2500000000000000 : ℝ)) (X := (50056041909660705909/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1539365146059709/25000000000000000000 : ℝ) ≤ ((16837255656298996497/16842500000000000000 : ℝ)+2*(1211273059021/673700000000000 : ℝ)*(9491/100000 : ℝ))^(527/128 : ℝ) := by
    rw [show (16837255656298996497/16842500000000000000 : ℝ)+2*(1211273059021/673700000000000 : ℝ)*(9491/100000 : ℝ)=(1000029909609653/1000000000000000 : ℝ) by norm_num, show 1+2*(1539365146059709/25000000000000000000 : ℝ)=(12501539365146059709/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56041909660705909/100000000000000000000 : ℝ)+(1539365146059709/25000000000000000000 : ℝ) ≤ ((16837255656298996497/16842500000000000000 : ℝ)+(1211273059021/673700000000000 : ℝ)*((4057/25000 : ℝ)+(9491/100000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (16837255656298996497/16842500000000000000 : ℝ)+(1211273059021/673700000000000 : ℝ)*((4057/25000 : ℝ)+(9491/100000 : ℝ))=(10001510369155551/10000000000000000 : ℝ) by norm_num, show 1+(56041909660705909/100000000000000000000 : ℝ)+(1539365146059709/25000000000000000000 : ℝ)=(20012439874048988949/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56041909660705909/100000000000000000000 : ℝ) ≤ ((16837255656298996497/16842500000000000000 : ℝ)+2*(1211273059021/673700000000000 : ℝ)*(4057/25000 : ℝ))^(527/128 : ℝ) := by
    rw [show (16837255656298996497/16842500000000000000 : ℝ)+2*(1211273059021/673700000000000 : ℝ)*(4057/25000 : ℝ)=(2500680410553643/2500000000000000 : ℝ) by norm_num, show 1+2*(56041909660705909/100000000000000000000 : ℝ)=(50056041909660705909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16837255656298996497/16842500000000000000 : ℝ)*(X 1 0+X 2 0)+(1211273059021/673700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (9491/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (16837255656298996497/16842500000000000000 : ℝ)) (alpha := (1211273059021/673700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16837255656298996497/16842500000000000000 : ℝ)*(X 0 1+X 2 1)+(1211273059021/673700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (9491/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (16837255656298996497/16842500000000000000 : ℝ)) (alpha := (1211273059021/673700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16837255656298996497/16842500000000000000 : ℝ)*(X 0 2+X 1 2)+(1211273059021/673700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (9491/100000 : ℝ)) (hi := (4057/25000 : ℝ)) (c := (16837255656298996497/16842500000000000000 : ℝ)) (alpha := (1211273059021/673700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529505883/2500000000 : ℝ)*X 0 0+(5419832503/10000000000 : ℝ)*X 0 1+(1310116297/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351533379/10000000000 : ℝ)*X 1 0+(-138095569/625000000 : ℝ)*X 1 1+(5240465319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675766647/5000000000 : ℝ)*X 2 0+(5240465749/10000000000 : ℝ)*X 2 1+(-44190573/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349339289/10000000000 : ℝ)*X 0 0+(1042793767/2500000000 : ℝ)*X 0 1+(4534892431/10000000000 : ℝ)*X 0 2+(4349339289/10000000000 : ℝ)*X 1 0+(1042793767/2500000000 : ℝ)*X 1 1+(4534892431/10000000000 : ℝ)*X 1 2+(4349339289/10000000000 : ℝ)*X 2 0+(1042793767/2500000000 : ℝ)*X 2 1+(4534892431/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059019071/5000000000 : ℝ)*X 0 0+(1310279493/2500000000 : ℝ)*X 0 1+(2709587947/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265288951/500000000 : ℝ)*X 1 0+(-253852269/1250000000 : ℝ)*X 1 1+(5419175817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652889337/5000000000 : ℝ)*X 2 0+(2709588059/5000000000 : ℝ)*X 2 1+(-507704553/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349367827/10000000000 : ℝ)*X 0 0+(4533569101/10000000000 : ℝ)*X 0 1+(417250531/1000000000 : ℝ)*X 0 2+(4349367827/10000000000 : ℝ)*X 1 0+(4533569101/10000000000 : ℝ)*X 1 1+(417250531/1000000000 : ℝ)*X 1 2+(4349367827/10000000000 : ℝ)*X 2 0+(4533569101/10000000000 : ℝ)*X 2 1+(417250531/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (764823198816023429748754449/105265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (482056723/50000000000000 : ℝ)*(base19) + (570785539/100000000000000 : ℝ)*(base23) + (23161991/12500000000000 : ℝ)*(lower2) + (75138229/100000000000000 : ℝ)*(upper5) + (520288947489143/12500000000000 : ℝ)*(major0) + (520288947489143/12500000000000 : ℝ)*(major1) + (520288947489143/12500000000000 : ℝ)*(major2) + (1115036003511187/20000000000000 : ℝ)*(sp0) + (2787604408547889/50000000000000 : ℝ)*(sp1) + (2787607030609549/50000000000000 : ℝ)*(sp2) + (687349458458879/25000000000000 : ℝ)*(sp3) + (34614448703/100000000000000 : ℝ)*(sp4) + (2425397707/50000000000000 : ℝ)*(sp5) + (5225898893/50000000000000 : ℝ)*(sp7) + (2749408285633301/100000000000000 : ℝ)*(f.failure) + (2787607316002319/50000000000000 : ℝ)*(f.sum) + (37677712988619/8421250000000000000000000000 : ℝ)*base66 + (3538841453708388321/210531250000000000000000000000000 : ℝ)*base67 + (1917917522509919571/210531250000000000000000000000000 : ℝ)*base69 + (689230205825857071/210531250000000000000000000000000 : ℝ)*base71 + (30787344060367/16842500000000000000000000000 : ℝ)*base73 + (2325049136433482071/210531250000000000000000000000000 : ℝ)*base75 + (5435602357894919571/210531250000000000000000000000000 : ℝ)*base77 + (30658789966517929/210531250000000000000000000000000 : ℝ)*base80 + (38120152461209/8421250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (52555941/10000000000000000000000 : ℝ)*base90 + (52555941/10000000000000000000000 : ℝ)*base92 + (52555941/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3963106411715135979769165179/421062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2633714543/100000000000000 : ℝ)*(base19) + (616624563/25000000000000 : ℝ)*(base23) + (4993401/5000000000000 : ℝ)*(upper2) + (3295337/1250000000000 : ℝ)*(upper3) + (220466713/100000000000000 : ℝ)*(upper5) + (2096434090391123/50000000000000 : ℝ)*(major0) + (2096434090391123/50000000000000 : ℝ)*(major1) + (2096434090391123/50000000000000 : ℝ)*(major2) + (50337673017/100000000000000 : ℝ)*(sp1) + (12897385679/25000000000000 : ℝ)*(sp2) + (561614364814989/10000000000000 : ℝ)*(sp4) + (561609067676233/10000000000000 : ℝ)*(sp5) + (2808044796054461/50000000000000 : ℝ)*(sp6) + (1384796199838011/50000000000000 : ℝ)*(sp7) + (1384796199838011/50000000000000 : ℝ)*(f.failure) + (561614364814989/10000000000000 : ℝ)*(f.sum) + (15100423699589/2105312500000000000000000000 : ℝ)*base66 + (9510579927795278869/842125000000000000000000000000000 : ℝ)*base68 + (8306685756818528869/842125000000000000000000000000000 : ℝ)*base70 + (4271700037057153869/842125000000000000000000000000000 : ℝ)*base72 + (39219818692153/4210625000000000000000000000 : ℝ)*base74 + (4733060421306153869/842125000000000000000000000000000 : ℝ)*base76 + (4472517281706278869/842125000000000000000000000000000 : ℝ)*base78 + (7909477981795278869/842125000000000000000000000000000 : ℝ)*base80 + (151651037068347/16842500000000000000000000000 : ℝ)*base82 + (89124949/5000000000000000000000 : ℝ)*base89 + (89124949/5000000000000000000000 : ℝ)*base91 + (89124949/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1240_s4_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120325181/10000000000 : ℝ)*x 0 + (1349394669/2500000000 : ℝ)*x 1 + (526121101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120325181/10000000000 : ℝ)^8433 ≤ (6446364837721/50000000000000 : ℝ)^6385 := by
    have hnat : (2120325181 : ℕ)^8433*50000000000000^6385 ≤ 6446364837721^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120325181 10000000000 6446364837721 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349394669/2500000000 : ℝ)^8433 ≤ (44289556642801/100000000000000 : ℝ)^6385 := by
    have hnat : (1349394669 : ℕ)^8433*100000000000000^6385 ≤ 44289556642801^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349394669 2500000000 44289556642801 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526121101/1000000000 : ℝ)^8433 ≤ (42817713669899/100000000000000 : ℝ)^6385 := by
    have hnat : (526121101 : ℕ)^8433*100000000000000^6385 ≤ 42817713669899^6385*1000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526121101 1000000000 42817713669899 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120325181/10000000000 : ℝ), (1349394669/2500000000 : ℝ), (526121101/1000000000 : ℝ)] ![(6446364837721/50000000000000 : ℝ), (44289556642801/100000000000000 : ℝ), (42817713669899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120325181/10000000000 : ℝ)|^8433 ≤ (6446364837721/50000000000000 : ℝ)^6385
        have hw : |(-2120325181/10000000000 : ℝ)|=(2120325181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349394669/2500000000 : ℝ)|^8433 ≤ (44289556642801/100000000000000 : ℝ)^6385
        have hw : |(1349394669/2500000000 : ℝ)|=(1349394669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526121101/1000000000 : ℝ)|^8433 ≤ (42817713669899/100000000000000 : ℝ)^6385
        have hw : |(526121101/1000000000 : ℝ)|=(526121101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345925027/10000000000 : ℝ)*x 0 + (-1094781271/5000000000 : ℝ)*x 1 + (5261211011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345925027/10000000000 : ℝ)^8433 ≤ (10932657100321/25000000000000 : ℝ)^6385 := by
    have hnat : (5345925027 : ℕ)^8433*25000000000000^6385 ≤ 10932657100321^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345925027 10000000000 10932657100321 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094781271/5000000000 : ℝ)^8433 ≤ (6725828952479/50000000000000 : ℝ)^6385 := by
    have hnat : (1094781271 : ℕ)^8433*50000000000000^6385 ≤ 6725828952479^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094781271 5000000000 6725828952479 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261211011/10000000000 : ℝ)^8433 ≤ (42817713680647/100000000000000 : ℝ)^6385 := by
    have hnat : (5261211011 : ℕ)^8433*100000000000000^6385 ≤ 42817713680647^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261211011 10000000000 42817713680647 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345925027/10000000000 : ℝ), (-1094781271/5000000000 : ℝ), (5261211011/10000000000 : ℝ)] ![(10932657100321/25000000000000 : ℝ), (6725828952479/50000000000000 : ℝ), (42817713680647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345925027/10000000000 : ℝ)|^8433 ≤ (10932657100321/25000000000000 : ℝ)^6385
        have hw : |(5345925027/10000000000 : ℝ)|=(5345925027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094781271/5000000000 : ℝ)|^8433 ≤ (6725828952479/50000000000000 : ℝ)^6385
        have hw : |(-1094781271/5000000000 : ℝ)|=(1094781271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261211011/10000000000 : ℝ)|^8433 ≤ (42817713680647/100000000000000 : ℝ)^6385
        have hw : |(5261211011/10000000000 : ℝ)|=(5261211011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345925061/10000000000 : ℝ)*x 0 + (5261210937/10000000000 : ℝ)*x 1 + (-437912519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345925061/10000000000 : ℝ)^8433 ≤ (2186531438431/5000000000000 : ℝ)^6385 := by
    have hnat : (5345925061 : ℕ)^8433*5000000000000^6385 ≤ 2186531438431^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345925061 10000000000 2186531438431 5000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261210937/10000000000 : ℝ)^8433 ≤ (21408856442619/50000000000000 : ℝ)^6385 := by
    have hnat : (5261210937 : ℕ)^8433*50000000000000^6385 ≤ 21408856442619^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261210937 10000000000 21408856442619 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437912519/2000000000 : ℝ)^8433 ≤ (2690331667001/20000000000000 : ℝ)^6385 := by
    have hnat : (437912519 : ℕ)^8433*20000000000000^6385 ≤ 2690331667001^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437912519 2000000000 2690331667001 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345925061/10000000000 : ℝ), (5261210937/10000000000 : ℝ), (-437912519/2000000000 : ℝ)] ![(2186531438431/5000000000000 : ℝ), (21408856442619/50000000000000 : ℝ), (2690331667001/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345925061/10000000000 : ℝ)|^8433 ≤ (2186531438431/5000000000000 : ℝ)^6385
        have hw : |(5345925061/10000000000 : ℝ)|=(5345925061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261210937/10000000000 : ℝ)|^8433 ≤ (21408856442619/50000000000000 : ℝ)^6385
        have hw : |(5261210937/10000000000 : ℝ)|=(5261210937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437912519/2000000000 : ℝ)|^8433 ≤ (2690331667001/20000000000000 : ℝ)^6385
        have hw : |(-437912519/2000000000 : ℝ)|=(437912519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350720933/10000000000 : ℝ)*x 0 + (4214595023/10000000000 : ℝ)*x 1 + (2245559859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350720933/10000000000 : ℝ)^8433 ≤ (33314178178779/100000000000000 : ℝ)^6385 := by
    have hnat : (4350720933 : ℕ)^8433*100000000000000^6385 ≤ 33314178178779^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350720933 10000000000 33314178178779 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4214595023/10000000000 : ℝ)^8433 ≤ (255555725081/800000000000 : ℝ)^6385 := by
    have hnat : (4214595023 : ℕ)^8433*800000000000^6385 ≤ 255555725081^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214595023 10000000000 255555725081 800000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245559859/5000000000 : ℝ)^8433 ≤ (17370678088401/50000000000000 : ℝ)^6385 := by
    have hnat : (2245559859 : ℕ)^8433*50000000000000^6385 ≤ 17370678088401^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245559859 5000000000 17370678088401 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350720933/10000000000 : ℝ), (4214595023/10000000000 : ℝ), (2245559859/5000000000 : ℝ)] ![(33314178178779/100000000000000 : ℝ), (255555725081/800000000000 : ℝ), (17370678088401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350720933/10000000000 : ℝ)|^8433 ≤ (33314178178779/100000000000000 : ℝ)^6385
        have hw : |(4350720933/10000000000 : ℝ)|=(4350720933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4214595023/10000000000 : ℝ)|^8433 ≤ (255555725081/800000000000 : ℝ)^6385
        have hw : |(4214595023/10000000000 : ℝ)|=(4214595023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2245559859/5000000000 : ℝ)|^8433 ≤ (17370678088401/50000000000000 : ℝ)^6385
        have hw : |(2245559859/5000000000 : ℝ)|=(2245559859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120331351/10000000000 : ℝ)*x 0 + (1315397213/2500000000 : ℝ)*x 1 + (5397199341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120331351/10000000000 : ℝ)^8433 ≤ (12892779226049/100000000000000 : ℝ)^6385 := by
    have hnat : (2120331351 : ℕ)^8433*100000000000000^6385 ≤ 12892779226049^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120331351 10000000000 12892779226049 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315397213/2500000000 : ℝ)^8433 ≤ (10705443763783/25000000000000 : ℝ)^6385 := by
    have hnat : (1315397213 : ℕ)^8433*25000000000000^6385 ≤ 10705443763783^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315397213 2500000000 10705443763783 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397199341/10000000000 : ℝ)^8433 ≤ (11071361424677/25000000000000 : ℝ)^6385 := by
    have hnat : (5397199341 : ℕ)^8433*25000000000000^6385 ≤ 11071361424677^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397199341 10000000000 11071361424677 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120331351/10000000000 : ℝ), (1315397213/2500000000 : ℝ), (5397199341/10000000000 : ℝ)] ![(12892779226049/100000000000000 : ℝ), (10705443763783/25000000000000 : ℝ), (11071361424677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120331351/10000000000 : ℝ)|^8433 ≤ (12892779226049/100000000000000 : ℝ)^6385
        have hw : |(-2120331351/10000000000 : ℝ)|=(2120331351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315397213/2500000000 : ℝ)|^8433 ≤ (10705443763783/25000000000000 : ℝ)^6385
        have hw : |(1315397213/2500000000 : ℝ)|=(1315397213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397199341/10000000000 : ℝ)|^8433 ≤ (11071361424677/25000000000000 : ℝ)^6385
        have hw : |(5397199341/10000000000 : ℝ)|=(5397199341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311136557/10000000000 : ℝ)*x 0 + (-410714889/2000000000 : ℝ)*x 1 + (1349299817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311136557/10000000000 : ℝ)^8433 ≤ (21677583530129/50000000000000 : ℝ)^6385 := by
    have hnat : (5311136557 : ℕ)^8433*50000000000000^6385 ≤ 21677583530129^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311136557 10000000000 21677583530129 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410714889/2000000000 : ℝ)^8433 ≤ (12359388024981/100000000000000 : ℝ)^6385 := by
    have hnat : (410714889 : ℕ)^8433*100000000000000^6385 ≤ 12359388024981^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410714889 2000000000 12359388024981 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349299817/2500000000 : ℝ)^8433 ≤ (44285444907599/100000000000000 : ℝ)^6385 := by
    have hnat : (1349299817 : ℕ)^8433*100000000000000^6385 ≤ 44285444907599^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349299817 2500000000 44285444907599 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311136557/10000000000 : ℝ), (-410714889/2000000000 : ℝ), (1349299817/2500000000 : ℝ)] ![(21677583530129/50000000000000 : ℝ), (12359388024981/100000000000000 : ℝ), (44285444907599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311136557/10000000000 : ℝ)|^8433 ≤ (21677583530129/50000000000000 : ℝ)^6385
        have hw : |(5311136557/10000000000 : ℝ)|=(5311136557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410714889/2000000000 : ℝ)|^8433 ≤ (12359388024981/100000000000000 : ℝ)^6385
        have hw : |(-410714889/2000000000 : ℝ)|=(410714889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349299817/2500000000 : ℝ)|^8433 ≤ (44285444907599/100000000000000 : ℝ)^6385
        have hw : |(1349299817/2500000000 : ℝ)|=(1349299817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655568187/5000000000 : ℝ)*x 0 + (1349299903/2500000000 : ℝ)*x 1 + (-2053574223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655568187/5000000000 : ℝ)^8433 ≤ (1354848908977/3125000000000 : ℝ)^6385 := by
    have hnat : (2655568187 : ℕ)^8433*3125000000000^6385 ≤ 1354848908977^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655568187 5000000000 1354848908977 3125000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349299903/2500000000 : ℝ)^8433 ≤ (44285448635567/100000000000000 : ℝ)^6385 := by
    have hnat : (1349299903 : ℕ)^8433*100000000000000^6385 ≤ 44285448635567^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349299903 2500000000 44285448635567 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2053574223/10000000000 : ℝ)^8433 ≤ (6179693130161/50000000000000 : ℝ)^6385 := by
    have hnat : (2053574223 : ℕ)^8433*50000000000000^6385 ≤ 6179693130161^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053574223 10000000000 6179693130161 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655568187/5000000000 : ℝ), (1349299903/2500000000 : ℝ), (-2053574223/10000000000 : ℝ)] ![(1354848908977/3125000000000 : ℝ), (44285448635567/100000000000000 : ℝ), (6179693130161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655568187/5000000000 : ℝ)|^8433 ≤ (1354848908977/3125000000000 : ℝ)^6385
        have hw : |(2655568187/5000000000 : ℝ)|=(2655568187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349299903/2500000000 : ℝ)|^8433 ≤ (44285448635567/100000000000000 : ℝ)^6385
        have hw : |(1349299903/2500000000 : ℝ)|=(1349299903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2053574223/10000000000 : ℝ)|^8433 ≤ (6179693130161/50000000000000 : ℝ)^6385
        have hw : |(-2053574223/10000000000 : ℝ)|=(2053574223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s4_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350733587/10000000000 : ℝ)*x 0 + (4490353761/10000000000 : ℝ)*x 1 + (1053840981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350733587/10000000000 : ℝ)^8433 ≤ (33314306151413/100000000000000 : ℝ)^6385 := by
    have hnat : (4350733587 : ℕ)^8433*100000000000000^6385 ≤ 33314306151413^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350733587 10000000000 33314306151413 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490353761/10000000000 : ℝ)^8433 ≤ (34733530789443/100000000000000 : ℝ)^6385 := by
    have hnat : (4490353761 : ℕ)^8433*100000000000000^6385 ≤ 34733530789443^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490353761 10000000000 34733530789443 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053840981/2500000000 : ℝ)^8433 ≤ (1597608151803/5000000000000 : ℝ)^6385 := by
    have hnat : (1053840981 : ℕ)^8433*5000000000000^6385 ≤ 1597608151803^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053840981 2500000000 1597608151803 5000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350733587/10000000000 : ℝ), (4490353761/10000000000 : ℝ), (1053840981/2500000000 : ℝ)] ![(33314306151413/100000000000000 : ℝ), (34733530789443/100000000000000 : ℝ), (1597608151803/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350733587/10000000000 : ℝ)|^8433 ≤ (33314306151413/100000000000000 : ℝ)^6385
        have hw : |(4350733587/10000000000 : ℝ)|=(4350733587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490353761/10000000000 : ℝ)|^8433 ≤ (34733530789443/100000000000000 : ℝ)^6385
        have hw : |(4490353761/10000000000 : ℝ)|=(4490353761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053840981/2500000000 : ℝ)|^8433 ≤ (1597608151803/5000000000000 : ℝ)^6385
        have hw : |(1053840981/2500000000 : ℝ)|=(1053840981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2837/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5453/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5453/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5453/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5453/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5453/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5453/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5453/50000 : ℝ) ^ (527/128 : ℝ) ≤ (10911599026921883/100000000000000000000 : ℝ) := by
    have hpowers : (5453/50000 : ℝ)^527 ≤ (10911599026921883/100000000000000000000 : ℝ)^128 := by
      have hnat : (5453 : ℕ)^527*100000000000000000000^128 ≤ 10911599026921883^128*50000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5453 50000 10911599026921883 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5453/50000 : ℝ)) (X := (10911599026921883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14703/100000 : ℝ) ^ (527/128 : ℝ) ≤ (1866483774319367/5000000000000000000 : ℝ) := by
    have hpowers : (14703/100000 : ℝ)^527 ≤ (1866483774319367/5000000000000000000 : ℝ)^128 := by
      have hnat : (14703 : ℕ)^527*5000000000000000000^128 ≤ 1866483774319367^128*100000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14703 100000 1866483774319367 5000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14703/100000 : ℝ)) (X := (1866483774319367/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010911599026921883/50000000000000000000 : ℝ) ≤ (125006625091581/125000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50010911599026921883/50000000000000000000 : ℝ)^128 ≤ (125006625091581/125000000000000 : ℝ)^527 := by
      have hnat : (50010911599026921883 : ℕ)^128*125000000000000^527 ≤ 125006625091581^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010911599026921883 50000000000000000000 125006625091581 125000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125006625091581/125000000000000 : ℝ)) (X := (50010911599026921883/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048241274513309223/100000000000000000000 : ℝ) ≤ (10001171490662619/10000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (100048241274513309223/100000000000000000000 : ℝ)^128 ≤ (10001171490662619/10000000000000000 : ℝ)^527 := by
      have hnat : (100048241274513309223 : ℕ)^128*10000000000000000^527 ≤ 10001171490662619^527*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048241274513309223 100000000000000000000 10001171490662619 10000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001171490662619/10000000000000000 : ℝ)) (X := (100048241274513309223/100000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501866483774319367/2500000000000000000 : ℝ) ≤ (5000906486999379/5000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (2501866483774319367/2500000000000000000 : ℝ)^128 ≤ (5000906486999379/5000000000000000 : ℝ)^527 := by
      have hnat : (2501866483774319367 : ℕ)^128*5000000000000000^527 ≤ 5000906486999379^527*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501866483774319367 2500000000000000000 5000906486999379 5000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000906486999379/5000000000000000 : ℝ)) (X := (2501866483774319367/2500000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10911599026921883/100000000000000000000 : ℝ) ≤ ((9489505100822695173/9492500000000000000 : ℝ)+2*(641483336139/379700000000000 : ℝ)*(5453/50000 : ℝ))^(527/128 : ℝ) := by
    rw [show (9489505100822695173/9492500000000000000 : ℝ)+2*(641483336139/379700000000000 : ℝ)*(5453/50000 : ℝ)=(125006625091581/125000000000000 : ℝ) by norm_num, show 1+2*(10911599026921883/100000000000000000000 : ℝ)=(50010911599026921883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1866483774319367/5000000000000000000 : ℝ)+(10911599026921883/100000000000000000000 : ℝ) ≤ ((9489505100822695173/9492500000000000000 : ℝ)+(641483336139/379700000000000 : ℝ)*((14703/100000 : ℝ)+(5453/50000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (9489505100822695173/9492500000000000000 : ℝ)+(641483336139/379700000000000 : ℝ)*((14703/100000 : ℝ)+(5453/50000 : ℝ))=(10001171490662619/10000000000000000 : ℝ) by norm_num, show 1+(1866483774319367/5000000000000000000 : ℝ)+(10911599026921883/100000000000000000000 : ℝ)=(100048241274513309223/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1866483774319367/5000000000000000000 : ℝ) ≤ ((9489505100822695173/9492500000000000000 : ℝ)+2*(641483336139/379700000000000 : ℝ)*(14703/100000 : ℝ))^(527/128 : ℝ) := by
    rw [show (9489505100822695173/9492500000000000000 : ℝ)+2*(641483336139/379700000000000 : ℝ)*(14703/100000 : ℝ)=(5000906486999379/5000000000000000 : ℝ) by norm_num, show 1+2*(1866483774319367/5000000000000000000 : ℝ)=(2501866483774319367/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9489505100822695173/9492500000000000000 : ℝ)*(X 1 0+X 2 0)+(641483336139/379700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (9489505100822695173/9492500000000000000 : ℝ)) (alpha := (641483336139/379700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9489505100822695173/9492500000000000000 : ℝ)*(X 0 1+X 2 1)+(641483336139/379700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (9489505100822695173/9492500000000000000 : ℝ)) (alpha := (641483336139/379700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9489505100822695173/9492500000000000000 : ℝ)*(X 0 2+X 1 2)+(641483336139/379700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (9489505100822695173/9492500000000000000 : ℝ)) (alpha := (641483336139/379700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2120325181/10000000000 : ℝ)*X 0 0+(1349394669/2500000000 : ℝ)*X 0 1+(526121101/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345925027/10000000000 : ℝ)*X 1 0+(-1094781271/5000000000 : ℝ)*X 1 1+(5261211011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345925061/10000000000 : ℝ)*X 2 0+(5261210937/10000000000 : ℝ)*X 2 1+(-437912519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350720933/10000000000 : ℝ)*X 0 0+(4214595023/10000000000 : ℝ)*X 0 1+(2245559859/5000000000 : ℝ)*X 0 2+(4350720933/10000000000 : ℝ)*X 1 0+(4214595023/10000000000 : ℝ)*X 1 1+(2245559859/5000000000 : ℝ)*X 1 2+(4350720933/10000000000 : ℝ)*X 2 0+(4214595023/10000000000 : ℝ)*X 2 1+(2245559859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120331351/10000000000 : ℝ)*X 0 0+(1315397213/2500000000 : ℝ)*X 0 1+(5397199341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311136557/10000000000 : ℝ)*X 1 0+(-410714889/2000000000 : ℝ)*X 1 1+(1349299817/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655568187/5000000000 : ℝ)*X 2 0+(1349299903/2500000000 : ℝ)*X 2 1+(-2053574223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350733587/10000000000 : ℝ)*X 0 0+(4490353761/10000000000 : ℝ)*X 0 1+(1053840981/2500000000 : ℝ)*X 0 2+(4350733587/10000000000 : ℝ)*X 1 0+(4490353761/10000000000 : ℝ)*X 1 1+(1053840981/2500000000 : ℝ)*X 1 2+(4350733587/10000000000 : ℝ)*X 2 0+(4490353761/10000000000 : ℝ)*X 2 1+(1053840981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (608118285673694983393515987/59328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (423999719/20000000000000 : ℝ)*(base19) + (536678217/25000000000000 : ℝ)*(base23) + (10651707/100000000000000 : ℝ)*(lower2) + (286822579/100000000000000 : ℝ)*(upper3) + (100349007/50000000000000 : ℝ)*(upper5) + (342174815447663/6250000000000 : ℝ)*(major0) + (342174815447663/6250000000000 : ℝ)*(major1) + (342174815447663/6250000000000 : ℝ)*(major2) + (7333172443895351/100000000000000 : ℝ)*(sp0) + (1833305790441101/25000000000000 : ℝ)*(sp1) + (1833305783762533/25000000000000 : ℝ)*(sp2) + (904084992118277/25000000000000 : ℝ)*(sp3) + (412795841/781250000000 : ℝ)*(sp4) + (3562802453/12500000000000 : ℝ)*(sp7) + (904092117723183/25000000000000 : ℝ)*(f.failure) + (7333225281762999/100000000000000 : ℝ)*(f.sum) + (100878269770393/18985000000000000000000000000 : ℝ)*base66 + (136822932890655699/59328125000000000000000000000000 : ℝ)*base67 + (133276304816186949/59328125000000000000000000000000 : ℝ)*base69 + (387034717573780699/59328125000000000000000000000000 : ℝ)*base71 + (1757322110947/4746250000000000000000000000 : ℝ)*base74 + (197776776427093199/59328125000000000000000000000000 : ℝ)*base75 + (878364130703844301/59328125000000000000000000000000 : ℝ)*base78 + (764496797099030699/59328125000000000000000000000000 : ℝ)*base79 + (13368468373947/4746250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (13809697/2500000000000000000000 : ℝ)*base89 + (13809697/2500000000000000000000 : ℝ)*base91 + (13809697/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57010420884195425051518791/5932812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (701219173/50000000000000 : ℝ)*(base19) + (697540873/50000000000000 : ℝ)*(base23) + (343758509/100000000000000 : ℝ)*(upper3) + (14403813/25000000000000 : ℝ)*(lower4) + (147006419/100000000000000 : ℝ)*(upper5) + (275263750760353/5000000000000 : ℝ)*(major0) + (275263750760353/5000000000000 : ℝ)*(major1) + (275263750760353/5000000000000 : ℝ)*(major2) + (18231379973/100000000000000 : ℝ)*(sp1) + (39336584399/100000000000000 : ℝ)*(sp2) + (368702453297719/5000000000000 : ℝ)*(sp4) + (7374029432136061/100000000000000 : ℝ)*(sp5) + (3687004167144117/50000000000000 : ℝ)*(sp6) + (28410161282409/781250000000 : ℝ)*(sp7) + (28410161282409/781250000000 : ℝ)*(f.failure) + (368702453297719/5000000000000 : ℝ)*(f.sum) + (12369241137/9492500000000000000000000 : ℝ)*base65 + (163119659214248931/47462500000000000000000000000000 : ℝ)*base68 + (550479783779398931/47462500000000000000000000000000 : ℝ)*base70 + (202439551567748931/47462500000000000000000000000000 : ℝ)*base72 + (8154308074551/3797000000000000000000000000 : ℝ)*base73 + (4946875309236431/47462500000000000000000000000000 : ℝ)*base76 + (447867218627486431/47462500000000000000000000000000 : ℝ)*base78 + (855674042212413569/47462500000000000000000000000000 : ℝ)*base79 + (9526370406549/3797000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (860831/78125000000000000000 : ℝ)*base89 + (860831/78125000000000000000 : ℝ)*base91 + (860831/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2837/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1240_s5_0 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060389571/5000000000 : ℝ)*x 0 + (1348115463/2500000000 : ℝ)*x 1 + (2633014663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060389571/5000000000 : ℝ)^8433 ≤ (644818775543/5000000000000 : ℝ)^6385 := by
    have hnat : (1060389571 : ℕ)^8433*5000000000000^6385 ≤ 644818775543^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060389571 5000000000 644818775543 5000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348115463/2500000000 : ℝ)^8433 ≤ (11058528051301/25000000000000 : ℝ)^6385 := by
    have hnat : (1348115463 : ℕ)^8433*25000000000000^6385 ≤ 11058528051301^6385*2500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348115463 2500000000 11058528051301 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633014663/5000000000 : ℝ)^8433 ≤ (42869512267317/100000000000000 : ℝ)^6385 := by
    have hnat : (2633014663 : ℕ)^8433*100000000000000^6385 ≤ 42869512267317^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633014663 5000000000 42869512267317 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060389571/5000000000 : ℝ), (1348115463/2500000000 : ℝ), (2633014663/5000000000 : ℝ)] ![(644818775543/5000000000000 : ℝ), (11058528051301/25000000000000 : ℝ), (42869512267317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060389571/5000000000 : ℝ)|^8433 ≤ (644818775543/5000000000000 : ℝ)^6385
        have hw : |(-1060389571/5000000000 : ℝ)|=(1060389571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348115463/2500000000 : ℝ)|^8433 ≤ (11058528051301/25000000000000 : ℝ)^6385
        have hw : |(1348115463/2500000000 : ℝ)|=(1348115463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633014663/5000000000 : ℝ)|^8433 ≤ (42869512267317/100000000000000 : ℝ)^6385
        have hw : |(2633014663/5000000000 : ℝ)|=(2633014663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_1 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344630023/10000000000 : ℝ)*x 0 + (-2184901471/10000000000 : ℝ)*x 1 + (5266029279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344630023/10000000000 : ℝ)^8433 ≤ (43716637738483/100000000000000 : ℝ)^6385 := by
    have hnat : (5344630023 : ℕ)^8433*100000000000000^6385 ≤ 43716637738483^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344630023 10000000000 43716637738483 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2184901471/10000000000 : ℝ)^8433 ≤ (6706925243863/50000000000000 : ℝ)^6385 := by
    have hnat : (2184901471 : ℕ)^8433*50000000000000^6385 ≤ 6706925243863^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184901471 10000000000 6706925243863 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266029279/10000000000 : ℝ)^8433 ≤ (5358688970247/12500000000000 : ℝ)^6385 := by
    have hnat : (5266029279 : ℕ)^8433*12500000000000^6385 ≤ 5358688970247^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266029279 10000000000 5358688970247 12500000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344630023/10000000000 : ℝ), (-2184901471/10000000000 : ℝ), (5266029279/10000000000 : ℝ)] ![(43716637738483/100000000000000 : ℝ), (6706925243863/50000000000000 : ℝ), (5358688970247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344630023/10000000000 : ℝ)|^8433 ≤ (43716637738483/100000000000000 : ℝ)^6385
        have hw : |(5344630023/10000000000 : ℝ)|=(5344630023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2184901471/10000000000 : ℝ)|^8433 ≤ (6706925243863/50000000000000 : ℝ)^6385
        have hw : |(-2184901471/10000000000 : ℝ)|=(2184901471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266029279/10000000000 : ℝ)|^8433 ≤ (5358688970247/12500000000000 : ℝ)^6385
        have hw : |(5266029279/10000000000 : ℝ)|=(5266029279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_2 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672315299/5000000000 : ℝ)*x 0 + (5266029151/10000000000 : ℝ)*x 1 + (-17479207/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672315299/5000000000 : ℝ)^8433 ≤ (43716643950293/100000000000000 : ℝ)^6385 := by
    have hnat : (2672315299 : ℕ)^8433*100000000000000^6385 ≤ 43716643950293^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672315299 5000000000 43716643950293 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266029151/10000000000 : ℝ)^8433 ≤ (42869510385729/100000000000000 : ℝ)^6385 := by
    have hnat : (5266029151 : ℕ)^8433*100000000000000^6385 ≤ 42869510385729^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266029151 10000000000 42869510385729 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17479207/80000000 : ℝ)^8433 ≤ (2682769131007/20000000000000 : ℝ)^6385 := by
    have hnat : (17479207 : ℕ)^8433*20000000000000^6385 ≤ 2682769131007^6385*80000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17479207 80000000 2682769131007 20000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672315299/5000000000 : ℝ), (5266029151/10000000000 : ℝ), (-17479207/80000000 : ℝ)] ![(43716643950293/100000000000000 : ℝ), (42869510385729/100000000000000 : ℝ), (2682769131007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672315299/5000000000 : ℝ)|^8433 ≤ (43716643950293/100000000000000 : ℝ)^6385
        have hw : |(2672315299/5000000000 : ℝ)|=(2672315299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266029151/10000000000 : ℝ)|^8433 ≤ (42869510385729/100000000000000 : ℝ)^6385
        have hw : |(5266029151/10000000000 : ℝ)|=(5266029151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17479207/80000000 : ℝ)|^8433 ≤ (2682769131007/20000000000000 : ℝ)^6385
        have hw : |(-17479207/80000000 : ℝ)|=(17479207/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_3 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217549297/500000000 : ℝ)*x 0 + (4224635857/10000000000 : ℝ)*x 1 + (4481011747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217549297/500000000 : ℝ)^8433 ≤ (33316858276711/100000000000000 : ℝ)^6385 := by
    have hnat : (217549297 : ℕ)^8433*100000000000000^6385 ≤ 33316858276711^6385*500000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217549297 500000000 33316858276711 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224635857/10000000000 : ℝ)^8433 ≤ (32045018992833/100000000000000 : ℝ)^6385 := by
    have hnat : (4224635857 : ℕ)^8433*100000000000000^6385 ≤ 32045018992833^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224635857 10000000000 32045018992833 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481011747/10000000000 : ℝ)^8433 ≤ (17319061361873/50000000000000 : ℝ)^6385 := by
    have hnat : (4481011747 : ℕ)^8433*50000000000000^6385 ≤ 17319061361873^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481011747 10000000000 17319061361873 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217549297/500000000 : ℝ), (4224635857/10000000000 : ℝ), (4481011747/10000000000 : ℝ)] ![(33316858276711/100000000000000 : ℝ), (32045018992833/100000000000000 : ℝ), (17319061361873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217549297/500000000 : ℝ)|^8433 ≤ (33316858276711/100000000000000 : ℝ)^6385
        have hw : |(217549297/500000000 : ℝ)|=(217549297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224635857/10000000000 : ℝ)|^8433 ≤ (32045018992833/100000000000000 : ℝ)^6385
        have hw : |(4224635857/10000000000 : ℝ)|=(4224635857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481011747/10000000000 : ℝ)|^8433 ≤ (17319061361873/50000000000000 : ℝ)^6385
        have hw : |(4481011747/10000000000 : ℝ)|=(4481011747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_4 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120784221/10000000000 : ℝ)*x 0 + (5266354513/10000000000 : ℝ)*x 1 + (16850423/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120784221/10000000000 : ℝ)^8433 ≤ (80602601891/625000000000 : ℝ)^6385 := by
    have hnat : (2120784221 : ℕ)^8433*625000000000^6385 ≤ 80602601891^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120784221 10000000000 80602601891 625000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266354513/10000000000 : ℝ)^8433 ≤ (42873008690123/100000000000000 : ℝ)^6385 := by
    have hnat : (5266354513 : ℕ)^8433*100000000000000^6385 ≤ 42873008690123^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266354513 10000000000 42873008690123 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16850423/31250000 : ℝ)^8433 ≤ (44230575004037/100000000000000 : ℝ)^6385 := by
    have hnat : (16850423 : ℕ)^8433*100000000000000^6385 ≤ 44230575004037^6385*31250000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16850423 31250000 44230575004037 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120784221/10000000000 : ℝ), (5266354513/10000000000 : ℝ), (16850423/31250000 : ℝ)] ![(80602601891/625000000000 : ℝ), (42873008690123/100000000000000 : ℝ), (44230575004037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120784221/10000000000 : ℝ)|^8433 ≤ (80602601891/625000000000 : ℝ)^6385
        have hw : |(-2120784221/10000000000 : ℝ)|=(2120784221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266354513/10000000000 : ℝ)|^8433 ≤ (42873008690123/100000000000000 : ℝ)^6385
        have hw : |(5266354513/10000000000 : ℝ)|=(5266354513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16850423/31250000 : ℝ)|^8433 ≤ (44230575004037/100000000000000 : ℝ)^6385
        have hw : |(16850423/31250000 : ℝ)|=(16850423/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_5 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312375063/10000000000 : ℝ)*x 0 + (-411759059/2000000000 : ℝ)*x 1 + (5392135323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312375063/10000000000 : ℝ)^8433 ≤ (43368520370843/100000000000000 : ℝ)^6385 := by
    have hnat : (5312375063 : ℕ)^8433*100000000000000^6385 ≤ 43368520370843^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312375063 10000000000 43368520370843 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411759059/2000000000 : ℝ)^8433 ≤ (3100226253907/25000000000000 : ℝ)^6385 := by
    have hnat : (411759059 : ℕ)^8433*25000000000000^6385 ≤ 3100226253907^6385*2000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411759059 2000000000 3100226253907 25000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392135323/10000000000 : ℝ)^8433 ≤ (2764410912699/6250000000000 : ℝ)^6385 := by
    have hnat : (5392135323 : ℕ)^8433*6250000000000^6385 ≤ 2764410912699^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392135323 10000000000 2764410912699 6250000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312375063/10000000000 : ℝ), (-411759059/2000000000 : ℝ), (5392135323/10000000000 : ℝ)] ![(43368520370843/100000000000000 : ℝ), (3100226253907/25000000000000 : ℝ), (2764410912699/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312375063/10000000000 : ℝ)|^8433 ≤ (43368520370843/100000000000000 : ℝ)^6385
        have hw : |(5312375063/10000000000 : ℝ)|=(5312375063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411759059/2000000000 : ℝ)|^8433 ≤ (3100226253907/25000000000000 : ℝ)^6385
        have hw : |(-411759059/2000000000 : ℝ)|=(411759059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392135323/10000000000 : ℝ)|^8433 ≤ (2764410912699/6250000000000 : ℝ)^6385
        have hw : |(5392135323/10000000000 : ℝ)|=(5392135323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_6 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656187521/5000000000 : ℝ)*x 0 + (5392135393/10000000000 : ℝ)*x 1 + (-2058795227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656187521/5000000000 : ℝ)^8433 ≤ (43368520144417/100000000000000 : ℝ)^6385 := by
    have hnat : (2656187521 : ℕ)^8433*100000000000000^6385 ≤ 43368520144417^6385*5000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656187521 5000000000 43368520144417 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392135393/10000000000 : ℝ)^8433 ≤ (22115287680777/50000000000000 : ℝ)^6385 := by
    have hnat : (5392135393 : ℕ)^8433*50000000000000^6385 ≤ 22115287680777^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392135393 10000000000 22115287680777 50000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058795227/10000000000 : ℝ)^8433 ≤ (12400904474661/100000000000000 : ℝ)^6385 := by
    have hnat : (2058795227 : ℕ)^8433*100000000000000^6385 ≤ 12400904474661^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058795227 10000000000 12400904474661 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656187521/5000000000 : ℝ), (5392135393/10000000000 : ℝ), (-2058795227/10000000000 : ℝ)] ![(43368520144417/100000000000000 : ℝ), (22115287680777/50000000000000 : ℝ), (12400904474661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656187521/5000000000 : ℝ)|^8433 ≤ (43368520144417/100000000000000 : ℝ)^6385
        have hw : |(2656187521/5000000000 : ℝ)|=(2656187521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392135393/10000000000 : ℝ)|^8433 ≤ (22115287680777/50000000000000 : ℝ)^6385
        have hw : |(5392135393/10000000000 : ℝ)|=(5392135393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058795227/10000000000 : ℝ)|^8433 ≤ (12400904474661/100000000000000 : ℝ)^6385
        have hw : |(-2058795227/10000000000 : ℝ)|=(2058795227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1240_s5_7 (p : ℝ) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (543874591/1250000000 : ℝ)*x 0 + (4480353079/10000000000 : ℝ)*x 1 + (4225296167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543874591/1250000000 : ℝ)^8433 ≤ (2082310461263/6250000000000 : ℝ)^6385 := by
    have hnat : (543874591 : ℕ)^8433*6250000000000^6385 ≤ 2082310461263^6385*1250000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543874591 1250000000 2082310461263 6250000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480353079/10000000000 : ℝ)^8433 ≤ (34631398288913/100000000000000 : ℝ)^6385 := by
    have hnat : (4480353079 : ℕ)^8433*100000000000000^6385 ≤ 34631398288913^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480353079 10000000000 34631398288913 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4225296167/10000000000 : ℝ)^8433 ≤ (32051634318233/100000000000000 : ℝ)^6385 := by
    have hnat : (4225296167 : ℕ)^8433*100000000000000^6385 ≤ 32051634318233^6385*10000000000^8433 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225296167 10000000000 32051634318233 100000000000000 8433 6385 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8433/2048 : ℝ)) 8433 6385 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543874591/1250000000 : ℝ), (4480353079/10000000000 : ℝ), (4225296167/10000000000 : ℝ)] ![(2082310461263/6250000000000 : ℝ), (34631398288913/100000000000000 : ℝ), (32051634318233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543874591/1250000000 : ℝ)|^8433 ≤ (2082310461263/6250000000000 : ℝ)^6385
        have hw : |(543874591/1250000000 : ℝ)|=(543874591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480353079/10000000000 : ℝ)|^8433 ≤ (34631398288913/100000000000000 : ℝ)^6385
        have hw : |(4480353079/10000000000 : ℝ)|=(4480353079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4225296167/10000000000 : ℝ)|^8433 ≤ (32051634318233/100000000000000 : ℝ)^6385
        have hw : |(4225296167/10000000000 : ℝ)|=(4225296167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1240_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2837/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14129/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2837/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2837/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2837/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2837/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2837/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2837/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2837/25000 : ℝ) ^ (527/128 : ℝ) ≤ (3212666730055991/25000000000000000000 : ℝ) := by
    have hpowers : (2837/25000 : ℝ)^527 ≤ (3212666730055991/25000000000000000000 : ℝ)^128 := by
      have hnat : (2837 : ℕ)^527*25000000000000000000^128 ≤ 3212666730055991^128*25000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2837 25000 3212666730055991 25000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2837/25000 : ℝ)) (X := (3212666730055991/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (527/128 : ℝ) ≤ (32693782482997327/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^527 ≤ (32693782482997327/100000000000000000000 : ℝ)^128 := by
      have hnat : (14237 : ℕ)^527*100000000000000000000^128 ≤ 32693782482997327^128*100000^527 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 32693782482997327 100000000000000000000 527 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (32693782482997327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503212666730055991/12500000000000000000 : ℝ) ≤ (2000124836838839/2000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (12503212666730055991/12500000000000000000 : ℝ)^128 ≤ (2000124836838839/2000000000000000 : ℝ)^527 := by
      have hnat : (12503212666730055991 : ℕ)^128*2000000000000000^527 ≤ 2000124836838839^527*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503212666730055991 12500000000000000000 2000124836838839 2000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000124836838839/2000000000000000 : ℝ)) (X := (12503212666730055991/12500000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045544449403221291/100000000000000000000 : ℝ) ≤ (2000221202454749/2000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (100045544449403221291/100000000000000000000 : ℝ)^128 ≤ (2000221202454749/2000000000000000 : ℝ)^527 := by
      have hnat : (100045544449403221291 : ℕ)^128*2000000000000000^527 ≤ 2000221202454749^527*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045544449403221291 100000000000000000000 2000221202454749 2000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000221202454749/2000000000000000 : ℝ)) (X := (100045544449403221291/100000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032693782482997327/50000000000000000000 : ℝ) ≤ (2000317568070659/2000000000000000 : ℝ) ^ (527/128 : ℝ) := by
    have hpowers : (50032693782482997327/50000000000000000000 : ℝ)^128 ≤ (2000317568070659/2000000000000000 : ℝ)^527 := by
      have hnat : (50032693782482997327 : ℕ)^128*2000000000000000^527 ≤ 2000317568070659^527*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032693782482997327 50000000000000000000 2000317568070659 2000000000000000 128 527 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000317568070659/2000000000000000 : ℝ)) (X := (50032693782482997327/50000000000000000000 : ℝ)) (by norm_num) 527 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3212666730055991/25000000000000000000 : ℝ) ≤ ((1925391179869570837/1926000000000000000 : ℝ)+2*(3212187197/1926000000000 : ℝ)*(2837/25000 : ℝ))^(527/128 : ℝ) := by
    rw [show (1925391179869570837/1926000000000000000 : ℝ)+2*(3212187197/1926000000000 : ℝ)*(2837/25000 : ℝ)=(2000124836838839/2000000000000000 : ℝ) by norm_num, show 1+2*(3212666730055991/25000000000000000000 : ℝ)=(12503212666730055991/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32693782482997327/100000000000000000000 : ℝ)+(3212666730055991/25000000000000000000 : ℝ) ≤ ((1925391179869570837/1926000000000000000 : ℝ)+(3212187197/1926000000000 : ℝ)*((14237/100000 : ℝ)+(2837/25000 : ℝ)))^(527/128 : ℝ) := by
    rw [show (1925391179869570837/1926000000000000000 : ℝ)+(3212187197/1926000000000 : ℝ)*((14237/100000 : ℝ)+(2837/25000 : ℝ))=(2000221202454749/2000000000000000 : ℝ) by norm_num, show 1+(32693782482997327/100000000000000000000 : ℝ)+(3212666730055991/25000000000000000000 : ℝ)=(100045544449403221291/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32693782482997327/100000000000000000000 : ℝ) ≤ ((1925391179869570837/1926000000000000000 : ℝ)+2*(3212187197/1926000000000 : ℝ)*(14237/100000 : ℝ))^(527/128 : ℝ) := by
    rw [show (1925391179869570837/1926000000000000000 : ℝ)+2*(3212187197/1926000000000 : ℝ)*(14237/100000 : ℝ)=(2000317568070659/2000000000000000 : ℝ) by norm_num, show 1+2*(32693782482997327/100000000000000000000 : ℝ)=(50032693782482997327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1925391179869570837/1926000000000000000 : ℝ)*(X 1 0+X 2 0)+(3212187197/1926000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (2837/25000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1925391179869570837/1926000000000000000 : ℝ)) (alpha := (3212187197/1926000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1925391179869570837/1926000000000000000 : ℝ)*(X 0 1+X 2 1)+(3212187197/1926000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (2837/25000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1925391179869570837/1926000000000000000 : ℝ)) (alpha := (3212187197/1926000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1925391179869570837/1926000000000000000 : ℝ)*(X 0 2+X 1 2)+(3212187197/1926000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (527/128 : ℝ)) (lo := (2837/25000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1925391179869570837/1926000000000000000 : ℝ)) (alpha := (3212187197/1926000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1060389571/5000000000 : ℝ)*X 0 0+(1348115463/2500000000 : ℝ)*X 0 1+(2633014663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344630023/10000000000 : ℝ)*X 1 0+(-2184901471/10000000000 : ℝ)*X 1 1+(5266029279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672315299/5000000000 : ℝ)*X 2 0+(5266029151/10000000000 : ℝ)*X 2 1+(-17479207/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217549297/500000000 : ℝ)*X 0 0+(4224635857/10000000000 : ℝ)*X 0 1+(4481011747/10000000000 : ℝ)*X 0 2+(217549297/500000000 : ℝ)*X 1 0+(4224635857/10000000000 : ℝ)*X 1 1+(4481011747/10000000000 : ℝ)*X 1 2+(217549297/500000000 : ℝ)*X 2 0+(4224635857/10000000000 : ℝ)*X 2 1+(4481011747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120784221/10000000000 : ℝ)*X 0 0+(5266354513/10000000000 : ℝ)*X 0 1+(16850423/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312375063/10000000000 : ℝ)*X 1 0+(-411759059/2000000000 : ℝ)*X 1 1+(5392135323/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656187521/5000000000 : ℝ)*X 2 0+(5392135393/10000000000 : ℝ)*X 2 1+(-2058795227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543874591/1250000000 : ℝ)*X 0 0+(4480353079/10000000000 : ℝ)*X 0 1+(4225296167/10000000000 : ℝ)*X 0 2+(543874591/1250000000 : ℝ)*X 1 0+(4480353079/10000000000 : ℝ)*X 1 1+(4225296167/10000000000 : ℝ)*X 1 2+(543874591/1250000000 : ℝ)*X 2 0+(4480353079/10000000000 : ℝ)*X 2 1+(4225296167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1240_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21947632797310785608871407/2675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (839893971/100000000000000 : ℝ)*(base19) + (446000091/25000000000000 : ℝ)*(base23) + (138178313/100000000000000 : ℝ)*(lower3) + (66630783/100000000000000 : ℝ)*(upper4) + (1476255045238167/25000000000000 : ℝ)*(major0) + (1476255045238167/25000000000000 : ℝ)*(major1) + (1476255045238167/25000000000000 : ℝ)*(major2) + (3954706388805461/50000000000000 : ℝ)*(sp0) + (79094514764357/1000000000000 : ℝ)*(sp1) + (7909486627626499/100000000000000 : ℝ)*(sp2) + (1950267771998963/50000000000000 : ℝ)*(sp3) + (75634015941/100000000000000 : ℝ)*(sp4) + (4511912149/12500000000000 : ℝ)*(sp5) + (16132789787/100000000000000 : ℝ)*(sp7) + (3809132496863/97656250000 : ℝ)*(f.failure) + (7909488411626863/100000000000000 : ℝ)*(f.sum) + (1767395293291/321000000000000000000000000 : ℝ)*base66 + (1302085077859531/5350000000000000000000000000000 : ℝ)*base67 + (33260955015009531/5350000000000000000000000000000 : ℝ)*base69 + (105880058561140469/5350000000000000000000000000000 : ℝ)*base72 + (69246552421/64200000000000000000000000 : ℝ)*base73 + (75059964750609531/5350000000000000000000000000000 : ℝ)*base75 + (27510035136759531/5350000000000000000000000000000 : ℝ)*base77 + (115816011857340469/5350000000000000000000000000000 : ℝ)*base80 + (447053389763/160500000000000000000000000 : ℝ)*base82 + (48221/4882812500000000000 : ℝ)*base89 + (48221/4882812500000000000 : ℝ)*base91 + (48221/4882812500000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84501462587676407677/40125000000000000000000000 : ℝ) := by norm_num
    linear_combination (263256753/100000000000000 : ℝ)*(base19) + (278453/62500000000 : ℝ)*(base23) + (18535719/50000000000000 : ℝ)*(upper3) + (20325879/25000000000000 : ℝ)*(lower4) + (271617/12500000000000 : ℝ)*(upper5) + (5935512925418227/100000000000000 : ℝ)*(major0) + (5935512925418227/100000000000000 : ℝ)*(major1) + (5935512925418227/100000000000000 : ℝ)*(major2) + (1086733823/25000000000000 : ℝ)*(sp1) + (7167885507/50000000000000 : ℝ)*(sp2) + (7950332170053167/100000000000000 : ℝ)*(sp4) + (3975163779930561/50000000000000 : ℝ)*(sp5) + (993789673594669/12500000000000 : ℝ)*(sp6) + (1960346805292381/50000000000000 : ℝ)*(sp7) + (1960346805292381/50000000000000 : ℝ)*(f.failure) + (7950332170053167/100000000000000 : ℝ)*(f.sum) + (4465595141137/963000000000000000000000000 : ℝ)*base66 + (1011596546940984667/64200000000000000000000000000000 : ℝ)*base68 + (1186510570761984667/64200000000000000000000000000000 : ℝ)*base70 + (212751620589215333/64200000000000000000000000000000 : ℝ)*base71 + (3404559525899/481500000000000000000000000 : ℝ)*base74 + (1805420511368784667/64200000000000000000000000000000 : ℝ)*base76 + (110851919782415333/64200000000000000000000000000000 : ℝ)*base77 + (252334804047215333/64200000000000000000000000000000 : ℝ)*base79 + (214421510789/96300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (17173779/5000000000000000000000 : ℝ)*base89 + (17173779/5000000000000000000000 : ℝ)*base91 + (17173779/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1240_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2837/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1240_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1240_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1240_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1240_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1240_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (527/128 : ℝ) ≤ p) (hpb : p ≤ (8433/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151389359/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4057/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9491/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14129/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1240_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

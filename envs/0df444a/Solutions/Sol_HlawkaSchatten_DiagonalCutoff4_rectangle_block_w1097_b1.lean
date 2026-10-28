-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1097_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:59:29.375379+00:00
-- url     : https://prove2.me/submissions/9a27f4bf-72bd-43be-885d-61088b49d093

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
theorem support_rectangle_w1097_s3_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-546065329/2500000000 : ℝ)*x 0 + (2717003477/5000000000 : ℝ)*x 1 + (2613824177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546065329/2500000000 : ℝ)^4145 ≤ (82872505711/625000000000 : ℝ)^3121 := by
    have hnat : (546065329 : ℕ)^4145*625000000000^3121 ≤ 82872505711^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546065329 2500000000 82872505711 625000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717003477/5000000000 : ℝ)^4145 ≤ (22242476324831/50000000000000 : ℝ)^3121 := by
    have hnat : (2717003477 : ℕ)^4145*50000000000000^3121 ≤ 22242476324831^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717003477 5000000000 22242476324831 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613824177/5000000000 : ℝ)^4145 ≤ (42255446413191/100000000000000 : ℝ)^3121 := by
    have hnat : (2613824177 : ℕ)^4145*100000000000000^3121 ≤ 42255446413191^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613824177 5000000000 42255446413191 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-546065329/2500000000 : ℝ), (2717003477/5000000000 : ℝ), (2613824177/5000000000 : ℝ)] ![(82872505711/625000000000 : ℝ), (22242476324831/50000000000000 : ℝ), (42255446413191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-546065329/2500000000 : ℝ)|^4145 ≤ (82872505711/625000000000 : ℝ)^3121
        have hw : |(-546065329/2500000000 : ℝ)|=(546065329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717003477/5000000000 : ℝ)|^4145 ≤ (22242476324831/50000000000000 : ℝ)^3121
        have hw : |(2717003477/5000000000 : ℝ)|=(2717003477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613824177/5000000000 : ℝ)|^4145 ≤ (42255446413191/100000000000000 : ℝ)^3121
        have hw : |(2613824177/5000000000 : ℝ)|=(2613824177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66936281/125000000 : ℝ)*x 0 + (-2289853281/10000000000 : ℝ)*x 1 + (5227648563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66936281/125000000 : ℝ)^4145 ≤ (10906740302017/25000000000000 : ℝ)^3121 := by
    have hnat : (66936281 : ℕ)^4145*25000000000000^3121 ≤ 10906740302017^3121*125000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66936281 125000000 10906740302017 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2289853281/10000000000 : ℝ)^4145 ≤ (7058795064757/50000000000000 : ℝ)^3121 := by
    have hnat : (2289853281 : ℕ)^4145*50000000000000^3121 ≤ 7058795064757^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289853281 10000000000 7058795064757 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227648563/10000000000 : ℝ)^4145 ≤ (660241385263/1562500000000 : ℝ)^3121 := by
    have hnat : (5227648563 : ℕ)^4145*1562500000000^3121 ≤ 660241385263^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227648563 10000000000 660241385263 1562500000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66936281/125000000 : ℝ), (-2289853281/10000000000 : ℝ), (5227648563/10000000000 : ℝ)] ![(10906740302017/25000000000000 : ℝ), (7058795064757/50000000000000 : ℝ), (660241385263/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66936281/125000000 : ℝ)|^4145 ≤ (10906740302017/25000000000000 : ℝ)^3121
        have hw : |(66936281/125000000 : ℝ)|=(66936281/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2289853281/10000000000 : ℝ)|^4145 ≤ (7058795064757/50000000000000 : ℝ)^3121
        have hw : |(-2289853281/10000000000 : ℝ)|=(2289853281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227648563/10000000000 : ℝ)|^4145 ≤ (660241385263/1562500000000 : ℝ)^3121
        have hw : |(5227648563/10000000000 : ℝ)|=(5227648563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677451317/5000000000 : ℝ)*x 0 + (5227648659/10000000000 : ℝ)*x 1 + (-45797059/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677451317/5000000000 : ℝ)^4145 ≤ (69803140599/160000000000 : ℝ)^3121 := by
    have hnat : (2677451317 : ℕ)^4145*160000000000^3121 ≤ 69803140599^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677451317 5000000000 69803140599 160000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227648659/10000000000 : ℝ)^4145 ≤ (10563862421851/25000000000000 : ℝ)^3121 := by
    have hnat : (5227648659 : ℕ)^4145*25000000000000^3121 ≤ 10563862421851^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227648659 10000000000 10563862421851 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45797059/200000000 : ℝ)^4145 ≤ (56470349677/400000000000 : ℝ)^3121 := by
    have hnat : (45797059 : ℕ)^4145*400000000000^3121 ≤ 56470349677^3121*200000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45797059 200000000 56470349677 400000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677451317/5000000000 : ℝ), (5227648659/10000000000 : ℝ), (-45797059/200000000 : ℝ)] ![(69803140599/160000000000 : ℝ), (10563862421851/25000000000000 : ℝ), (56470349677/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677451317/5000000000 : ℝ)|^4145 ≤ (69803140599/160000000000 : ℝ)^3121
        have hw : |(2677451317/5000000000 : ℝ)|=(2677451317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227648659/10000000000 : ℝ)|^4145 ≤ (10563862421851/25000000000000 : ℝ)^3121
        have hw : |(5227648659/10000000000 : ℝ)|=(5227648659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45797059/200000000 : ℝ)|^4145 ≤ (56470349677/400000000000 : ℝ)^3121
        have hw : |(-45797059/200000000 : ℝ)|=(45797059/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184242787/5000000000 : ℝ)*x 0 + (2084890733/5000000000 : ℝ)*x 1 + (4576704839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184242787/5000000000 : ℝ)^4145 ≤ (6658148593191/20000000000000 : ℝ)^3121 := by
    have hnat : (2184242787 : ℕ)^4145*20000000000000^3121 ≤ 6658148593191^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184242787 5000000000 6658148593191 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084890733/5000000000 : ℝ)^4145 ≤ (31294821501611/100000000000000 : ℝ)^3121 := by
    have hnat : (2084890733 : ℕ)^4145*100000000000000^3121 ≤ 31294821501611^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084890733 5000000000 31294821501611 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4576704839/10000000000 : ℝ)^4145 ≤ (35414435510263/100000000000000 : ℝ)^3121 := by
    have hnat : (4576704839 : ℕ)^4145*100000000000000^3121 ≤ 35414435510263^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4576704839 10000000000 35414435510263 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184242787/5000000000 : ℝ), (2084890733/5000000000 : ℝ), (4576704839/10000000000 : ℝ)] ![(6658148593191/20000000000000 : ℝ), (31294821501611/100000000000000 : ℝ), (35414435510263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184242787/5000000000 : ℝ)|^4145 ≤ (6658148593191/20000000000000 : ℝ)^3121
        have hw : |(2184242787/5000000000 : ℝ)|=(2184242787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084890733/5000000000 : ℝ)|^4145 ≤ (31294821501611/100000000000000 : ℝ)^3121
        have hw : |(2084890733/5000000000 : ℝ)|=(2084890733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4576704839/10000000000 : ℝ)|^4145 ≤ (35414435510263/100000000000000 : ℝ)^3121
        have hw : |(4576704839/10000000000 : ℝ)|=(4576704839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184282169/10000000000 : ℝ)*x 0 + (52284753/100000000 : ℝ)*x 1 + (5433174941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184282169/10000000000 : ℝ)^4145 ≤ (13259769036263/100000000000000 : ℝ)^3121 := by
    have hnat : (2184282169 : ℕ)^4145*100000000000000^3121 ≤ 13259769036263^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184282169 10000000000 13259769036263 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52284753/100000000 : ℝ)^4145 ≤ (8452864802399/20000000000000 : ℝ)^3121 := by
    have hnat : (52284753 : ℕ)^4145*20000000000000^3121 ≤ 8452864802399^3121*100000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52284753 100000000 8452864802399 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433174941/10000000000 : ℝ)^4145 ≤ (44475906934423/100000000000000 : ℝ)^3121 := by
    have hnat : (5433174941 : ℕ)^4145*100000000000000^3121 ≤ 44475906934423^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433174941 10000000000 44475906934423 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184282169/10000000000 : ℝ), (52284753/100000000 : ℝ), (5433174941/10000000000 : ℝ)] ![(13259769036263/100000000000000 : ℝ), (8452864802399/20000000000000 : ℝ), (44475906934423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184282169/10000000000 : ℝ)|^4145 ≤ (13259769036263/100000000000000 : ℝ)^3121
        have hw : |(-2184282169/10000000000 : ℝ)|=(2184282169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52284753/100000000 : ℝ)|^4145 ≤ (8452864802399/20000000000000 : ℝ)^3121
        have hw : |(52284753/100000000 : ℝ)|=(52284753/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433174941/10000000000 : ℝ)|^4145 ≤ (44475906934423/100000000000000 : ℝ)^3121
        have hw : |(5433174941/10000000000 : ℝ)|=(5433174941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302797333/10000000000 : ℝ)*x 0 + (-416865417/2000000000 : ℝ)*x 1 + (2716587501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302797333/10000000000 : ℝ)^4145 ≤ (8612815295813/20000000000000 : ℝ)^3121 := by
    have hnat : (5302797333 : ℕ)^4145*20000000000000^3121 ≤ 8612815295813^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302797333 10000000000 8612815295813 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416865417/2000000000 : ℝ)^4145 ≤ (6230007949557/50000000000000 : ℝ)^3121 := by
    have hnat : (416865417 : ℕ)^4145*50000000000000^3121 ≤ 6230007949557^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416865417 2000000000 6230007949557 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716587501/5000000000 : ℝ)^4145 ≤ (44475907597603/100000000000000 : ℝ)^3121 := by
    have hnat : (2716587501 : ℕ)^4145*100000000000000^3121 ≤ 44475907597603^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716587501 5000000000 44475907597603 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302797333/10000000000 : ℝ), (-416865417/2000000000 : ℝ), (2716587501/5000000000 : ℝ)] ![(8612815295813/20000000000000 : ℝ), (6230007949557/50000000000000 : ℝ), (44475907597603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302797333/10000000000 : ℝ)|^4145 ≤ (8612815295813/20000000000000 : ℝ)^3121
        have hw : |(5302797333/10000000000 : ℝ)|=(5302797333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416865417/2000000000 : ℝ)|^4145 ≤ (6230007949557/50000000000000 : ℝ)^3121
        have hw : |(-416865417/2000000000 : ℝ)|=(416865417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716587501/5000000000 : ℝ)|^4145 ≤ (44475907597603/100000000000000 : ℝ)^3121
        have hw : |(2716587501/5000000000 : ℝ)|=(2716587501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265139891/500000000 : ℝ)*x 0 + (2716587641/5000000000 : ℝ)*x 1 + (-2084326041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265139891/500000000 : ℝ)^4145 ≤ (43064081731611/100000000000000 : ℝ)^3121 := by
    have hnat : (265139891 : ℕ)^4145*100000000000000^3121 ≤ 43064081731611^3121*500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265139891 500000000 43064081731611 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716587641/5000000000 : ℝ)^4145 ≤ (4447591064171/10000000000000 : ℝ)^3121 := by
    have hnat : (2716587641 : ℕ)^4145*10000000000000^3121 ≤ 4447591064171^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716587641 5000000000 4447591064171 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084326041/10000000000 : ℝ)^4145 ≤ (6230003805231/50000000000000 : ℝ)^3121 := by
    have hnat : (2084326041 : ℕ)^4145*50000000000000^3121 ≤ 6230003805231^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084326041 10000000000 6230003805231 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265139891/500000000 : ℝ), (2716587641/5000000000 : ℝ), (-2084326041/10000000000 : ℝ)] ![(43064081731611/100000000000000 : ℝ), (4447591064171/10000000000000 : ℝ), (6230003805231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265139891/500000000 : ℝ)|^4145 ≤ (43064081731611/100000000000000 : ℝ)^3121
        have hw : |(265139891/500000000 : ℝ)|=(265139891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716587641/5000000000 : ℝ)|^4145 ≤ (4447591064171/10000000000000 : ℝ)^3121
        have hw : |(2716587641/5000000000 : ℝ)|=(2716587641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084326041/10000000000 : ℝ)|^4145 ≤ (6230003805231/50000000000000 : ℝ)^3121
        have hw : |(-2084326041/10000000000 : ℝ)|=(2084326041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s3_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34948203/80000000 : ℝ)*x 0 + (2287537509/5000000000 : ℝ)*x 1 + (4171421231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34948203/80000000 : ℝ)^4145 ≤ (33291145792407/100000000000000 : ℝ)^3121 := by
    have hnat : (34948203 : ℕ)^4145*100000000000000^3121 ≤ 33291145792407^3121*80000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34948203 80000000 33291145792407 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287537509/5000000000 : ℝ)^4145 ≤ (8849421783393/25000000000000 : ℝ)^3121 := by
    have hnat : (2287537509 : ℕ)^4145*25000000000000^3121 ≤ 8849421783393^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287537509 5000000000 8849421783393 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171421231/10000000000 : ℝ)^4145 ≤ (122309246301/390625000000 : ℝ)^3121 := by
    have hnat : (4171421231 : ℕ)^4145*390625000000^3121 ≤ 122309246301^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171421231 10000000000 122309246301 390625000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34948203/80000000 : ℝ), (2287537509/5000000000 : ℝ), (4171421231/10000000000 : ℝ)] ![(33291145792407/100000000000000 : ℝ), (8849421783393/25000000000000 : ℝ), (122309246301/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34948203/80000000 : ℝ)|^4145 ≤ (33291145792407/100000000000000 : ℝ)^3121
        have hw : |(34948203/80000000 : ℝ)|=(34948203/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2287537509/5000000000 : ℝ)|^4145 ≤ (8849421783393/25000000000000 : ℝ)^3121
        have hw : |(2287537509/5000000000 : ℝ)|=(2287537509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171421231/10000000000 : ℝ)|^4145 ≤ (122309246301/390625000000 : ℝ)^3121
        have hw : |(4171421231/10000000000 : ℝ)|=(4171421231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14863/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16641/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16641/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8861/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16641/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16641/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8861/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16641/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16641/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8861/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8861/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (1374106151163767/25000000000000000000 : ℝ) := by
    have hpowers : (8861/100000 : ℝ)^8289 ≤ (1374106151163767/25000000000000000000 : ℝ)^2048 := by
      have hnat : (8861 : ℕ)^8289*25000000000000000000^2048 ≤ 1374106151163767^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8861 100000 1374106151163767 25000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8861/100000 : ℝ)) (X := (1374106151163767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16641/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (70441757711746997/100000000000000000000 : ℝ) := by
    have hpowers : (16641/100000 : ℝ)^8289 ≤ (70441757711746997/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16641 : ℕ)^8289*100000000000000000000^2048 ≤ 70441757711746997^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16641 100000 70441757711746997 100000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16641/100000 : ℝ)) (X := (70441757711746997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501374106151163767/12500000000000000000 : ℝ) ≤ (5000135796981229/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (12501374106151163767/12500000000000000000 : ℝ)^2048 ≤ (5000135796981229/5000000000000000 : ℝ)^8289 := by
      have hnat : (12501374106151163767 : ℕ)^2048*5000000000000000^8289 ≤ 5000135796981229^8289*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501374106151163767 12500000000000000000 5000135796981229 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000135796981229/5000000000000000 : ℝ)) (X := (12501374106151163767/12500000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20015187636463280413/20000000000000000000 : ℝ) ≤ (5000937851108703/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (20015187636463280413/20000000000000000000 : ℝ)^2048 ≤ (5000937851108703/5000000000000000 : ℝ)^8289 := by
      have hnat : (20015187636463280413 : ℕ)^2048*5000000000000000^8289 ≤ 5000937851108703^8289*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20015187636463280413 20000000000000000000 5000937851108703 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000937851108703/5000000000000000 : ℝ)) (X := (20015187636463280413/20000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50070441757711746997/50000000000000000000 : ℝ) ≤ (5001739905236177/5000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (50070441757711746997/50000000000000000000 : ℝ)^2048 ≤ (5001739905236177/5000000000000000 : ℝ)^8289 := by
      have hnat : (50070441757711746997 : ℕ)^2048*5000000000000000^8289 ≤ 5001739905236177^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50070441757711746997 50000000000000000000 5001739905236177 5000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001739905236177/5000000000000000 : ℝ)) (X := (50070441757711746997/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1374106151163767/25000000000000000000 : ℝ) ≤ ((607606914019794803/607812500000000000 : ℝ)+2*(401027063737/194500000000000 : ℝ)*(8861/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (607606914019794803/607812500000000000 : ℝ)+2*(401027063737/194500000000000 : ℝ)*(8861/100000 : ℝ)=(5000135796981229/5000000000000000 : ℝ) by norm_num, show 1+2*(1374106151163767/25000000000000000000 : ℝ)=(12501374106151163767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(70441757711746997/100000000000000000000 : ℝ)+(1374106151163767/25000000000000000000 : ℝ) ≤ ((607606914019794803/607812500000000000 : ℝ)+(401027063737/194500000000000 : ℝ)*((16641/100000 : ℝ)+(8861/100000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (607606914019794803/607812500000000000 : ℝ)+(401027063737/194500000000000 : ℝ)*((16641/100000 : ℝ)+(8861/100000 : ℝ))=(5000937851108703/5000000000000000 : ℝ) by norm_num, show 1+(70441757711746997/100000000000000000000 : ℝ)+(1374106151163767/25000000000000000000 : ℝ)=(20015187636463280413/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(70441757711746997/100000000000000000000 : ℝ) ≤ ((607606914019794803/607812500000000000 : ℝ)+2*(401027063737/194500000000000 : ℝ)*(16641/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (607606914019794803/607812500000000000 : ℝ)+2*(401027063737/194500000000000 : ℝ)*(16641/100000 : ℝ)=(5001739905236177/5000000000000000 : ℝ) by norm_num, show 1+2*(70441757711746997/100000000000000000000 : ℝ)=(50070441757711746997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (607606914019794803/607812500000000000 : ℝ)*(X 1 0+X 2 0)+(401027063737/194500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (8861/100000 : ℝ)) (hi := (16641/100000 : ℝ)) (c := (607606914019794803/607812500000000000 : ℝ)) (alpha := (401027063737/194500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (607606914019794803/607812500000000000 : ℝ)*(X 0 1+X 2 1)+(401027063737/194500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (8861/100000 : ℝ)) (hi := (16641/100000 : ℝ)) (c := (607606914019794803/607812500000000000 : ℝ)) (alpha := (401027063737/194500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (607606914019794803/607812500000000000 : ℝ)*(X 0 2+X 1 2)+(401027063737/194500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (8861/100000 : ℝ)) (hi := (16641/100000 : ℝ)) (c := (607606914019794803/607812500000000000 : ℝ)) (alpha := (401027063737/194500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-546065329/2500000000 : ℝ)*X 0 0+(2717003477/5000000000 : ℝ)*X 0 1+(2613824177/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66936281/125000000 : ℝ)*X 1 0+(-2289853281/10000000000 : ℝ)*X 1 1+(5227648563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677451317/5000000000 : ℝ)*X 2 0+(5227648659/10000000000 : ℝ)*X 2 1+(-45797059/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184242787/5000000000 : ℝ)*X 0 0+(2084890733/5000000000 : ℝ)*X 0 1+(4576704839/10000000000 : ℝ)*X 0 2+(2184242787/5000000000 : ℝ)*X 1 0+(2084890733/5000000000 : ℝ)*X 1 1+(4576704839/10000000000 : ℝ)*X 1 2+(2184242787/5000000000 : ℝ)*X 2 0+(2084890733/5000000000 : ℝ)*X 2 1+(4576704839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184282169/10000000000 : ℝ)*X 0 0+(52284753/100000000 : ℝ)*X 0 1+(5433174941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302797333/10000000000 : ℝ)*X 1 0+(-416865417/2000000000 : ℝ)*X 1 1+(2716587501/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265139891/500000000 : ℝ)*X 2 0+(2716587641/5000000000 : ℝ)*X 2 1+(-2084326041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34948203/80000000 : ℝ)*X 0 0+(2287537509/5000000000 : ℝ)*X 0 1+(4171421231/10000000000 : ℝ)*X 0 2+(34948203/80000000 : ℝ)*X 1 0+(2287537509/5000000000 : ℝ)*X 1 1+(4171421231/10000000000 : ℝ)*X 1 2+(34948203/80000000 : ℝ)*X 2 0+(2287537509/5000000000 : ℝ)*X 2 1+(4171421231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6205434956072142800213229/6078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136759813/20000000000000 : ℝ)*(base19) + (657062519/100000000000000 : ℝ)*(base23) + (25430103/25000000000000 : ℝ)*(lower2) + (923923/800000000000 : ℝ)*(upper5) + (182586284310637/5000000000000 : ℝ)*(major0) + (182586284310637/5000000000000 : ℝ)*(major1) + (182586284310637/5000000000000 : ℝ)*(major2) + (2422974956261781/50000000000000 : ℝ)*(sp0) + (484597003448761/10000000000000 : ℝ)*(sp1) + (969194502610029/20000000000000 : ℝ)*(sp2) + (307183970789507/12500000000000 : ℝ)*(sp3) + (11628794551/50000000000000 : ℝ)*(sp4) + (245182599/10000000000000 : ℝ)*(sp5) + (6401965227/100000000000000 : ℝ)*(sp7) + (614369542070321/25000000000000 : ℝ)*(f.failure) + (605746646264083/12500000000000 : ℝ)*(f.sum) + (16855140783021/1945000000000000000000000000 : ℝ)*base65 + (28801597358169511/3039062500000000000000000000000 : ℝ)*base67 + (33025740610573397/6078125000000000000000000000000 : ℝ)*base69 + (49930043236635897/6078125000000000000000000000000 : ℝ)*base71 + (8381018583543/972500000000000000000000000 : ℝ)*base73 + (14529419818073397/6078125000000000000000000000000 : ℝ)*base75 + (99988116440698397/6078125000000000000000000000000 : ℝ)*base77 + (23833285342542147/6078125000000000000000000000000 : ℝ)*base79 + (3690038281781/1945000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3596947/500000000000000000000 : ℝ)*base90 + (3596947/500000000000000000000 : ℝ)*base92 + (3596947/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51266548613926637048642787/7597656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (760736153/50000000000000 : ℝ)*(base19) + (2663153167/100000000000000 : ℝ)*(base23) + (36544301/20000000000000 : ℝ)*(upper2) + (65017551/25000000000000 : ℝ)*(upper3) + (1010747/625000000000 : ℝ)*(upper5) + (460161171323867/12500000000000 : ℝ)*(major0) + (460161171323867/12500000000000 : ℝ)*(major1) + (460161171323867/12500000000000 : ℝ)*(major2) + (11301692507/50000000000000 : ℝ)*(sp1) + (29033270301/50000000000000 : ℝ)*(sp2) + (4885205066903657/100000000000000 : ℝ)*(sp4) + (4885180942046337/100000000000000 : ℝ)*(sp5) + (152660760537809/3125000000000 : ℝ)*(sp6) + (1238686724677783/50000000000000 : ℝ)*(sp7) + (1238686724677783/50000000000000 : ℝ)*(f.failure) + (4885205066903657/100000000000000 : ℝ)*(f.sum) + (10473639497493/9725000000000000000000000000 : ℝ)*base66 + (1396624163166231/1899414062500000000000000000000 : ℝ)*base68 + (94036215700894071/30390625000000000000000000000000 : ℝ)*base70 + (185690092334644071/30390625000000000000000000000000 : ℝ)*base72 + (2840354659693/9725000000000000000000000000 : ℝ)*base74 + (25945906721189223/15195312500000000000000000000000 : ℝ)*base76 + (11050743825251723/15195312500000000000000000000000 : ℝ)*base78 + (3448406920217027/15195312500000000000000000000000 : ℝ)*base79 + (18043093264141/4862500000000000000000000000 : ℝ)*base81 + (3567419/1000000000000000000000 : ℝ)*base89 + (3567419/1000000000000000000000 : ℝ)*base91 + (3567419/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1097_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14863/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1097_s4_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187644849/10000000000 : ℝ)*x 0 + (1351036797/2500000000 : ℝ)*x 1 + (5255296843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187644849/10000000000 : ℝ)^4145 ≤ (3321721688827/25000000000000 : ℝ)^3121 := by
    have hnat : (2187644849 : ℕ)^4145*25000000000000^3121 ≤ 3321721688827^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187644849 10000000000 3321721688827 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351036797/2500000000 : ℝ)^4145 ≤ (5520074952989/12500000000000 : ℝ)^3121 := by
    have hnat : (1351036797 : ℕ)^4145*12500000000000^3121 ≤ 5520074952989^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351036797 2500000000 5520074952989 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255296843/10000000000 : ℝ)^4145 ≤ (21276256805753/50000000000000 : ℝ)^3121 := by
    have hnat : (5255296843 : ℕ)^4145*50000000000000^3121 ≤ 21276256805753^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255296843 10000000000 21276256805753 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187644849/10000000000 : ℝ), (1351036797/2500000000 : ℝ), (5255296843/10000000000 : ℝ)] ![(3321721688827/25000000000000 : ℝ), (5520074952989/12500000000000 : ℝ), (21276256805753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187644849/10000000000 : ℝ)|^4145 ≤ (3321721688827/25000000000000 : ℝ)^3121
        have hw : |(-2187644849/10000000000 : ℝ)|=(2187644849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351036797/2500000000 : ℝ)|^4145 ≤ (5520074952989/12500000000000 : ℝ)^3121
        have hw : |(1351036797/2500000000 : ℝ)|=(1351036797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255296843/10000000000 : ℝ)|^4145 ≤ (21276256805753/50000000000000 : ℝ)^3121
        have hw : |(5255296843/10000000000 : ℝ)|=(5255296843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336870339/2500000000 : ℝ)*x 0 + (-2263327309/10000000000 : ℝ)*x 1 + (5255296691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336870339/2500000000 : ℝ)^4145 ≤ (43546681631441/100000000000000 : ℝ)^3121 := by
    have hnat : (1336870339 : ℕ)^4145*100000000000000^3121 ≤ 43546681631441^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336870339 2500000000 43546681631441 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263327309/10000000000 : ℝ)^4145 ≤ (13900806381171/100000000000000 : ℝ)^3121 := by
    have hnat : (2263327309 : ℕ)^4145*100000000000000^3121 ≤ 13900806381171^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263327309 10000000000 13900806381171 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255296691/10000000000 : ℝ)^4145 ≤ (42552511976941/100000000000000 : ℝ)^3121 := by
    have hnat : (5255296691 : ℕ)^4145*100000000000000^3121 ≤ 42552511976941^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255296691 10000000000 42552511976941 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336870339/2500000000 : ℝ), (-2263327309/10000000000 : ℝ), (5255296691/10000000000 : ℝ)] ![(43546681631441/100000000000000 : ℝ), (13900806381171/100000000000000 : ℝ), (42552511976941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336870339/2500000000 : ℝ)|^4145 ≤ (43546681631441/100000000000000 : ℝ)^3121
        have hw : |(1336870339/2500000000 : ℝ)|=(1336870339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263327309/10000000000 : ℝ)|^4145 ≤ (13900806381171/100000000000000 : ℝ)^3121
        have hw : |(-2263327309/10000000000 : ℝ)|=(2263327309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255296691/10000000000 : ℝ)|^4145 ≤ (42552511976941/100000000000000 : ℝ)^3121
        have hw : |(5255296691/10000000000 : ℝ)|=(5255296691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668435221/1250000000 : ℝ)*x 0 + (5255296569/10000000000 : ℝ)*x 1 + (-1131663461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668435221/1250000000 : ℝ)^4145 ≤ (10886671521831/25000000000000 : ℝ)^3121 := by
    have hnat : (668435221 : ℕ)^4145*25000000000000^3121 ≤ 10886671521831^3121*1250000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668435221 1250000000 10886671521831 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255296569/10000000000 : ℝ)^4145 ≤ (42552510664987/100000000000000 : ℝ)^3121 := by
    have hnat : (5255296569 : ℕ)^4145*100000000000000^3121 ≤ 42552510664987^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255296569 10000000000 42552510664987 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131663461/5000000000 : ℝ)^4145 ≤ (13900803224463/100000000000000 : ℝ)^3121 := by
    have hnat : (1131663461 : ℕ)^4145*100000000000000^3121 ≤ 13900803224463^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131663461 5000000000 13900803224463 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668435221/1250000000 : ℝ), (5255296569/10000000000 : ℝ), (-1131663461/5000000000 : ℝ)] ![(10886671521831/25000000000000 : ℝ), (42552510664987/100000000000000 : ℝ), (13900803224463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668435221/1250000000 : ℝ)|^4145 ≤ (10886671521831/25000000000000 : ℝ)^3121
        have hw : |(668435221/1250000000 : ℝ)|=(668435221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255296569/10000000000 : ℝ)|^4145 ≤ (42552510664987/100000000000000 : ℝ)^3121
        have hw : |(5255296569/10000000000 : ℝ)|=(5255296569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1131663461/5000000000 : ℝ)|^4145 ≤ (13900803224463/100000000000000 : ℝ)^3121
        have hw : |(-1131663461/5000000000 : ℝ)|=(1131663461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4370502867/10000000000 : ℝ)*x 0 + (4226218597/10000000000 : ℝ)*x 1 + (451974119/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370502867/10000000000 : ℝ)^4145 ≤ (6662232306267/20000000000000 : ℝ)^3121 := by
    have hnat : (4370502867 : ℕ)^4145*20000000000000^3121 ≤ 6662232306267^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370502867 10000000000 6662232306267 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226218597/10000000000 : ℝ)^4145 ≤ (31858608698483/100000000000000 : ℝ)^3121 := by
    have hnat : (4226218597 : ℕ)^4145*100000000000000^3121 ≤ 31858608698483^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226218597 10000000000 31858608698483 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451974119/1000000000 : ℝ)^4145 ≤ (34830229754019/100000000000000 : ℝ)^3121 := by
    have hnat : (451974119 : ℕ)^4145*100000000000000^3121 ≤ 34830229754019^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451974119 1000000000 34830229754019 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370502867/10000000000 : ℝ), (4226218597/10000000000 : ℝ), (451974119/1000000000 : ℝ)] ![(6662232306267/20000000000000 : ℝ), (31858608698483/100000000000000 : ℝ), (34830229754019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370502867/10000000000 : ℝ)|^4145 ≤ (6662232306267/20000000000000 : ℝ)^3121
        have hw : |(4370502867/10000000000 : ℝ)|=(4370502867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226218597/10000000000 : ℝ)|^4145 ≤ (31858608698483/100000000000000 : ℝ)^3121
        have hw : |(4226218597/10000000000 : ℝ)|=(4226218597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451974119/1000000000 : ℝ)|^4145 ≤ (34830229754019/100000000000000 : ℝ)^3121
        have hw : |(451974119/1000000000 : ℝ)|=(451974119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187653293/10000000000 : ℝ)*x 0 + (1051145499/2000000000 : ℝ)*x 1 + (42216517/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187653293/10000000000 : ℝ)^4145 ≤ (13286954867629/100000000000000 : ℝ)^3121 := by
    have hnat : (2187653293 : ℕ)^4145*100000000000000^3121 ≤ 13286954867629^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187653293 10000000000 13286954867629 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051145499/2000000000 : ℝ)^4145 ≤ (21278572392443/50000000000000 : ℝ)^3121 := by
    have hnat : (1051145499 : ℕ)^4145*50000000000000^3121 ≤ 21278572392443^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051145499 2000000000 21278572392443 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42216517/78125000 : ℝ)^4145 ≤ (22077950164059/50000000000000 : ℝ)^3121 := by
    have hnat : (42216517 : ℕ)^4145*50000000000000^3121 ≤ 22077950164059^3121*78125000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42216517 78125000 22077950164059 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187653293/10000000000 : ℝ), (1051145499/2000000000 : ℝ), (42216517/78125000 : ℝ)] ![(13286954867629/100000000000000 : ℝ), (21278572392443/50000000000000 : ℝ), (22077950164059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187653293/10000000000 : ℝ)|^4145 ≤ (13286954867629/100000000000000 : ℝ)^3121
        have hw : |(-2187653293/10000000000 : ℝ)|=(2187653293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051145499/2000000000 : ℝ)|^4145 ≤ (21278572392443/50000000000000 : ℝ)^3121
        have hw : |(1051145499/2000000000 : ℝ)|=(1051145499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42216517/78125000 : ℝ)|^4145 ≤ (22077950164059/50000000000000 : ℝ)^3121
        have hw : |(42216517/78125000 : ℝ)|=(42216517/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309899839/10000000000 : ℝ)*x 0 + (-1057454609/5000000000 : ℝ)*x 1 + (5403714389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309899839/10000000000 : ℝ)^4145 ≤ (21570348744439/50000000000000 : ℝ)^3121 := by
    have hnat : (5309899839 : ℕ)^4145*50000000000000^3121 ≤ 21570348744439^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309899839 10000000000 21570348744439 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057454609/5000000000 : ℝ)^4145 ≤ (12703399859001/100000000000000 : ℝ)^3121 := by
    have hnat : (1057454609 : ℕ)^4145*100000000000000^3121 ≤ 12703399859001^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057454609 5000000000 12703399859001 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403714389/10000000000 : ℝ)^4145 ≤ (44155902639687/100000000000000 : ℝ)^3121 := by
    have hnat : (5403714389 : ℕ)^4145*100000000000000^3121 ≤ 44155902639687^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403714389 10000000000 44155902639687 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309899839/10000000000 : ℝ), (-1057454609/5000000000 : ℝ), (5403714389/10000000000 : ℝ)] ![(21570348744439/50000000000000 : ℝ), (12703399859001/100000000000000 : ℝ), (44155902639687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309899839/10000000000 : ℝ)|^4145 ≤ (21570348744439/50000000000000 : ℝ)^3121
        have hw : |(5309899839/10000000000 : ℝ)|=(5309899839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057454609/5000000000 : ℝ)|^4145 ≤ (12703399859001/100000000000000 : ℝ)^3121
        have hw : |(-1057454609/5000000000 : ℝ)|=(1057454609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403714389/10000000000 : ℝ)|^4145 ≤ (44155902639687/100000000000000 : ℝ)^3121
        have hw : |(5403714389/10000000000 : ℝ)|=(5403714389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309899649/10000000000 : ℝ)*x 0 + (1350928651/2500000000 : ℝ)*x 1 + (-1057454591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309899649/10000000000 : ℝ)^4145 ≤ (4314069543873/10000000000000 : ℝ)^3121 := by
    have hnat : (5309899649 : ℕ)^4145*10000000000000^3121 ≤ 4314069543873^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309899649 10000000000 4314069543873 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1350928651/2500000000 : ℝ)^4145 ≤ (275974406081/625000000000 : ℝ)^3121 := by
    have hnat : (1350928651 : ℕ)^4145*625000000000^3121 ≤ 275974406081^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350928651 2500000000 275974406081 625000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057454591/5000000000 : ℝ)^4145 ≤ (1587924946477/12500000000000 : ℝ)^3121 := by
    have hnat : (1057454591 : ℕ)^4145*12500000000000^3121 ≤ 1587924946477^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057454591 5000000000 1587924946477 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309899649/10000000000 : ℝ), (1350928651/2500000000 : ℝ), (-1057454591/5000000000 : ℝ)] ![(4314069543873/10000000000000 : ℝ), (275974406081/625000000000 : ℝ), (1587924946477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309899649/10000000000 : ℝ)|^4145 ≤ (4314069543873/10000000000000 : ℝ)^3121
        have hw : |(5309899649/10000000000 : ℝ)|=(5309899649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1350928651/2500000000 : ℝ)|^4145 ≤ (275974406081/625000000000 : ℝ)^3121
        have hw : |(1350928651/2500000000 : ℝ)|=(1350928651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057454591/5000000000 : ℝ)|^4145 ≤ (1587924946477/12500000000000 : ℝ)^3121
        have hw : |(-1057454591/5000000000 : ℝ)|=(1057454591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s4_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4370517973/10000000000 : ℝ)*x 0 + (903778247/2000000000 : ℝ)*x 1 + (4227072157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370517973/10000000000 : ℝ)^4145 ≤ (33311314442381/100000000000000 : ℝ)^3121 := by
    have hnat : (4370517973 : ℕ)^4145*100000000000000^3121 ≤ 33311314442381^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370517973 10000000000 33311314442381 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903778247/2000000000 : ℝ)^4145 ≤ (34821531019577/100000000000000 : ℝ)^3121 := by
    have hnat : (903778247 : ℕ)^4145*100000000000000^3121 ≤ 34821531019577^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903778247 2000000000 34821531019577 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227072157/10000000000 : ℝ)^4145 ≤ (31867154524729/100000000000000 : ℝ)^3121 := by
    have hnat : (4227072157 : ℕ)^4145*100000000000000^3121 ≤ 31867154524729^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227072157 10000000000 31867154524729 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370517973/10000000000 : ℝ), (903778247/2000000000 : ℝ), (4227072157/10000000000 : ℝ)] ![(33311314442381/100000000000000 : ℝ), (34821531019577/100000000000000 : ℝ), (31867154524729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370517973/10000000000 : ℝ)|^4145 ≤ (33311314442381/100000000000000 : ℝ)^3121
        have hw : |(4370517973/10000000000 : ℝ)|=(4370517973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903778247/2000000000 : ℝ)|^4145 ≤ (34821531019577/100000000000000 : ℝ)^3121
        have hw : |(903778247/2000000000 : ℝ)|=(903778247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227072157/10000000000 : ℝ)|^4145 ≤ (31867154524729/100000000000000 : ℝ)^3121
        have hw : |(4227072157/10000000000 : ℝ)|=(4227072157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14239/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14863/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14863/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14863/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14863/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14863/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14863/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10497/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (1091177053110607/10000000000000000000 : ℝ) := by
    have hpowers : (10497/100000 : ℝ)^8289 ≤ (1091177053110607/10000000000000000000 : ℝ)^2048 := by
      have hnat : (10497 : ℕ)^8289*10000000000000000000^2048 ≤ 1091177053110607^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10497 100000 1091177053110607 10000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10497/100000 : ℝ)) (X := (1091177053110607/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14863/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (44587606268817963/100000000000000000000 : ℝ) := by
    have hpowers : (14863/100000 : ℝ)^8289 ≤ (44587606268817963/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14863 : ℕ)^8289*100000000000000000000^2048 ≤ 44587606268817963^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14863 100000 44587606268817963 100000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14863/100000 : ℝ)) (X := (44587606268817963/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001091177053110607/5000000000000000000 : ℝ) ≤ (1250067394951993/1250000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (5001091177053110607/5000000000000000000 : ℝ)^2048 ≤ (1250067394951993/1250000000000000 : ℝ)^8289 := by
      have hnat : (5001091177053110607 : ℕ)^2048*1250000000000000^8289 ≤ 1250067394951993^8289*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001091177053110607 5000000000000000000 1250067394951993 1250000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250067394951993/1250000000000000 : ℝ)) (X := (5001091177053110607/5000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055499376799924033/100000000000000000000 : ℝ) ≤ (2500342740328509/2500000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (100055499376799924033/100000000000000000000 : ℝ)^2048 ≤ (2500342740328509/2500000000000000 : ℝ)^8289 := by
      have hnat : (100055499376799924033 : ℕ)^2048*2500000000000000^8289 ≤ 2500342740328509^8289*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055499376799924033 100000000000000000000 2500342740328509 2500000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500342740328509/2500000000000000 : ℝ)) (X := (100055499376799924033/100000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044587606268817963/50000000000000000000 : ℝ) ≤ (312568836344129/312500000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (50044587606268817963/50000000000000000000 : ℝ)^2048 ≤ (312568836344129/312500000000000 : ℝ)^8289 := by
      have hnat : (50044587606268817963 : ℕ)^2048*312500000000000^8289 ≤ 312568836344129^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044587606268817963 50000000000000000000 312568836344129 312500000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312568836344129/312500000000000 : ℝ)) (X := (50044587606268817963/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1091177053110607/10000000000000000000 : ℝ) ≤ ((5455611390754183507/5457500000000000000 : ℝ)+2*(207950424523/109150000000000 : ℝ)*(10497/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (5455611390754183507/5457500000000000000 : ℝ)+2*(207950424523/109150000000000 : ℝ)*(10497/100000 : ℝ)=(1250067394951993/1250000000000000 : ℝ) by norm_num, show 1+2*(1091177053110607/10000000000000000000 : ℝ)=(5001091177053110607/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44587606268817963/100000000000000000000 : ℝ)+(1091177053110607/10000000000000000000 : ℝ) ≤ ((5455611390754183507/5457500000000000000 : ℝ)+(207950424523/109150000000000 : ℝ)*((14863/100000 : ℝ)+(10497/100000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (5455611390754183507/5457500000000000000 : ℝ)+(207950424523/109150000000000 : ℝ)*((14863/100000 : ℝ)+(10497/100000 : ℝ))=(2500342740328509/2500000000000000 : ℝ) by norm_num, show 1+(44587606268817963/100000000000000000000 : ℝ)+(1091177053110607/10000000000000000000 : ℝ)=(100055499376799924033/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44587606268817963/100000000000000000000 : ℝ) ≤ ((5455611390754183507/5457500000000000000 : ℝ)+2*(207950424523/109150000000000 : ℝ)*(14863/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (5455611390754183507/5457500000000000000 : ℝ)+2*(207950424523/109150000000000 : ℝ)*(14863/100000 : ℝ)=(312568836344129/312500000000000 : ℝ) by norm_num, show 1+2*(44587606268817963/100000000000000000000 : ℝ)=(50044587606268817963/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5455611390754183507/5457500000000000000 : ℝ)*(X 1 0+X 2 0)+(207950424523/109150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (14863/100000 : ℝ)) (c := (5455611390754183507/5457500000000000000 : ℝ)) (alpha := (207950424523/109150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5455611390754183507/5457500000000000000 : ℝ)*(X 0 1+X 2 1)+(207950424523/109150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (14863/100000 : ℝ)) (c := (5455611390754183507/5457500000000000000 : ℝ)) (alpha := (207950424523/109150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5455611390754183507/5457500000000000000 : ℝ)*(X 0 2+X 1 2)+(207950424523/109150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (10497/100000 : ℝ)) (hi := (14863/100000 : ℝ)) (c := (5455611390754183507/5457500000000000000 : ℝ)) (alpha := (207950424523/109150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2187644849/10000000000 : ℝ)*X 0 0+(1351036797/2500000000 : ℝ)*X 0 1+(5255296843/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336870339/2500000000 : ℝ)*X 1 0+(-2263327309/10000000000 : ℝ)*X 1 1+(5255296691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668435221/1250000000 : ℝ)*X 2 0+(5255296569/10000000000 : ℝ)*X 2 1+(-1131663461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370502867/10000000000 : ℝ)*X 0 0+(4226218597/10000000000 : ℝ)*X 0 1+(451974119/1000000000 : ℝ)*X 0 2+(4370502867/10000000000 : ℝ)*X 1 0+(4226218597/10000000000 : ℝ)*X 1 1+(451974119/1000000000 : ℝ)*X 1 2+(4370502867/10000000000 : ℝ)*X 2 0+(4226218597/10000000000 : ℝ)*X 2 1+(451974119/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2187653293/10000000000 : ℝ)*X 0 0+(1051145499/2000000000 : ℝ)*X 0 1+(42216517/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309899839/10000000000 : ℝ)*X 1 0+(-1057454609/5000000000 : ℝ)*X 1 1+(5403714389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309899649/10000000000 : ℝ)*X 2 0+(1350928651/2500000000 : ℝ)*X 2 1+(-1057454591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370517973/10000000000 : ℝ)*X 0 0+(903778247/2000000000 : ℝ)*X 0 1+(4227072157/10000000000 : ℝ)*X 0 2+(4370517973/10000000000 : ℝ)*X 1 0+(903778247/2000000000 : ℝ)*X 1 1+(4227072157/10000000000 : ℝ)*X 1 2+(4370517973/10000000000 : ℝ)*X 2 0+(903778247/2000000000 : ℝ)*X 2 1+(4227072157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (508019812364641786136149311/68218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8576309/20000000000000 : ℝ)*(base8) + (36447633/50000000000000 : ℝ)*(base21) + (396102007/100000000000000 : ℝ)*(lower2) + (61169897/100000000000000 : ℝ)*(lower4) + (2531258608663509/50000000000000 : ℝ)*(major0) + (2531258608663509/50000000000000 : ℝ)*(major1) + (2531258608663509/50000000000000 : ℝ)*(major2) + (1343628731300443/20000000000000 : ℝ)*(sp0) + (6718138337473607/100000000000000 : ℝ)*(sp1) + (6718144711867569/100000000000000 : ℝ)*(sp2) + (3406888002045259/100000000000000 : ℝ)*(sp3) + (542689537/50000000000000 : ℝ)*(sp4) + (6447289227/100000000000000 : ℝ)*(sp5) + (1399615149/100000000000000 : ℝ)*(sp7) + (425861175207551/12500000000000 : ℝ)*(f.failure) + (1343628956952567/20000000000000 : ℝ)*(f.sum) + (52181408823433/10915000000000000000000000000 : ℝ)*base65 + (2808859866747896063/272875000000000000000000000000000 : ℝ)*base67 + (1140468502913896063/272875000000000000000000000000000 : ℝ)*base69 + (2827149480895271063/272875000000000000000000000000000 : ℝ)*base71 + (33031704484107/10915000000000000000000000000 : ℝ)*base74 + (1486484516514771063/272875000000000000000000000000000 : ℝ)*base75 + (2753055979579853937/272875000000000000000000000000000 : ℝ)*base78 + (1684448491858771063/272875000000000000000000000000000 : ℝ)*base79 + (29286324791447/10915000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1018557/250000000000000000000 : ℝ)*base90 + (1018557/250000000000000000000 : ℝ)*base92 + (1018557/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37038519502952940693143949/3687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215919783/12500000000000 : ℝ)*(base19) + (755958721/50000000000000 : ℝ)*(base23) + (3433387/20000000000000 : ℝ)*(upper2) + (9570983/4000000000000 : ℝ)*(upper3) + (295141161/100000000000000 : ℝ)*(upper5) + (2546035887880351/50000000000000 : ℝ)*(major0) + (2546035887880351/50000000000000 : ℝ)*(major1) + (2546035887880351/50000000000000 : ℝ)*(major2) + (23534945463/50000000000000 : ℝ)*(sp1) + (46224598273/100000000000000 : ℝ)*(sp2) + (6757364675402961/100000000000000 : ℝ)*(sp4) + (675731587815377/10000000000000 : ℝ)*(sp5) + (3378658469443623/50000000000000 : ℝ)*(sp6) + (856694635326739/25000000000000 : ℝ)*(sp7) + (856694635326739/25000000000000 : ℝ)*(f.failure) + (6757364675402961/100000000000000 : ℝ)*(f.sum) + (1524287091691/295000000000000000000000000 : ℝ)*base65 + (83131350437929839/7375000000000000000000000000000 : ℝ)*base68 + (42124550001304839/7375000000000000000000000000000 : ℝ)*base70 + (96809729890554839/7375000000000000000000000000000 : ℝ)*base72 + (603277040823/147500000000000000000000000 : ℝ)*base73 + (27184623543804839/7375000000000000000000000000000 : ℝ)*base76 + (3139446551554839/7375000000000000000000000000000 : ℝ)*base78 + (170802792979679839/7375000000000000000000000000000 : ℝ)*base80 + (1001092660993/147500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2924473/500000000000000000000 : ℝ)*base90 + (2924473/500000000000000000000 : ℝ)*base92 + (2924473/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1097_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14863/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1097_s5_0 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2188390777/10000000000 : ℝ)*x 0 + (539612601/1000000000 : ℝ)*x 1 + (5262828571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188390777/10000000000 : ℝ)^4145 ≤ (13292904009823/100000000000000 : ℝ)^3121 := by
    have hnat : (2188390777 : ℕ)^4145*100000000000000^3121 ≤ 13292904009823^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188390777 10000000000 13292904009823 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539612601/1000000000 : ℝ)^4145 ≤ (1377299038639/3125000000000 : ℝ)^3121 := by
    have hnat : (539612601 : ℕ)^4145*3125000000000^3121 ≤ 1377299038639^3121*1000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539612601 1000000000 1377299038639 3125000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262828571/10000000000 : ℝ)^4145 ≤ (10658381685943/25000000000000 : ℝ)^3121 := by
    have hnat : (5262828571 : ℕ)^4145*25000000000000^3121 ≤ 10658381685943^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262828571 10000000000 10658381685943 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2188390777/10000000000 : ℝ), (539612601/1000000000 : ℝ), (5262828571/10000000000 : ℝ)] ![(13292904009823/100000000000000 : ℝ), (1377299038639/3125000000000 : ℝ), (10658381685943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2188390777/10000000000 : ℝ)|^4145 ≤ (13292904009823/100000000000000 : ℝ)^3121
        have hw : |(-2188390777/10000000000 : ℝ)|=(2188390777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539612601/1000000000 : ℝ)|^4145 ≤ (1377299038639/3125000000000 : ℝ)^3121
        have hw : |(539612601/1000000000 : ℝ)|=(539612601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262828571/10000000000 : ℝ)|^4145 ≤ (10658381685943/25000000000000 : ℝ)^3121
        have hw : |(5262828571/10000000000 : ℝ)|=(5262828571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_1 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345478267/10000000000 : ℝ)*x 0 + (-564011779/2500000000 : ℝ)*x 1 + (1315707143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345478267/10000000000 : ℝ)^4145 ≤ (2176250952749/5000000000000 : ℝ)^3121 := by
    have hnat : (5345478267 : ℕ)^4145*5000000000000^3121 ≤ 2176250952749^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345478267 10000000000 2176250952749 5000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564011779/2500000000 : ℝ)^4145 ≤ (13841454171177/100000000000000 : ℝ)^3121 := by
    have hnat : (564011779 : ℕ)^4145*100000000000000^3121 ≤ 13841454171177^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564011779 2500000000 13841454171177 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315707143/2500000000 : ℝ)^4145 ≤ (42633526754531/100000000000000 : ℝ)^3121 := by
    have hnat : (1315707143 : ℕ)^4145*100000000000000^3121 ≤ 42633526754531^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315707143 2500000000 42633526754531 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345478267/10000000000 : ℝ), (-564011779/2500000000 : ℝ), (1315707143/2500000000 : ℝ)] ![(2176250952749/5000000000000 : ℝ), (13841454171177/100000000000000 : ℝ), (42633526754531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345478267/10000000000 : ℝ)|^4145 ≤ (2176250952749/5000000000000 : ℝ)^3121
        have hw : |(5345478267/10000000000 : ℝ)|=(5345478267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564011779/2500000000 : ℝ)|^4145 ≤ (13841454171177/100000000000000 : ℝ)^3121
        have hw : |(-564011779/2500000000 : ℝ)|=(564011779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315707143/2500000000 : ℝ)|^4145 ≤ (42633526754531/100000000000000 : ℝ)^3121
        have hw : |(1315707143/2500000000 : ℝ)|=(1315707143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_2 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345478271/10000000000 : ℝ)*x 0 + (2631414277/5000000000 : ℝ)*x 1 + (-451209427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345478271/10000000000 : ℝ)^4145 ≤ (8705003819647/20000000000000 : ℝ)^3121 := by
    have hnat : (5345478271 : ℕ)^4145*20000000000000^3121 ≤ 8705003819647^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345478271 10000000000 8705003819647 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631414277/5000000000 : ℝ)^4145 ≤ (42633526560873/100000000000000 : ℝ)^3121 := by
    have hnat : (2631414277 : ℕ)^4145*100000000000000^3121 ≤ 42633526560873^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631414277 5000000000 42633526560873 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451209427/2000000000 : ℝ)^4145 ≤ (6920727162997/50000000000000 : ℝ)^3121 := by
    have hnat : (451209427 : ℕ)^4145*50000000000000^3121 ≤ 6920727162997^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451209427 2000000000 6920727162997 50000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345478271/10000000000 : ℝ), (2631414277/5000000000 : ℝ), (-451209427/2000000000 : ℝ)] ![(8705003819647/20000000000000 : ℝ), (42633526560873/100000000000000 : ℝ), (6920727162997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345478271/10000000000 : ℝ)|^4145 ≤ (8705003819647/20000000000000 : ℝ)^3121
        have hw : |(5345478271/10000000000 : ℝ)|=(5345478271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631414277/5000000000 : ℝ)|^4145 ≤ (42633526560873/100000000000000 : ℝ)^3121
        have hw : |(2631414277/5000000000 : ℝ)|=(2631414277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451209427/2000000000 : ℝ)|^4145 ≤ (6920727162997/50000000000000 : ℝ)^3121
        have hw : |(-451209427/2000000000 : ℝ)|=(451209427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_3 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092734067/2500000000 : ℝ)*x 0 + (2120748363/5000000000 : ℝ)*x 1 + (4504349851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092734067/2500000000 : ℝ)^4145 ≤ (1665777435897/5000000000000 : ℝ)^3121 := by
    have hnat : (1092734067 : ℕ)^4145*5000000000000^3121 ≤ 1665777435897^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092734067 2500000000 1665777435897 5000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120748363/5000000000 : ℝ)^4145 ≤ (6402331720643/20000000000000 : ℝ)^3121 := by
    have hnat : (2120748363 : ℕ)^4145*20000000000000^3121 ≤ 6402331720643^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120748363 5000000000 6402331720643 20000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504349851/10000000000 : ℝ)^4145 ≤ (8668198164453/25000000000000 : ℝ)^3121 := by
    have hnat : (4504349851 : ℕ)^4145*25000000000000^3121 ≤ 8668198164453^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504349851 10000000000 8668198164453 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092734067/2500000000 : ℝ), (2120748363/5000000000 : ℝ), (4504349851/10000000000 : ℝ)] ![(1665777435897/5000000000000 : ℝ), (6402331720643/20000000000000 : ℝ), (8668198164453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092734067/2500000000 : ℝ)|^4145 ≤ (1665777435897/5000000000000 : ℝ)^3121
        have hw : |(1092734067/2500000000 : ℝ)|=(1092734067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120748363/5000000000 : ℝ)|^4145 ≤ (6402331720643/20000000000000 : ℝ)^3121
        have hw : |(2120748363/5000000000 : ℝ)|=(2120748363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504349851/10000000000 : ℝ)|^4145 ≤ (8668198164453/25000000000000 : ℝ)^3121
        have hw : |(4504349851/10000000000 : ℝ)|=(4504349851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_4 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-136774761/625000000 : ℝ)*x 0 + (5263174429/10000000000 : ℝ)*x 1 + (1079155791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136774761/625000000 : ℝ)^4145 ≤ (3323236891237/25000000000000 : ℝ)^3121 := by
    have hnat : (136774761 : ℕ)^4145*25000000000000^3121 ≤ 3323236891237^3121*625000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136774761 625000000 3323236891237 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263174429/10000000000 : ℝ)^4145 ≤ (42637247792097/100000000000000 : ℝ)^3121 := by
    have hnat : (5263174429 : ℕ)^4145*100000000000000^3121 ≤ 42637247792097^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263174429 10000000000 42637247792097 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079155791/2000000000 : ℝ)^4145 ≤ (44069804620919/100000000000000 : ℝ)^3121 := by
    have hnat : (1079155791 : ℕ)^4145*100000000000000^3121 ≤ 44069804620919^3121*2000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079155791 2000000000 44069804620919 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136774761/625000000 : ℝ), (5263174429/10000000000 : ℝ), (1079155791/2000000000 : ℝ)] ![(3323236891237/25000000000000 : ℝ), (42637247792097/100000000000000 : ℝ), (44069804620919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136774761/625000000 : ℝ)|^4145 ≤ (3323236891237/25000000000000 : ℝ)^3121
        have hw : |(-136774761/625000000 : ℝ)|=(136774761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263174429/10000000000 : ℝ)|^4145 ≤ (42637247792097/100000000000000 : ℝ)^3121
        have hw : |(5263174429/10000000000 : ℝ)|=(5263174429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079155791/2000000000 : ℝ)|^4145 ≤ (44069804620919/100000000000000 : ℝ)^3121
        have hw : |(1079155791/2000000000 : ℝ)|=(1079155791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_5 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655911/5000000 : ℝ)*x 0 + (-2123096873/10000000000 : ℝ)*x 1 + (5395778853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655911/5000000 : ℝ)^4145 ≤ (43161439322619/100000000000000 : ℝ)^3121 := by
    have hnat : (2655911 : ℕ)^4145*100000000000000^3121 ≤ 43161439322619^3121*5000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655911 5000000 43161439322619 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123096873/10000000000 : ℝ)^4145 ≤ (12768757148773/100000000000000 : ℝ)^3121 := by
    have hnat : (2123096873 : ℕ)^4145*100000000000000^3121 ≤ 12768757148773^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123096873 10000000000 12768757148773 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395778853/10000000000 : ℝ)^4145 ≤ (5508725439313/12500000000000 : ℝ)^3121 := by
    have hnat : (5395778853 : ℕ)^4145*12500000000000^3121 ≤ 5508725439313^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395778853 10000000000 5508725439313 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655911/5000000 : ℝ), (-2123096873/10000000000 : ℝ), (5395778853/10000000000 : ℝ)] ![(43161439322619/100000000000000 : ℝ), (12768757148773/100000000000000 : ℝ), (5508725439313/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655911/5000000 : ℝ)|^4145 ≤ (43161439322619/100000000000000 : ℝ)^3121
        have hw : |(2655911/5000000 : ℝ)|=(2655911/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123096873/10000000000 : ℝ)|^4145 ≤ (12768757148773/100000000000000 : ℝ)^3121
        have hw : |(-2123096873/10000000000 : ℝ)|=(2123096873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395778853/10000000000 : ℝ)|^4145 ≤ (5508725439313/12500000000000 : ℝ)^3121
        have hw : |(5395778853/10000000000 : ℝ)|=(5395778853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_6 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655911017/5000000000 : ℝ)*x 0 + (5395778879/10000000000 : ℝ)*x 1 + (-2123096793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655911017/5000000000 : ℝ)^4145 ≤ (43161439689531/100000000000000 : ℝ)^3121 := by
    have hnat : (2655911017 : ℕ)^4145*100000000000000^3121 ≤ 43161439689531^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655911017 5000000000 43161439689531 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395778879/10000000000 : ℝ)^4145 ≤ (44069803796531/100000000000000 : ℝ)^3121 := by
    have hnat : (5395778879 : ℕ)^4145*100000000000000^3121 ≤ 44069803796531^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395778879 10000000000 44069803796531 100000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123096793/10000000000 : ℝ)^4145 ≤ (510750260391/4000000000000 : ℝ)^3121 := by
    have hnat : (2123096793 : ℕ)^4145*4000000000000^3121 ≤ 510750260391^3121*10000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123096793 10000000000 510750260391 4000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655911017/5000000000 : ℝ), (5395778879/10000000000 : ℝ), (-2123096793/10000000000 : ℝ)] ![(43161439689531/100000000000000 : ℝ), (44069803796531/100000000000000 : ℝ), (510750260391/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655911017/5000000000 : ℝ)|^4145 ≤ (43161439689531/100000000000000 : ℝ)^3121
        have hw : |(2655911017/5000000000 : ℝ)|=(2655911017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395778879/10000000000 : ℝ)|^4145 ≤ (44069803796531/100000000000000 : ℝ)^3121
        have hw : |(5395778879/10000000000 : ℝ)|=(5395778879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123096793/10000000000 : ℝ)|^4145 ≤ (510750260391/4000000000000 : ℝ)^3121
        have hw : |(-2123096793/10000000000 : ℝ)|=(2123096793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1097_s5_7 (p : ℝ) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2185473581/5000000000 : ℝ)*x 0 + (1125916983/2500000000 : ℝ)*x 1 + (2121090597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185473581/5000000000 : ℝ)^4145 ≤ (3331565899643/10000000000000 : ℝ)^3121 := by
    have hnat : (2185473581 : ℕ)^4145*10000000000000^3121 ≤ 3331565899643^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185473581 5000000000 3331565899643 10000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125916983/2500000000 : ℝ)^4145 ≤ (8666455356683/25000000000000 : ℝ)^3121 := by
    have hnat : (1125916983 : ℕ)^4145*25000000000000^3121 ≤ 8666455356683^3121*2500000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125916983 2500000000 8666455356683 25000000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121090597/5000000000 : ℝ)^4145 ≤ (4002314944543/12500000000000 : ℝ)^3121 := by
    have hnat : (2121090597 : ℕ)^4145*12500000000000^3121 ≤ 4002314944543^3121*5000000000^4145 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121090597 5000000000 4002314944543 12500000000000 4145 3121 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4145/1024 : ℝ)) 4145 3121 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185473581/5000000000 : ℝ), (1125916983/2500000000 : ℝ), (2121090597/5000000000 : ℝ)] ![(3331565899643/10000000000000 : ℝ), (8666455356683/25000000000000 : ℝ), (4002314944543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185473581/5000000000 : ℝ)|^4145 ≤ (3331565899643/10000000000000 : ℝ)^3121
        have hw : |(2185473581/5000000000 : ℝ)|=(2185473581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125916983/2500000000 : ℝ)|^4145 ≤ (8666455356683/25000000000000 : ℝ)^3121
        have hw : |(1125916983/2500000000 : ℝ)|=(1125916983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121090597/5000000000 : ℝ)|^4145 ≤ (4002314944543/12500000000000 : ℝ)^3121
        have hw : |(2121090597/5000000000 : ℝ)|=(2121090597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1097_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11247/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14239/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14239/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11087/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (3403732785342481/25000000000000000000 : ℝ) := by
    have hpowers : (11087/100000 : ℝ)^8289 ≤ (3403732785342481/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11087 : ℕ)^8289*25000000000000000000^2048 ≤ 3403732785342481^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11087 100000 3403732785342481 25000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11087/100000 : ℝ)) (X := (3403732785342481/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14239/100000 : ℝ) ^ (8289/2048 : ℝ) ≤ (37482104840613199/100000000000000000000 : ℝ) := by
    have hpowers : (14239/100000 : ℝ)^8289 ≤ (37482104840613199/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14239 : ℕ)^8289*100000000000000000000^2048 ≤ 37482104840613199^2048*100000^8289 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14239 100000 37482104840613199 100000000000000000000 8289 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14239/100000 : ℝ)) (X := (37482104840613199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503403732785342481/12500000000000000000 : ℝ) ≤ (200013454226613/200000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (12503403732785342481/12500000000000000000 : ℝ)^2048 ≤ (200013454226613/200000000000000 : ℝ)^8289 := by
      have hnat : (12503403732785342481 : ℕ)^2048*200000000000000^8289 ≤ 200013454226613^8289*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503403732785342481 12500000000000000000 200013454226613 200000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200013454226613/200000000000000 : ℝ)) (X := (12503403732785342481/12500000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051097035981983123/100000000000000000000 : ℝ) ≤ (10001262234355359/10000000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (100051097035981983123/100000000000000000000 : ℝ)^2048 ≤ (10001262234355359/10000000000000000 : ℝ)^8289 := by
      have hnat : (100051097035981983123 : ℕ)^2048*10000000000000000^8289 ≤ 10001262234355359^8289*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051097035981983123 100000000000000000000 10001262234355359 10000000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001262234355359/10000000000000000 : ℝ)) (X := (100051097035981983123/100000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037482104840613199/50000000000000000000 : ℝ) ≤ (2500462939345017/2500000000000000 : ℝ) ^ (8289/2048 : ℝ) := by
    have hpowers : (50037482104840613199/50000000000000000000 : ℝ)^2048 ≤ (2500462939345017/2500000000000000 : ℝ)^8289 := by
      have hnat : (50037482104840613199 : ℕ)^2048*2500000000000000^8289 ≤ 2500462939345017^8289*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037482104840613199 50000000000000000000 2500462939345017 2500000000000000 2048 8289 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500462939345017/2500000000000000 : ℝ)) (X := (50037482104840613199/50000000000000000000 : ℝ)) (by norm_num) 8289 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3403732785342481/25000000000000000000 : ℝ) ≤ ((15754524151282155717/15760000000000000000 : ℝ)+2*(589523024709/315200000000000 : ℝ)*(11087/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (15754524151282155717/15760000000000000000 : ℝ)+2*(589523024709/315200000000000 : ℝ)*(11087/100000 : ℝ)=(200013454226613/200000000000000 : ℝ) by norm_num, show 1+2*(3403732785342481/25000000000000000000 : ℝ)=(12503403732785342481/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37482104840613199/100000000000000000000 : ℝ)+(3403732785342481/25000000000000000000 : ℝ) ≤ ((15754524151282155717/15760000000000000000 : ℝ)+(589523024709/315200000000000 : ℝ)*((14239/100000 : ℝ)+(11087/100000 : ℝ)))^(8289/2048 : ℝ) := by
    rw [show (15754524151282155717/15760000000000000000 : ℝ)+(589523024709/315200000000000 : ℝ)*((14239/100000 : ℝ)+(11087/100000 : ℝ))=(10001262234355359/10000000000000000 : ℝ) by norm_num, show 1+(37482104840613199/100000000000000000000 : ℝ)+(3403732785342481/25000000000000000000 : ℝ)=(100051097035981983123/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37482104840613199/100000000000000000000 : ℝ) ≤ ((15754524151282155717/15760000000000000000 : ℝ)+2*(589523024709/315200000000000 : ℝ)*(14239/100000 : ℝ))^(8289/2048 : ℝ) := by
    rw [show (15754524151282155717/15760000000000000000 : ℝ)+2*(589523024709/315200000000000 : ℝ)*(14239/100000 : ℝ)=(2500462939345017/2500000000000000 : ℝ) by norm_num, show 1+2*(37482104840613199/100000000000000000000 : ℝ)=(50037482104840613199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15754524151282155717/15760000000000000000 : ℝ)*(X 1 0+X 2 0)+(589523024709/315200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15754524151282155717/15760000000000000000 : ℝ)) (alpha := (589523024709/315200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15754524151282155717/15760000000000000000 : ℝ)*(X 0 1+X 2 1)+(589523024709/315200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15754524151282155717/15760000000000000000 : ℝ)) (alpha := (589523024709/315200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15754524151282155717/15760000000000000000 : ℝ)*(X 0 2+X 1 2)+(589523024709/315200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8289/2048 : ℝ)) (lo := (11087/100000 : ℝ)) (hi := (14239/100000 : ℝ)) (c := (15754524151282155717/15760000000000000000 : ℝ)) (alpha := (589523024709/315200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2188390777/10000000000 : ℝ)*X 0 0+(539612601/1000000000 : ℝ)*X 0 1+(5262828571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345478267/10000000000 : ℝ)*X 1 0+(-564011779/2500000000 : ℝ)*X 1 1+(1315707143/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345478271/10000000000 : ℝ)*X 2 0+(2631414277/5000000000 : ℝ)*X 2 1+(-451209427/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092734067/2500000000 : ℝ)*X 0 0+(2120748363/5000000000 : ℝ)*X 0 1+(4504349851/10000000000 : ℝ)*X 0 2+(1092734067/2500000000 : ℝ)*X 1 0+(2120748363/5000000000 : ℝ)*X 1 1+(4504349851/10000000000 : ℝ)*X 1 2+(1092734067/2500000000 : ℝ)*X 2 0+(2120748363/5000000000 : ℝ)*X 2 1+(4504349851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-136774761/625000000 : ℝ)*X 0 0+(5263174429/10000000000 : ℝ)*X 0 1+(1079155791/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655911/5000000 : ℝ)*X 1 0+(-2123096873/10000000000 : ℝ)*X 1 1+(5395778853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655911017/5000000000 : ℝ)*X 2 0+(5395778879/10000000000 : ℝ)*X 2 1+(-2123096793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185473581/5000000000 : ℝ)*X 0 0+(1125916983/2500000000 : ℝ)*X 0 1+(2121090597/5000000000 : ℝ)*X 0 2+(2185473581/5000000000 : ℝ)*X 1 0+(1125916983/2500000000 : ℝ)*X 1 1+(2121090597/5000000000 : ℝ)*X 1 2+(2185473581/5000000000 : ℝ)*X 2 0+(1125916983/2500000000 : ℝ)*X 2 1+(2121090597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1097_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191783726369027026663095993/19700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188673431/10000000000000 : ℝ)*(base19) + (357546351/20000000000000 : ℝ)*(base23) + (1118449/2000000000000 : ℝ)*(lower2) + (24086909/10000000000000 : ℝ)*(upper3) + (67501177/50000000000000 : ℝ)*(upper5) + (282664475258543/5000000000000 : ℝ)*(major0) + (282664475258543/5000000000000 : ℝ)*(major1) + (282664475258543/5000000000000 : ℝ)*(major2) + (7502071920735669/100000000000000 : ℝ)*(sp0) + (750211919967427/10000000000000 : ℝ)*(sp1) + (3751059649338413/50000000000000 : ℝ)*(sp2) + (3804430400060099/100000000000000 : ℝ)*(sp3) + (3072854557/6250000000000 : ℝ)*(sp4) + (6799841469/25000000000000 : ℝ)*(sp7) + (152178303977039/4000000000000 : ℝ)*(f.failure) + (375106054320429/5000000000000 : ℝ)*(f.sum) + (1539834061043/157600000000000000000000000 : ℝ)*base65 + (1011263915917309669/78800000000000000000000000000000 : ℝ)*base68 + (1010850602667709669/78800000000000000000000000000000 : ℝ)*base70 + (796192104369309669/78800000000000000000000000000000 : ℝ)*base72 + (3131438578019/788000000000000000000000000 : ℝ)*base73 + (74239829370509669/78800000000000000000000000000000 : ℝ)*base76 + (96599464457890331/78800000000000000000000000000000 : ℝ)*base77 + (1598235003198109669/78800000000000000000000000000000 : ℝ)*base80 + (2334834644783/788000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (686573/80000000000000000000 : ℝ)*base90 + (686573/80000000000000000000 : ℝ)*base92 + (686573/80000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33713352223581707476659/3152000000000000000000000000 : ℝ) := by norm_num
    linear_combination (306971777/20000000000000 : ℝ)*(base19) + (1959529153/100000000000000 : ℝ)*(base23) + (151559829/100000000000000 : ℝ)*(upper3) + (157520029/100000000000000 : ℝ)*(lower4) + (166770167/100000000000000 : ℝ)*(upper5) + (227310062717431/4000000000000 : ℝ)*(major0) + (227310062717431/4000000000000 : ℝ)*(major1) + (227310062717431/4000000000000 : ℝ)*(major2) + (35968537437/100000000000000 : ℝ)*(sp1) + (48571619583/100000000000000 : ℝ)*(sp2) + (3770609143240541/50000000000000 : ℝ)*(sp4) + (7541180783084759/100000000000000 : ℝ)*(sp5) + (3770583877666173/50000000000000 : ℝ)*(sp6) + (152971379714471/4000000000000 : ℝ)*(sp7) + (152971379714471/4000000000000 : ℝ)*(f.failure) + (3770609143240541/50000000000000 : ℝ)*(f.sum) + (15630212360959/3152000000000000000000000000 : ℝ)*base65 + (86860783668033027/63040000000000000000000000000000 : ℝ)*base67 + (1308279800285246973/63040000000000000000000000000000 : ℝ)*base70 + (399718169924993027/63040000000000000000000000000000 : ℝ)*base71 + (22250425558257/3152000000000000000000000000 : ℝ)*base74 + (2313945704271486973/63040000000000000000000000000000 : ℝ)*base76 + (779130654512126973/63040000000000000000000000000000 : ℝ)*base78 + (59397978936513027/63040000000000000000000000000000 : ℝ)*base79 + (9899062675311/3152000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10997/80000000000000000000 : ℝ)*base90 + (10997/80000000000000000000 : ℝ)*base92 + (10997/80000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1097_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14239/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1097_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1097_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1097_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1097_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1097_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8289/2048 : ℝ) ≤ p) (hpb : p ≤ (4145/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29719293/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16641/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8861/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11247/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1097_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:39.140237+00:00
-- url     : https://prove2.me/submissions/a9f7c408-94dc-4365-8161-d2fbfedd77ba

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
theorem support_rectangle_w1687_box_0 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-290543657/2500000000 : ℝ)*x 0 + (271486747/500000000 : ℝ)*x 1 + (5429734941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290543657/2500000000 : ℝ)^5119 ≤ (1696180948177/25000000000000 : ℝ)^4095 := by
    have hnat : (290543657 : ℕ)^5119*25000000000000^4095 ≤ 1696180948177^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290543657 2500000000 1696180948177 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271486747/500000000 : ℝ)^5119 ≤ (46607638091349/100000000000000 : ℝ)^4095 := by
    have hnat : (271486747 : ℕ)^5119*100000000000000^4095 ≤ 46607638091349^4095*500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271486747 500000000 46607638091349 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429734941/10000000000 : ℝ)^5119 ≤ (46607638102079/100000000000000 : ℝ)^4095 := by
    have hnat : (5429734941 : ℕ)^5119*100000000000000^4095 ≤ 46607638102079^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429734941 10000000000 46607638102079 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-290543657/2500000000 : ℝ), (271486747/500000000 : ℝ), (5429734941/10000000000 : ℝ)] ![(1696180948177/25000000000000 : ℝ), (46607638091349/100000000000000 : ℝ), (46607638102079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-290543657/2500000000 : ℝ)|^5119 ≤ (1696180948177/25000000000000 : ℝ)^4095
        have hw : |(-290543657/2500000000 : ℝ)|=(290543657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271486747/500000000 : ℝ)|^5119 ≤ (46607638091349/100000000000000 : ℝ)^4095
        have hw : |(271486747/500000000 : ℝ)|=(271486747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429734941/10000000000 : ℝ)|^5119 ≤ (46607638102079/100000000000000 : ℝ)^4095
        have hw : |(5429734941/10000000000 : ℝ)|=(5429734941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_1 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522607653/1000000000 : ℝ)*x 0 + (-1451693851/10000000000 : ℝ)*x 1 + (5429734941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522607653/1000000000 : ℝ)^5119 ≤ (44432679199947/100000000000000 : ℝ)^4095 := by
    have hnat : (522607653 : ℕ)^5119*100000000000000^4095 ≤ 44432679199947^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522607653 1000000000 44432679199947 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1451693851/10000000000 : ℝ)^5119 ≤ (895968268491/10000000000000 : ℝ)^4095 := by
    have hnat : (1451693851 : ℕ)^5119*10000000000000^4095 ≤ 895968268491^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451693851 10000000000 895968268491 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429734941/10000000000 : ℝ)^5119 ≤ (46607638102079/100000000000000 : ℝ)^4095 := by
    have hnat : (5429734941 : ℕ)^5119*100000000000000^4095 ≤ 46607638102079^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429734941 10000000000 46607638102079 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522607653/1000000000 : ℝ), (-1451693851/10000000000 : ℝ), (5429734941/10000000000 : ℝ)] ![(44432679199947/100000000000000 : ℝ), (895968268491/10000000000000 : ℝ), (46607638102079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522607653/1000000000 : ℝ)|^5119 ≤ (44432679199947/100000000000000 : ℝ)^4095
        have hw : |(522607653/1000000000 : ℝ)|=(522607653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1451693851/10000000000 : ℝ)|^5119 ≤ (895968268491/10000000000000 : ℝ)^4095
        have hw : |(-1451693851/10000000000 : ℝ)|=(1451693851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429734941/10000000000 : ℝ)|^5119 ≤ (46607638102079/100000000000000 : ℝ)^4095
        have hw : |(5429734941/10000000000 : ℝ)|=(5429734941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_2 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522607653/1000000000 : ℝ)*x 0 + (5429734941/10000000000 : ℝ)*x 1 + (-1451693851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522607653/1000000000 : ℝ)^5119 ≤ (44432679199947/100000000000000 : ℝ)^4095 := by
    have hnat : (522607653 : ℕ)^5119*100000000000000^4095 ≤ 44432679199947^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522607653 1000000000 44432679199947 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429734941/10000000000 : ℝ)^5119 ≤ (46607638102079/100000000000000 : ℝ)^4095 := by
    have hnat : (5429734941 : ℕ)^5119*100000000000000^4095 ≤ 46607638102079^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429734941 10000000000 46607638102079 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1451693851/10000000000 : ℝ)^5119 ≤ (895968268491/10000000000000 : ℝ)^4095 := by
    have hnat : (1451693851 : ℕ)^5119*10000000000000^4095 ≤ 895968268491^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451693851 10000000000 895968268491 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522607653/1000000000 : ℝ), (5429734941/10000000000 : ℝ), (-1451693851/10000000000 : ℝ)] ![(44432679199947/100000000000000 : ℝ), (46607638102079/100000000000000 : ℝ), (895968268491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522607653/1000000000 : ℝ)|^5119 ≤ (44432679199947/100000000000000 : ℝ)^4095
        have hw : |(522607653/1000000000 : ℝ)|=(522607653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429734941/10000000000 : ℝ)|^5119 ≤ (46607638102079/100000000000000 : ℝ)^4095
        have hw : |(5429734941/10000000000 : ℝ)|=(5429734941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1451693851/10000000000 : ℝ)|^5119 ≤ (895968268491/10000000000000 : ℝ)^4095
        have hw : |(-1451693851/10000000000 : ℝ)|=(1451693851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_3 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2260056529/5000000000 : ℝ)*x 0 + (3965812969/10000000000 : ℝ)*x 1 + (495726621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260056529/5000000000 : ℝ)^5119 ≤ (3706086647879/10000000000000 : ℝ)^4095 := by
    have hnat : (2260056529 : ℕ)^5119*10000000000000^4095 ≤ 3706086647879^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260056529 5000000000 3706086647879 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3965812969/10000000000 : ℝ)^5119 ≤ (31469566756307/100000000000000 : ℝ)^4095 := by
    have hnat : (3965812969 : ℕ)^5119*100000000000000^4095 ≤ 31469566756307^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3965812969 10000000000 31469566756307 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495726621/1250000000 : ℝ)^5119 ≤ (31469566746387/100000000000000 : ℝ)^4095 := by
    have hnat : (495726621 : ℕ)^5119*100000000000000^4095 ≤ 31469566746387^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495726621 1250000000 31469566746387 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2260056529/5000000000 : ℝ), (3965812969/10000000000 : ℝ), (495726621/1250000000 : ℝ)] ![(3706086647879/10000000000000 : ℝ), (31469566756307/100000000000000 : ℝ), (31469566746387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2260056529/5000000000 : ℝ)|^5119 ≤ (3706086647879/10000000000000 : ℝ)^4095
        have hw : |(2260056529/5000000000 : ℝ)|=(2260056529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3965812969/10000000000 : ℝ)|^5119 ≤ (31469566756307/100000000000000 : ℝ)^4095
        have hw : |(3965812969/10000000000 : ℝ)|=(3965812969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(495726621/1250000000 : ℝ)|^5119 ≤ (31469566746387/100000000000000 : ℝ)^4095
        have hw : |(495726621/1250000000 : ℝ)|=(495726621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_4 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929145789/5000000000 : ℝ)*x 0 + (2587956207/5000000000 : ℝ)*x 1 + (129397819/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929145789/5000000000 : ℝ)^5119 ≤ (12199659309541/100000000000000 : ℝ)^4095 := by
    have hnat : (929145789 : ℕ)^5119*100000000000000^4095 ≤ 12199659309541^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929145789 5000000000 12199659309541 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587956207/5000000000 : ℝ)^5119 ≤ (4390016850287/10000000000000 : ℝ)^4095 := by
    have hnat : (2587956207 : ℕ)^5119*10000000000000^4095 ≤ 4390016850287^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587956207 5000000000 4390016850287 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129397819/250000000 : ℝ)^5119 ≤ (21950086085677/50000000000000 : ℝ)^4095 := by
    have hnat : (129397819 : ℕ)^5119*50000000000000^4095 ≤ 21950086085677^4095*250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129397819 250000000 21950086085677 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929145789/5000000000 : ℝ), (2587956207/5000000000 : ℝ), (129397819/250000000 : ℝ)] ![(12199659309541/100000000000000 : ℝ), (4390016850287/10000000000000 : ℝ), (21950086085677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929145789/5000000000 : ℝ)|^5119 ≤ (12199659309541/100000000000000 : ℝ)^4095
        have hw : |(-929145789/5000000000 : ℝ)|=(929145789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587956207/5000000000 : ℝ)|^5119 ≤ (4390016850287/10000000000000 : ℝ)^4095
        have hw : |(2587956207/5000000000 : ℝ)|=(2587956207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129397819/250000000 : ℝ)|^5119 ≤ (21950086085677/50000000000000 : ℝ)^4095
        have hw : |(129397819/250000000 : ℝ)|=(129397819/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_5 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699594673/5000000000 : ℝ)*x 0 + (-1562136039/10000000000 : ℝ)*x 1 + (646989039/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699594673/5000000000 : ℝ)^5119 ≤ (4628010720961/10000000000000 : ℝ)^4095 := by
    have hnat : (2699594673 : ℕ)^5119*10000000000000^4095 ≤ 4628010720961^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699594673 5000000000 4628010720961 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562136039/10000000000 : ℝ)^5119 ≤ (9819725354347/100000000000000 : ℝ)^4095 := by
    have hnat : (1562136039 : ℕ)^5119*100000000000000^4095 ≤ 9819725354347^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562136039 10000000000 9819725354347 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646989039/1250000000 : ℝ)^5119 ≤ (4390016742141/10000000000000 : ℝ)^4095 := by
    have hnat : (646989039 : ℕ)^5119*10000000000000^4095 ≤ 4390016742141^4095*1250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646989039 1250000000 4390016742141 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699594673/5000000000 : ℝ), (-1562136039/10000000000 : ℝ), (646989039/1250000000 : ℝ)] ![(4628010720961/10000000000000 : ℝ), (9819725354347/100000000000000 : ℝ), (4390016742141/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699594673/5000000000 : ℝ)|^5119 ≤ (4628010720961/10000000000000 : ℝ)^4095
        have hw : |(2699594673/5000000000 : ℝ)|=(2699594673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1562136039/10000000000 : ℝ)|^5119 ≤ (9819725354347/100000000000000 : ℝ)^4095
        have hw : |(-1562136039/10000000000 : ℝ)|=(1562136039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646989039/1250000000 : ℝ)|^5119 ≤ (4390016742141/10000000000000 : ℝ)^4095
        have hw : |(646989039/1250000000 : ℝ)|=(646989039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_6 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5399188869/10000000000 : ℝ)*x 0 + (1293978197/2500000000 : ℝ)*x 1 + (-1562136047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399188869/10000000000 : ℝ)^5119 ≤ (23140051049249/50000000000000 : ℝ)^4095 := by
    have hnat : (5399188869 : ℕ)^5119*50000000000000^4095 ≤ 23140051049249^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399188869 10000000000 23140051049249 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293978197/2500000000 : ℝ)^5119 ≤ (1756006898729/4000000000000 : ℝ)^4095 := by
    have hnat : (1293978197 : ℕ)^5119*4000000000000^4095 ≤ 1756006898729^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293978197 2500000000 1756006898729 4000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1562136047/10000000000 : ℝ)^5119 ≤ (9819725417211/100000000000000 : ℝ)^4095 := by
    have hnat : (1562136047 : ℕ)^5119*100000000000000^4095 ≤ 9819725417211^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562136047 10000000000 9819725417211 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399188869/10000000000 : ℝ), (1293978197/2500000000 : ℝ), (-1562136047/10000000000 : ℝ)] ![(23140051049249/50000000000000 : ℝ), (1756006898729/4000000000000 : ℝ), (9819725417211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399188869/10000000000 : ℝ)|^5119 ≤ (23140051049249/50000000000000 : ℝ)^4095
        have hw : |(5399188869/10000000000 : ℝ)|=(5399188869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293978197/2500000000 : ℝ)|^5119 ≤ (1756006898729/4000000000000 : ℝ)^4095
        have hw : |(1293978197/2500000000 : ℝ)|=(1293978197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1562136047/10000000000 : ℝ)|^5119 ≤ (9819725417211/100000000000000 : ℝ)^4095
        have hw : |(-1562136047/10000000000 : ℝ)|=(1562136047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_7 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (934062313/2500000000 : ℝ)*x 0 + (871375589/2000000000 : ℝ)*x 1 + (2178439041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (934062313/2500000000 : ℝ)^5119 ≤ (29209135174963/100000000000000 : ℝ)^4095 := by
    have hnat : (934062313 : ℕ)^5119*100000000000000^4095 ≤ 29209135174963^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934062313 2500000000 29209135174963 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871375589/2000000000 : ℝ)^5119 ≤ (17697715854859/50000000000000 : ℝ)^4095 := by
    have hnat : (871375589 : ℕ)^5119*50000000000000^4095 ≤ 17697715854859^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871375589 2000000000 17697715854859 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178439041/5000000000 : ℝ)^5119 ≤ (35395433101027/100000000000000 : ℝ)^4095 := by
    have hnat : (2178439041 : ℕ)^5119*100000000000000^4095 ≤ 35395433101027^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178439041 5000000000 35395433101027 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(934062313/2500000000 : ℝ), (871375589/2000000000 : ℝ), (2178439041/5000000000 : ℝ)] ![(29209135174963/100000000000000 : ℝ), (17697715854859/50000000000000 : ℝ), (35395433101027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(934062313/2500000000 : ℝ)|^5119 ≤ (29209135174963/100000000000000 : ℝ)^4095
        have hw : |(934062313/2500000000 : ℝ)|=(934062313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(871375589/2000000000 : ℝ)|^5119 ≤ (17697715854859/50000000000000 : ℝ)^4095
        have hw : |(871375589/2000000000 : ℝ)|=(871375589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2178439041/5000000000 : ℝ)|^5119 ≤ (35395433101027/100000000000000 : ℝ)^4095
        have hw : |(2178439041/5000000000 : ℝ)|=(2178439041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_8 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-854493959/5000000000 : ℝ)*x 0 + (4989817123/10000000000 : ℝ)*x 1 + (2736717547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (854493959/5000000000 : ℝ)^5119 ≤ (10986943702447/100000000000000 : ℝ)^4095 := by
    have hnat : (854493959 : ℕ)^5119*100000000000000^4095 ≤ 10986943702447^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854493959 5000000000 10986943702447 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989817123/10000000000 : ℝ)^5119 ≤ (20968016932087/50000000000000 : ℝ)^4095 := by
    have hnat : (4989817123 : ℕ)^5119*50000000000000^4095 ≤ 20968016932087^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989817123 10000000000 20968016932087 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736717547/5000000000 : ℝ)^5119 ≤ (11769255604769/25000000000000 : ℝ)^4095 := by
    have hnat : (2736717547 : ℕ)^5119*25000000000000^4095 ≤ 11769255604769^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736717547 5000000000 11769255604769 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-854493959/5000000000 : ℝ), (4989817123/10000000000 : ℝ), (2736717547/5000000000 : ℝ)] ![(10986943702447/100000000000000 : ℝ), (20968016932087/50000000000000 : ℝ), (11769255604769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-854493959/5000000000 : ℝ)|^5119 ≤ (10986943702447/100000000000000 : ℝ)^4095
        have hw : |(-854493959/5000000000 : ℝ)|=(854493959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989817123/10000000000 : ℝ)|^5119 ≤ (20968016932087/50000000000000 : ℝ)^4095
        have hw : |(4989817123/10000000000 : ℝ)|=(4989817123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736717547/5000000000 : ℝ)|^5119 ≤ (11769255604769/25000000000000 : ℝ)^4095
        have hw : |(2736717547/5000000000 : ℝ)|=(2736717547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_9 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196282089/10000000000 : ℝ)*x 0 + (-715917551/5000000000 : ℝ)*x 1 + (5473435231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196282089/10000000000 : ℝ)^5119 ≤ (8823249049287/20000000000000 : ℝ)^4095 := by
    have hnat : (5196282089 : ℕ)^5119*20000000000000^4095 ≤ 8823249049287^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196282089 10000000000 8823249049287 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (715917551/5000000000 : ℝ)^5119 ≤ (4403365424027/50000000000000 : ℝ)^4095 := by
    have hnat : (715917551 : ℕ)^5119*50000000000000^4095 ≤ 4403365424027^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715917551 5000000000 4403365424027 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473435231/10000000000 : ℝ)^5119 ≤ (4707702389207/10000000000000 : ℝ)^4095 := by
    have hnat : (5473435231 : ℕ)^5119*10000000000000^4095 ≤ 4707702389207^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473435231 10000000000 4707702389207 10000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196282089/10000000000 : ℝ), (-715917551/5000000000 : ℝ), (5473435231/10000000000 : ℝ)] ![(8823249049287/20000000000000 : ℝ), (4403365424027/50000000000000 : ℝ), (4707702389207/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196282089/10000000000 : ℝ)|^5119 ≤ (8823249049287/20000000000000 : ℝ)^4095
        have hw : |(5196282089/10000000000 : ℝ)|=(5196282089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-715917551/5000000000 : ℝ)|^5119 ≤ (4403365424027/50000000000000 : ℝ)^4095
        have hw : |(-715917551/5000000000 : ℝ)|=(715917551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473435231/10000000000 : ℝ)|^5119 ≤ (4707702389207/10000000000000 : ℝ)^4095
        have hw : |(5473435231/10000000000 : ℝ)|=(5473435231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_10 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039256423/2000000000 : ℝ)*x 0 + (547343527/1000000000 : ℝ)*x 1 + (-357958753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039256423/2000000000 : ℝ)^5119 ≤ (11029061380593/25000000000000 : ℝ)^4095 := by
    have hnat : (1039256423 : ℕ)^5119*25000000000000^4095 ≤ 11029061380593^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039256423 2000000000 11029061380593 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547343527/1000000000 : ℝ)^5119 ≤ (47077024311389/100000000000000 : ℝ)^4095 := by
    have hnat : (547343527 : ℕ)^5119*100000000000000^4095 ≤ 47077024311389^4095*1000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547343527 1000000000 47077024311389 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357958753/2500000000 : ℝ)^5119 ≤ (8806730156071/100000000000000 : ℝ)^4095 := by
    have hnat : (357958753 : ℕ)^5119*100000000000000^4095 ≤ 8806730156071^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357958753 2500000000 8806730156071 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039256423/2000000000 : ℝ), (547343527/1000000000 : ℝ), (-357958753/2500000000 : ℝ)] ![(11029061380593/25000000000000 : ℝ), (47077024311389/100000000000000 : ℝ), (8806730156071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039256423/2000000000 : ℝ)|^5119 ≤ (11029061380593/25000000000000 : ℝ)^4095
        have hw : |(1039256423/2000000000 : ℝ)|=(1039256423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547343527/1000000000 : ℝ)|^5119 ≤ (47077024311389/100000000000000 : ℝ)^4095
        have hw : |(547343527/1000000000 : ℝ)|=(547343527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357958753/2500000000 : ℝ)|^5119 ≤ (8806730156071/100000000000000 : ℝ)^4095
        have hw : |(-357958753/2500000000 : ℝ)|=(357958753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_11 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1162508739/2500000000 : ℝ)*x 0 + (779661581/2000000000 : ℝ)*x 1 + (121822123/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1162508739/2500000000 : ℝ)^5119 ≤ (38397236632907/100000000000000 : ℝ)^4095 := by
    have hnat : (1162508739 : ℕ)^5119*100000000000000^4095 ≤ 38397236632907^4095*2500000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162508739 2500000000 38397236632907 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (779661581/2000000000 : ℝ)^5119 ≤ (30801381522041/100000000000000 : ℝ)^4095 := by
    have hnat : (779661581 : ℕ)^5119*100000000000000^4095 ≤ 30801381522041^4095*2000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779661581 2000000000 30801381522041 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121822123/312500000 : ℝ)^5119 ≤ (7700345457057/25000000000000 : ℝ)^4095 := by
    have hnat : (121822123 : ℕ)^5119*25000000000000^4095 ≤ 7700345457057^4095*312500000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121822123 312500000 7700345457057 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1162508739/2500000000 : ℝ), (779661581/2000000000 : ℝ), (121822123/312500000 : ℝ)] ![(38397236632907/100000000000000 : ℝ), (30801381522041/100000000000000 : ℝ), (7700345457057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1162508739/2500000000 : ℝ)|^5119 ≤ (38397236632907/100000000000000 : ℝ)^4095
        have hw : |(1162508739/2500000000 : ℝ)|=(1162508739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(779661581/2000000000 : ℝ)|^5119 ≤ (30801381522041/100000000000000 : ℝ)^4095
        have hw : |(779661581/2000000000 : ℝ)|=(779661581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(121822123/312500000 : ℝ)|^5119 ≤ (7700345457057/25000000000000 : ℝ)^4095
        have hw : |(121822123/312500000 : ℝ)|=(121822123/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_12 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1306775111/10000000000 : ℝ)*x 0 + (2803261281/5000000000 : ℝ)*x 1 + (5150585753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306775111/10000000000 : ℝ)^5119 ≤ (3927960539253/50000000000000 : ℝ)^4095 := by
    have hnat : (1306775111 : ℕ)^5119*50000000000000^4095 ≤ 3927960539253^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306775111 10000000000 3927960539253 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2803261281/5000000000 : ℝ)^5119 ≤ (48512273210539/100000000000000 : ℝ)^4095 := by
    have hnat : (2803261281 : ℕ)^5119*100000000000000^4095 ≤ 48512273210539^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803261281 5000000000 48512273210539 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150585753/10000000000 : ℝ)^5119 ≤ (2726987856131/6250000000000 : ℝ)^4095 := by
    have hnat : (5150585753 : ℕ)^5119*6250000000000^4095 ≤ 2726987856131^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150585753 10000000000 2726987856131 6250000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1306775111/10000000000 : ℝ), (2803261281/5000000000 : ℝ), (5150585753/10000000000 : ℝ)] ![(3927960539253/50000000000000 : ℝ), (48512273210539/100000000000000 : ℝ), (2726987856131/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1306775111/10000000000 : ℝ)|^5119 ≤ (3927960539253/50000000000000 : ℝ)^4095
        have hw : |(-1306775111/10000000000 : ℝ)|=(1306775111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2803261281/5000000000 : ℝ)|^5119 ≤ (48512273210539/100000000000000 : ℝ)^4095
        have hw : |(2803261281/5000000000 : ℝ)|=(2803261281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150585753/10000000000 : ℝ)|^5119 ≤ (2726987856131/6250000000000 : ℝ)^4095
        have hw : |(5150585753/10000000000 : ℝ)|=(5150585753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_13 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2708244917/5000000000 : ℝ)*x 0 + (-1572678441/10000000000 : ℝ)*x 1 + (128764641/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708244917/5000000000 : ℝ)^5119 ≤ (2904097388477/6250000000000 : ℝ)^4095 := by
    have hnat : (2708244917 : ℕ)^5119*6250000000000^4095 ≤ 2904097388477^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708244917 5000000000 2904097388477 6250000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1572678441/10000000000 : ℝ)^5119 ≤ (9902637274001/100000000000000 : ℝ)^4095 := by
    have hnat : (1572678441 : ℕ)^5119*100000000000000^4095 ≤ 9902637274001^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572678441 10000000000 9902637274001 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128764641/250000000 : ℝ)^5119 ≤ (10907951125369/25000000000000 : ℝ)^4095 := by
    have hnat : (128764641 : ℕ)^5119*25000000000000^4095 ≤ 10907951125369^4095*250000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128764641 250000000 10907951125369 25000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708244917/5000000000 : ℝ), (-1572678441/10000000000 : ℝ), (128764641/250000000 : ℝ)] ![(2904097388477/6250000000000 : ℝ), (9902637274001/100000000000000 : ℝ), (10907951125369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708244917/5000000000 : ℝ)|^5119 ≤ (2904097388477/6250000000000 : ℝ)^4095
        have hw : |(2708244917/5000000000 : ℝ)|=(2708244917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1572678441/10000000000 : ℝ)|^5119 ≤ (9902637274001/100000000000000 : ℝ)^4095
        have hw : |(-1572678441/10000000000 : ℝ)|=(1572678441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128764641/250000000 : ℝ)|^5119 ≤ (10907951125369/25000000000000 : ℝ)^4095
        have hw : |(128764641/250000000 : ℝ)|=(128764641/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_14 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2708244803/5000000000 : ℝ)*x 0 + (5150586099/10000000000 : ℝ)*x 1 + (-1572678133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708244803/5000000000 : ℝ)^5119 ≤ (46465555770629/100000000000000 : ℝ)^4095 := by
    have hnat : (2708244803 : ℕ)^5119*100000000000000^4095 ≤ 46465555770629^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708244803 5000000000 46465555770629 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150586099/10000000000 : ℝ)^5119 ≤ (43631809362083/100000000000000 : ℝ)^4095 := by
    have hnat : (5150586099 : ℕ)^5119*100000000000000^4095 ≤ 43631809362083^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150586099 10000000000 43631809362083 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1572678133/10000000000 : ℝ)^5119 ≤ (1980526969933/20000000000000 : ℝ)^4095 := by
    have hnat : (1572678133 : ℕ)^5119*20000000000000^4095 ≤ 1980526969933^4095*10000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572678133 10000000000 1980526969933 20000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708244803/5000000000 : ℝ), (5150586099/10000000000 : ℝ), (-1572678133/10000000000 : ℝ)] ![(46465555770629/100000000000000 : ℝ), (43631809362083/100000000000000 : ℝ), (1980526969933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708244803/5000000000 : ℝ)|^5119 ≤ (46465555770629/100000000000000 : ℝ)^4095
        have hw : |(2708244803/5000000000 : ℝ)|=(2708244803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150586099/10000000000 : ℝ)|^5119 ≤ (43631809362083/100000000000000 : ℝ)^4095
        have hw : |(5150586099/10000000000 : ℝ)|=(5150586099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1572678133/10000000000 : ℝ)|^5119 ≤ (1980526969933/20000000000000 : ℝ)^4095
        have hw : |(-1572678133/10000000000 : ℝ)|=(1572678133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1687_box_15 (p : ℝ) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (114220483/312500000 : ℝ)*x 0 + (2197897177/5000000000 : ℝ)*x 1 + (2197897187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114220483/312500000 : ℝ)^5119 ≤ (28417821234281/100000000000000 : ℝ)^4095 := by
    have hnat : (114220483 : ℕ)^5119*100000000000000^4095 ≤ 28417821234281^4095*312500000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114220483 312500000 28417821234281 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197897177/5000000000 : ℝ)^5119 ≤ (17895544636599/50000000000000 : ℝ)^4095 := by
    have hnat : (2197897177 : ℕ)^5119*50000000000000^4095 ≤ 17895544636599^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197897177 5000000000 17895544636599 50000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197897187/5000000000 : ℝ)^5119 ≤ (35791089476761/100000000000000 : ℝ)^4095 := by
    have hnat : (2197897187 : ℕ)^5119*100000000000000^4095 ≤ 35791089476761^4095*5000000000^5119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197897187 5000000000 35791089476761 100000000000000 5119 4095 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5119/1024 : ℝ)) 5119 4095 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114220483/312500000 : ℝ), (2197897177/5000000000 : ℝ), (2197897187/5000000000 : ℝ)] ![(28417821234281/100000000000000 : ℝ), (17895544636599/50000000000000 : ℝ), (35791089476761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114220483/312500000 : ℝ)|^5119 ≤ (28417821234281/100000000000000 : ℝ)^4095
        have hw : |(114220483/312500000 : ℝ)|=(114220483/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2197897177/5000000000 : ℝ)|^5119 ≤ (17895544636599/50000000000000 : ℝ)^4095
        have hw : |(2197897177/5000000000 : ℝ)|=(2197897177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2197897187/5000000000 : ℝ)|^5119 ≤ (35791089476761/100000000000000 : ℝ)^4095
        have hw : |(2197897187/5000000000 : ℝ)|=(2197897187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1687_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66549/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57859/100000 : ℝ) ∧ (40349/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90087/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3451/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3451/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9801/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3451/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3451/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9801/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3451/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3451/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9801/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9801/100000 : ℝ) ^ (5111/1024 : ℝ) ≤ (461517037186041/50000000000000000000 : ℝ) := by
    have hpowers : (9801/100000 : ℝ)^5111 ≤ (461517037186041/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9801 : ℕ)^5111*50000000000000000000^1024 ≤ 461517037186041^1024*100000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9801 100000 461517037186041 50000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9801/100000 : ℝ)) (X := (461517037186041/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3451/20000 : ℝ) ^ (5111/1024 : ℝ) ≤ (15533939887690811/100000000000000000000 : ℝ) := by
    have hpowers : (3451/20000 : ℝ)^5111 ≤ (15533939887690811/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3451 : ℕ)^5111*100000000000000000000^1024 ≤ 15533939887690811^1024*20000^5111 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3451 20000 15533939887690811 100000000000000000000 5111 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3451/20000 : ℝ)) (X := (15533939887690811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000461517037186041/25000000000000000000 : ℝ) ≤ (10000036986105099/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (25000461517037186041/25000000000000000000 : ℝ)^1024 ≤ (10000036986105099/10000000000000000 : ℝ)^5111 := by
      have hnat : (25000461517037186041 : ℕ)^1024*10000000000000000^5111 ≤ 10000036986105099^5111*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000461517037186041 25000000000000000000 10000036986105099 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036986105099/10000000000000000 : ℝ)) (X := (25000461517037186041/25000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016456973962062893/100000000000000000000 : ℝ) ≤ (5000164848685259/5000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (100016456973962062893/100000000000000000000 : ℝ)^1024 ≤ (5000164848685259/5000000000000000 : ℝ)^5111 := by
      have hnat : (100016456973962062893 : ℕ)^1024*5000000000000000^5111 ≤ 5000164848685259^5111*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016456973962062893 100000000000000000000 5000164848685259 5000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000164848685259/5000000000000000 : ℝ)) (X := (100016456973962062893/100000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015533939887690811/50000000000000000000 : ℝ) ≤ (10000622408635937/10000000000000000 : ℝ) ^ (5111/1024 : ℝ) := by
    have hpowers : (50015533939887690811/50000000000000000000 : ℝ)^1024 ≤ (10000622408635937/10000000000000000 : ℝ)^5111 := by
      have hnat : (50015533939887690811 : ℕ)^1024*10000000000000000^5111 ≤ 10000622408635937^5111*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015533939887690811 50000000000000000000 10000622408635937 10000000000000000 1024 5111 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000622408635937/10000000000000000 : ℝ)) (X := (50015533939887690811/50000000000000000000 : ℝ)) (by norm_num) 5111 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(461517037186041/50000000000000000000 : ℝ) ≤ ((18633634492050666177/18635000000000000000 : ℝ)+2*(292711265419/745400000000000 : ℝ)*(9801/100000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (18633634492050666177/18635000000000000000 : ℝ)+2*(292711265419/745400000000000 : ℝ)*(9801/100000 : ℝ)=(10000036986105099/10000000000000000 : ℝ) by norm_num, show 1+2*(461517037186041/50000000000000000000 : ℝ)=(25000461517037186041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15533939887690811/100000000000000000000 : ℝ)+(461517037186041/50000000000000000000 : ℝ) ≤ ((18633634492050666177/18635000000000000000 : ℝ)+(292711265419/745400000000000 : ℝ)*((3451/20000 : ℝ)+(9801/100000 : ℝ)))^(5111/1024 : ℝ) := by
    rw [show (18633634492050666177/18635000000000000000 : ℝ)+(292711265419/745400000000000 : ℝ)*((3451/20000 : ℝ)+(9801/100000 : ℝ))=(5000164848685259/5000000000000000 : ℝ) by norm_num, show 1+(15533939887690811/100000000000000000000 : ℝ)+(461517037186041/50000000000000000000 : ℝ)=(100016456973962062893/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15533939887690811/100000000000000000000 : ℝ) ≤ ((18633634492050666177/18635000000000000000 : ℝ)+2*(292711265419/745400000000000 : ℝ)*(3451/20000 : ℝ))^(5111/1024 : ℝ) := by
    rw [show (18633634492050666177/18635000000000000000 : ℝ)+2*(292711265419/745400000000000 : ℝ)*(3451/20000 : ℝ)=(10000622408635937/10000000000000000 : ℝ) by norm_num, show 1+2*(15533939887690811/100000000000000000000 : ℝ)=(50015533939887690811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18633634492050666177/18635000000000000000 : ℝ)*(X 1 0+X 2 0)+(292711265419/745400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (3451/20000 : ℝ)) (c := (18633634492050666177/18635000000000000000 : ℝ)) (alpha := (292711265419/745400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18633634492050666177/18635000000000000000 : ℝ)*(X 0 1+X 2 1)+(292711265419/745400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (3451/20000 : ℝ)) (c := (18633634492050666177/18635000000000000000 : ℝ)) (alpha := (292711265419/745400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18633634492050666177/18635000000000000000 : ℝ)*(X 0 2+X 1 2)+(292711265419/745400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5111/1024 : ℝ)) (lo := (9801/100000 : ℝ)) (hi := (3451/20000 : ℝ)) (c := (18633634492050666177/18635000000000000000 : ℝ)) (alpha := (292711265419/745400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-290543657/2500000000 : ℝ)*X 0 0+(271486747/500000000 : ℝ)*X 0 1+(5429734941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((522607653/1000000000 : ℝ)*X 1 0+(-1451693851/10000000000 : ℝ)*X 1 1+(5429734941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((522607653/1000000000 : ℝ)*X 2 0+(5429734941/10000000000 : ℝ)*X 2 1+(-1451693851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2260056529/5000000000 : ℝ)*X 0 0+(3965812969/10000000000 : ℝ)*X 0 1+(495726621/1250000000 : ℝ)*X 0 2+(2260056529/5000000000 : ℝ)*X 1 0+(3965812969/10000000000 : ℝ)*X 1 1+(495726621/1250000000 : ℝ)*X 1 2+(2260056529/5000000000 : ℝ)*X 2 0+(3965812969/10000000000 : ℝ)*X 2 1+(495726621/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929145789/5000000000 : ℝ)*X 0 0+(2587956207/5000000000 : ℝ)*X 0 1+(129397819/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2699594673/5000000000 : ℝ)*X 1 0+(-1562136039/10000000000 : ℝ)*X 1 1+(646989039/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5399188869/10000000000 : ℝ)*X 2 0+(1293978197/2500000000 : ℝ)*X 2 1+(-1562136047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((934062313/2500000000 : ℝ)*X 0 0+(871375589/2000000000 : ℝ)*X 0 1+(2178439041/5000000000 : ℝ)*X 0 2+(934062313/2500000000 : ℝ)*X 1 0+(871375589/2000000000 : ℝ)*X 1 1+(2178439041/5000000000 : ℝ)*X 1 2+(934062313/2500000000 : ℝ)*X 2 0+(871375589/2000000000 : ℝ)*X 2 1+(2178439041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-854493959/5000000000 : ℝ)*X 0 0+(4989817123/10000000000 : ℝ)*X 0 1+(2736717547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196282089/10000000000 : ℝ)*X 1 0+(-715917551/5000000000 : ℝ)*X 1 1+(5473435231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1039256423/2000000000 : ℝ)*X 2 0+(547343527/1000000000 : ℝ)*X 2 1+(-357958753/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1162508739/2500000000 : ℝ)*X 0 0+(779661581/2000000000 : ℝ)*X 0 1+(121822123/312500000 : ℝ)*X 0 2+(1162508739/2500000000 : ℝ)*X 1 0+(779661581/2000000000 : ℝ)*X 1 1+(121822123/312500000 : ℝ)*X 1 2+(1162508739/2500000000 : ℝ)*X 2 0+(779661581/2000000000 : ℝ)*X 2 1+(121822123/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1306775111/10000000000 : ℝ)*X 0 0+(2803261281/5000000000 : ℝ)*X 0 1+(5150585753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2708244917/5000000000 : ℝ)*X 1 0+(-1572678441/10000000000 : ℝ)*X 1 1+(128764641/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2708244803/5000000000 : ℝ)*X 2 0+(5150586099/10000000000 : ℝ)*X 2 1+(-1572678133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((114220483/312500000 : ℝ)*X 0 0+(2197897177/5000000000 : ℝ)*X 0 1+(2197897187/5000000000 : ℝ)*X 0 2+(114220483/312500000 : ℝ)*X 1 0+(2197897177/5000000000 : ℝ)*X 1 1+(2197897187/5000000000 : ℝ)*X 1 2+(114220483/312500000 : ℝ)*X 2 0+(2197897177/5000000000 : ℝ)*X 2 1+(2197897187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1687_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66549/100000 : ℝ) ≤ (-620045379775650190846317300369627/931750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14786019/25000000000000 : ℝ)*(upper1) + (14905167/20000000000000 : ℝ)*(lower4) + (14013053/25000000000000 : ℝ)*(upper5) + (1297799755903383/100000000000000 : ℝ)*(major0) + (1297799755903383/100000000000000 : ℝ)*(major1) + (1297799755903383/100000000000000 : ℝ)*(major2) + (1029137219/100000000000000 : ℝ)*(sp1) + (7372021/25000000000000 : ℝ)*(sp2) + (451074607/20000000000000 : ℝ)*(sp3) + (1925178732175809/100000000000000 : ℝ)*(sp4) + (962589045406499/50000000000000 : ℝ)*(sp5) + (1925179090462133/100000000000000 : ℝ)*(sp6) + (346300122347393/50000000000000 : ℝ)*(sp7) + (48471801/12500000000000 : ℝ)*(sp12) + (692602500067821/100000000000000 : ℝ)*(f.failure) + (1925179119950217/100000000000000 : ℝ)*(f.sum) + (114717397461237/37270000000000000000000000000 : ℝ)*base65 + (5040195170215401791/1863500000000000000000000000000000 : ℝ)*base67 + (5176925274036098209/1863500000000000000000000000000000 : ℝ)*base70 + (298934655570098209/1863500000000000000000000000000000 : ℝ)*base72 + (186103789628097/37270000000000000000000000000 : ℝ)*base73 + (6122465879335401791/1863500000000000000000000000000000 : ℝ)*base75 + (1456870171426598209/1863500000000000000000000000000000 : ℝ)*base78 + (3551683321835598209/1863500000000000000000000000000000 : ℝ)*base80 + (154707235902287/37270000000000000000000000000 : ℝ)*base81 + (2661303/2500000000000000000000 : ℝ)*base89 + (2661303/2500000000000000000000 : ℝ)*base91 + (2661303/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (57859/100000 : ℝ) ≤ (134780042491100491652054084362173/232937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16667/10000000000000 : ℝ)*(lower0) + (9217/10000000000000 : ℝ)*(lower1) + (6819/50000000000000 : ℝ)*(lower3) + (6819/50000000000000 : ℝ)*(lower5) + (348993766773817/25000000000000 : ℝ)*(major0) + (348993766773817/25000000000000 : ℝ)*(major1) + (348993766773817/25000000000000 : ℝ)*(major2) + (1013833485323167/50000000000000 : ℝ)*(sp0) + (1013833486729797/50000000000000 : ℝ)*(sp1) + (1013833486729797/50000000000000 : ℝ)*(sp2) + (744996149693259/100000000000000 : ℝ)*(sp3) + (8681/4000000000000 : ℝ)*(sp7) + (140663/5000000000000 : ℝ)*(sp12) + (186249037477571/25000000000000 : ℝ)*(f.failure) + (1013833486729797/50000000000000 : ℝ)*(f.sum) + (2960762234301/4658750000000000000000000000 : ℝ)*base66 + (328923611732662609/465875000000000000000000000000000 : ℝ)*base67 + (632362006057337391/465875000000000000000000000000000 : ℝ)*base70 + (950518045134912609/465875000000000000000000000000000 : ℝ)*base71 + (12721860278219/4658750000000000000000000000 : ℝ)*base73 + (280455349027337391/465875000000000000000000000000000 : ℝ)*base76 + (950518045134912609/465875000000000000000000000000000 : ℝ)*base77 + (1527157897432912609/465875000000000000000000000000000 : ℝ)*base79 + (10708544372767/9317500000000000000000000000 : ℝ)*base82 + (30553/625000000000000000000 : ℝ)*base89 + (30553/625000000000000000000 : ℝ)*base91 + (30553/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40349/50000 : ℝ) ≤ (9399140370502553281630061252049/11646875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6705919/100000000000000 : ℝ)*(upper0) + (1760983/25000000000000 : ℝ)*(lower3) + (1013311/6250000000000 : ℝ)*(upper4) + (8928135754799/625000000000 : ℝ)*(major0) + (8928135754799/625000000000 : ℝ)*(major1) + (8928135754799/625000000000 : ℝ)*(major2) + (10477762653/100000000000000 : ℝ)*(sp1) + (14114973737/100000000000000 : ℝ)*(sp2) + (707769657/20000000000000 : ℝ)*(sp3) + (350092803/100000000000000 : ℝ)*(sp4) + (6461712431417/312500000000 : ℝ)*(sp8) + (206773785038359/10000000000000 : ℝ)*(sp9) + (1033867106586253/50000000000000 : ℝ)*(sp10) + (381175626647369/50000000000000 : ℝ)*(sp11) + (47647174508939/6250000000000 : ℝ)*(f.failure) + (2067748328146243/100000000000000 : ℝ)*(f.sum) + (2198830021397/931750000000000000000000000 : ℝ)*base65 + (5380038684065387/2911718750000000000000000000000 : ℝ)*base67 + (70593462746208423/11646875000000000000000000000000 : ℝ)*base69 + (70374147780614673/11646875000000000000000000000000 : ℝ)*base71 + (2239815627887/931750000000000000000000000 : ℝ)*base74 + (21705246819321399/5823437500000000000000000000000 : ℝ)*base75 + (63511003066864673/11646875000000000000000000000000 : ℝ)*base77 + (46033136232566577/11646875000000000000000000000000 : ℝ)*base80 + (18912584399693/3727000000000000000000000000 : ℝ)*base81 + (1339377/156250000000000000000 : ℝ)*base89 + (1339377/156250000000000000000 : ℝ)*base91 + (1339377/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-90087/100000 : ℝ) ≤ (-209840523445061872078949854156923/232937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69577861/100000000000000 : ℝ)*(lower0) + (44160217/50000000000000 : ℝ)*(lower1) + (32675779/100000000000000 : ℝ)*(lower2) + (368823341907189/25000000000000 : ℝ)*(major0) + (368823341907189/25000000000000 : ℝ)*(major1) + (368823341907189/25000000000000 : ℝ)*(major2) + (2238580429/100000000000000 : ℝ)*(sp0) + (69331803981/100000000000000 : ℝ)*(sp5) + (21539339667/100000000000000 : ℝ)*(sp6) + (4240507257/100000000000000 : ℝ)*(sp7) + (2193286358946927/100000000000000 : ℝ)*(sp12) + (17545754125787/800000000000 : ℝ)*(sp13) + (2193267058187689/100000000000000 : ℝ)*(sp14) + (31492882219341/4000000000000 : ℝ)*(sp15) + (393663147995391/50000000000000 : ℝ)*(f.failure) + (548322149381839/25000000000000 : ℝ)*(f.sum) + (6926670228543/18635000000000000000000000000 : ℝ)*base66 + (1041840065530153547/465875000000000000000000000000000 : ℝ)*base68 + (2347738561750778547/465875000000000000000000000000000 : ℝ)*base70 + (1316109711812278547/465875000000000000000000000000000 : ℝ)*base72 + (38480201840053/18635000000000000000000000000 : ℝ)*base74 + (1437627687738778547/465875000000000000000000000000000 : ℝ)*base76 + (2165386317585653547/465875000000000000000000000000000 : ℝ)*base78 + (3124180454976528547/465875000000000000000000000000000 : ℝ)*base80 + (20323124936937/4658750000000000000000000000 : ℝ)*base82 + (5196813/1250000000000000000000 : ℝ)*base89 + (5196813/1250000000000000000000 : ℝ)*base91 + (5196813/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1687_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66549/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57859/100000 : ℝ) else (40349/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90087/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1687_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1687_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66549/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57859/100000 : ℝ) else (40349/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90087/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1687_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5111/1024 : ℝ) ≤ p) (hpb : p ≤ (5119/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46845043/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3451/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9801/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66549/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(57859/100000 : ℝ) else (40349/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90087/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1687_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

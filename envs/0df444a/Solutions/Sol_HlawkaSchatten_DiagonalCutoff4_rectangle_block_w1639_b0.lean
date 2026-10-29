-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1639_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:41.296345+00:00
-- url     : https://prove2.me/submissions/e152b45b-e250-4dd0-90bc-22352588b857

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
theorem support_rectangle_w1639_s0_0 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-378039101/2500000000 : ℝ)*x 0 + (724886539/1250000000 : ℝ)*x 1 + (4913986089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378039101/2500000000 : ℝ)^4875 ≤ (9150554459077/100000000000000 : ℝ)^3851 := by
    have hnat : (378039101 : ℕ)^4875*100000000000000^3851 ≤ 9150554459077^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378039101 2500000000 9150554459077 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (724886539/1250000000 : ℝ)^4875 ≤ (50169096314923/100000000000000 : ℝ)^3851 := by
    have hnat : (724886539 : ℕ)^4875*100000000000000^3851 ≤ 50169096314923^3851*1250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724886539 1250000000 50169096314923 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4913986089/10000000000 : ℝ)^4875 ≤ (40680349208257/100000000000000 : ℝ)^3851 := by
    have hnat : (4913986089 : ℕ)^4875*100000000000000^3851 ≤ 40680349208257^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913986089 10000000000 40680349208257 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378039101/2500000000 : ℝ), (724886539/1250000000 : ℝ), (4913986089/10000000000 : ℝ)] ![(9150554459077/100000000000000 : ℝ), (50169096314923/100000000000000 : ℝ), (40680349208257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378039101/2500000000 : ℝ)|^4875 ≤ (9150554459077/100000000000000 : ℝ)^3851
        have hw : |(-378039101/2500000000 : ℝ)|=(378039101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(724886539/1250000000 : ℝ)|^4875 ≤ (50169096314923/100000000000000 : ℝ)^3851
        have hw : |(724886539/1250000000 : ℝ)|=(724886539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4913986089/10000000000 : ℝ)|^4875 ≤ (40680349208257/100000000000000 : ℝ)^3851
        have hw : |(4913986089/10000000000 : ℝ)|=(4913986089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_1 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5441922337/10000000000 : ℝ)*x 0 + (-499782161/2500000000 : ℝ)*x 1 + (4913987647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5441922337/10000000000 : ℝ)^4875 ≤ (46290042130607/100000000000000 : ℝ)^3851 := by
    have hnat : (5441922337 : ℕ)^4875*100000000000000^3851 ≤ 46290042130607^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441922337 10000000000 46290042130607 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499782161/2500000000 : ℝ)^4875 ≤ (13029592323349/100000000000000 : ℝ)^3851 := by
    have hnat : (499782161 : ℕ)^4875*100000000000000^3851 ≤ 13029592323349^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499782161 2500000000 13029592323349 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4913987647/10000000000 : ℝ)^4875 ≤ (79453838937/195312500000 : ℝ)^3851 := by
    have hnat : (4913987647 : ℕ)^4875*195312500000^3851 ≤ 79453838937^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913987647 10000000000 79453838937 195312500000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5441922337/10000000000 : ℝ), (-499782161/2500000000 : ℝ), (4913987647/10000000000 : ℝ)] ![(46290042130607/100000000000000 : ℝ), (13029592323349/100000000000000 : ℝ), (79453838937/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5441922337/10000000000 : ℝ)|^4875 ≤ (46290042130607/100000000000000 : ℝ)^3851
        have hw : |(5441922337/10000000000 : ℝ)|=(5441922337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499782161/2500000000 : ℝ)|^4875 ≤ (13029592323349/100000000000000 : ℝ)^3851
        have hw : |(-499782161/2500000000 : ℝ)|=(499782161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4913987647/10000000000 : ℝ)|^4875 ≤ (79453838937/195312500000 : ℝ)^3851
        have hw : |(4913987647/10000000000 : ℝ)|=(4913987647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_2 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5441924131/10000000000 : ℝ)*x 0 + (2456993063/5000000000 : ℝ)*x 1 + (-1999128233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5441924131/10000000000 : ℝ)^4875 ≤ (46290061448457/100000000000000 : ℝ)^3851 := by
    have hnat : (5441924131 : ℕ)^4875*100000000000000^3851 ≤ 46290061448457^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441924131 10000000000 46290061448457 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2456993063/5000000000 : ℝ)^4875 ≤ (40680349596009/100000000000000 : ℝ)^3851 := by
    have hnat : (2456993063 : ℕ)^4875*100000000000000^3851 ≤ 40680349596009^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2456993063 5000000000 40680349596009 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999128233/10000000000 : ℝ)^4875 ≤ (3257397233077/25000000000000 : ℝ)^3851 := by
    have hnat : (1999128233 : ℕ)^4875*25000000000000^3851 ≤ 3257397233077^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999128233 10000000000 3257397233077 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5441924131/10000000000 : ℝ), (2456993063/5000000000 : ℝ), (-1999128233/10000000000 : ℝ)] ![(46290061448457/100000000000000 : ℝ), (40680349596009/100000000000000 : ℝ), (3257397233077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5441924131/10000000000 : ℝ)|^4875 ≤ (46290061448457/100000000000000 : ℝ)^3851
        have hw : |(5441924131/10000000000 : ℝ)|=(5441924131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2456993063/5000000000 : ℝ)|^4875 ≤ (40680349596009/100000000000000 : ℝ)^3851
        have hw : |(2456993063/5000000000 : ℝ)|=(2456993063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999128233/10000000000 : ℝ)|^4875 ≤ (3257397233077/25000000000000 : ℝ)^3851
        have hw : |(-1999128233/10000000000 : ℝ)|=(1999128233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_3 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (409579571/1000000000 : ℝ)*x 0 + (61599783/200000000 : ℝ)*x 1 + (533827423/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409579571/1000000000 : ℝ)^4875 ≤ (32304060467811/100000000000000 : ℝ)^3851 := by
    have hnat : (409579571 : ℕ)^4875*100000000000000^3851 ≤ 32304060467811^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409579571 1000000000 32304060467811 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61599783/200000000 : ℝ)^4875 ≤ (87965406371/390625000000 : ℝ)^3851 := by
    have hnat : (61599783 : ℕ)^4875*390625000000^3851 ≤ 87965406371^3851*200000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61599783 200000000 87965406371 390625000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533827423/1000000000 : ℝ)^4875 ≤ (45176795480253/100000000000000 : ℝ)^3851 := by
    have hnat : (533827423 : ℕ)^4875*100000000000000^3851 ≤ 45176795480253^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533827423 1000000000 45176795480253 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(409579571/1000000000 : ℝ), (61599783/200000000 : ℝ), (533827423/1000000000 : ℝ)] ![(32304060467811/100000000000000 : ℝ), (87965406371/390625000000 : ℝ), (45176795480253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(409579571/1000000000 : ℝ)|^4875 ≤ (32304060467811/100000000000000 : ℝ)^3851
        have hw : |(409579571/1000000000 : ℝ)|=(409579571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61599783/200000000 : ℝ)|^4875 ≤ (87965406371/390625000000 : ℝ)^3851
        have hw : |(61599783/200000000 : ℝ)|=(61599783/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(533827423/1000000000 : ℝ)|^4875 ≤ (45176795480253/100000000000000 : ℝ)^3851
        have hw : |(533827423/1000000000 : ℝ)|=(533827423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_4 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-151458031/1000000000 : ℝ)*x 0 + (4936070843/10000000000 : ℝ)*x 1 + (2888119297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151458031/1000000000 : ℝ)^4875 ≤ (9169126519203/100000000000000 : ℝ)^3851 := by
    have hnat : (151458031 : ℕ)^4875*100000000000000^3851 ≤ 9169126519203^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151458031 1000000000 9169126519203 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4936070843/10000000000 : ℝ)^4875 ≤ (8182386108969/20000000000000 : ℝ)^3851 := by
    have hnat : (4936070843 : ℕ)^4875*20000000000000^3851 ≤ 8182386108969^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936070843 10000000000 8182386108969 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2888119297/5000000000 : ℝ)^4875 ≤ (3119933932839/6250000000000 : ℝ)^3851 := by
    have hnat : (2888119297 : ℕ)^4875*6250000000000^3851 ≤ 3119933932839^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888119297 5000000000 3119933932839 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-151458031/1000000000 : ℝ), (4936070843/10000000000 : ℝ), (2888119297/5000000000 : ℝ)] ![(9169126519203/100000000000000 : ℝ), (8182386108969/20000000000000 : ℝ), (3119933932839/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-151458031/1000000000 : ℝ)|^4875 ≤ (9169126519203/100000000000000 : ℝ)^3851
        have hw : |(-151458031/1000000000 : ℝ)|=(151458031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4936070843/10000000000 : ℝ)|^4875 ≤ (8182386108969/20000000000000 : ℝ)^3851
        have hw : |(4936070843/10000000000 : ℝ)|=(4936070843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2888119297/5000000000 : ℝ)|^4875 ≤ (3119933932839/6250000000000 : ℝ)^3851
        have hw : |(2888119297/5000000000 : ℝ)|=(2888119297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_5 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200317817/10000000000 : ℝ)*x 0 + (-568438339/5000000000 : ℝ)*x 1 + (1155247701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200317817/10000000000 : ℝ)^4875 ≤ (5462995435857/12500000000000 : ℝ)^3851 := by
    have hnat : (5200317817 : ℕ)^4875*12500000000000^3851 ≤ 5462995435857^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200317817 10000000000 5462995435857 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568438339/5000000000 : ℝ)^4875 ≤ (398568409029/6250000000000 : ℝ)^3851 := by
    have hnat : (568438339 : ℕ)^4875*6250000000000^3851 ≤ 398568409029^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568438339 5000000000 398568409029 6250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1155247701/2000000000 : ℝ)^4875 ≤ (9983788390351/20000000000000 : ℝ)^3851 := by
    have hnat : (1155247701 : ℕ)^4875*20000000000000^3851 ≤ 9983788390351^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155247701 2000000000 9983788390351 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200317817/10000000000 : ℝ), (-568438339/5000000000 : ℝ), (1155247701/2000000000 : ℝ)] ![(5462995435857/12500000000000 : ℝ), (398568409029/6250000000000 : ℝ), (9983788390351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200317817/10000000000 : ℝ)|^4875 ≤ (5462995435857/12500000000000 : ℝ)^3851
        have hw : |(5200317817/10000000000 : ℝ)|=(5200317817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-568438339/5000000000 : ℝ)|^4875 ≤ (398568409029/6250000000000 : ℝ)^3851
        have hw : |(-568438339/5000000000 : ℝ)|=(568438339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1155247701/2000000000 : ℝ)|^4875 ≤ (9983788390351/20000000000000 : ℝ)^3851
        have hw : |(1155247701/2000000000 : ℝ)|=(1155247701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_6 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200317917/10000000000 : ℝ)*x 0 + (1444059599/2500000000 : ℝ)*x 1 + (-142109587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200317917/10000000000 : ℝ)^4875 ≤ (8740792910147/20000000000000 : ℝ)^3851 := by
    have hnat : (5200317917 : ℕ)^4875*20000000000000^3851 ≤ 8740792910147^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200317917 10000000000 8740792910147 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1444059599/2500000000 : ℝ)^4875 ≤ (12479735189821/25000000000000 : ℝ)^3851 := by
    have hnat : (1444059599 : ℕ)^4875*25000000000000^3851 ≤ 12479735189821^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1444059599 2500000000 12479735189821 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142109587/1250000000 : ℝ)^4875 ≤ (6377094672279/100000000000000 : ℝ)^3851 := by
    have hnat : (142109587 : ℕ)^4875*100000000000000^3851 ≤ 6377094672279^3851*1250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142109587 1250000000 6377094672279 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200317917/10000000000 : ℝ), (1444059599/2500000000 : ℝ), (-142109587/1250000000 : ℝ)] ![(8740792910147/20000000000000 : ℝ), (12479735189821/25000000000000 : ℝ), (6377094672279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200317917/10000000000 : ℝ)|^4875 ≤ (8740792910147/20000000000000 : ℝ)^3851
        have hw : |(5200317917/10000000000 : ℝ)|=(5200317917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1444059599/2500000000 : ℝ)|^4875 ≤ (12479735189821/25000000000000 : ℝ)^3851
        have hw : |(1444059599/2500000000 : ℝ)|=(1444059599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142109587/1250000000 : ℝ)|^4875 ≤ (6377094672279/100000000000000 : ℝ)^3851
        have hw : |(-142109587/1250000000 : ℝ)|=(142109587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s0_7 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025495457/2500000000 : ℝ)*x 0 + (2640963813/5000000000 : ℝ)*x 1 + (3138296583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025495457/2500000000 : ℝ)^4875 ≤ (16182918625983/50000000000000 : ℝ)^3851 := by
    have hnat : (1025495457 : ℕ)^4875*50000000000000^3851 ≤ 16182918625983^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025495457 2500000000 16182918625983 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640963813/5000000000 : ℝ)^4875 ≤ (44573997324901/100000000000000 : ℝ)^3851 := by
    have hnat : (2640963813 : ℕ)^4875*100000000000000^3851 ≤ 44573997324901^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640963813 5000000000 44573997324901 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3138296583/10000000000 : ℝ)^4875 ≤ (23060165402551/100000000000000 : ℝ)^3851 := by
    have hnat : (3138296583 : ℕ)^4875*100000000000000^3851 ≤ 23060165402551^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3138296583 10000000000 23060165402551 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025495457/2500000000 : ℝ), (2640963813/5000000000 : ℝ), (3138296583/10000000000 : ℝ)] ![(16182918625983/50000000000000 : ℝ), (44573997324901/100000000000000 : ℝ), (23060165402551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025495457/2500000000 : ℝ)|^4875 ≤ (16182918625983/50000000000000 : ℝ)^3851
        have hw : |(1025495457/2500000000 : ℝ)|=(1025495457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640963813/5000000000 : ℝ)|^4875 ≤ (44573997324901/100000000000000 : ℝ)^3851
        have hw : |(2640963813/5000000000 : ℝ)|=(2640963813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3138296583/10000000000 : ℝ)|^4875 ≤ (23060165402551/100000000000000 : ℝ)^3851
        have hw : |(3138296583/10000000000 : ℝ)|=(3138296583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1639_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1157/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23593/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4871/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4871 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4871*1^1024 ≤ 0^1024*1^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4871/1024 : ℝ) ≤ (127957181624732341/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4871 ≤ (127957181624732341/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4871*10000000000000000000^1024 ≤ 127957181624732341^1024*5^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 127957181624732341 10000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (127957181624732341/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4871 := by
      have hnat : (1 : ℕ)^1024*1^4871 ≤ 1^4871*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10127957181624732341/10000000000000000000 : ℝ) ≤ (626672796836963/625000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (10127957181624732341/10000000000000000000 : ℝ)^1024 ≤ (626672796836963/625000000000000 : ℝ)^4871 := by
      have hnat : (10127957181624732341 : ℕ)^1024*625000000000000^4871 ≤ 626672796836963^4871*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10127957181624732341 10000000000000000000 626672796836963 625000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626672796836963/625000000000000 : ℝ)) (X := (10127957181624732341/10000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5127957181624732341/5000000000000000000 : ℝ) ≤ (314172796836963/312500000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (5127957181624732341/5000000000000000000 : ℝ)^1024 ≤ (314172796836963/312500000000000 : ℝ)^4871 := by
      have hnat : (5127957181624732341 : ℕ)^1024*312500000000000^4871 ≤ 314172796836963^4871*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5127957181624732341 5000000000000000000 314172796836963 312500000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314172796836963/312500000000000 : ℝ)) (X := (5127957181624732341/5000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1672796836963/250000000000000 : ℝ)*(0 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1672796836963/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(127957181624732341/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1672796836963/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4871/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1672796836963/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(626672796836963/625000000000000 : ℝ) by norm_num, show 1+(127957181624732341/10000000000000000000 : ℝ)+(0 : ℝ)=(10127957181624732341/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(127957181624732341/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1672796836963/250000000000000 : ℝ)*(2/5 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1672796836963/250000000000000 : ℝ)*(2/5 : ℝ)=(314172796836963/312500000000000 : ℝ) by norm_num, show 1+2*(127957181624732341/10000000000000000000 : ℝ)=(5127957181624732341/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1672796836963/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1672796836963/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1672796836963/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1672796836963/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1672796836963/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1672796836963/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-378039101/2500000000 : ℝ)*X 0 0+(724886539/1250000000 : ℝ)*X 0 1+(4913986089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5441922337/10000000000 : ℝ)*X 1 0+(-499782161/2500000000 : ℝ)*X 1 1+(4913987647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5441924131/10000000000 : ℝ)*X 2 0+(2456993063/5000000000 : ℝ)*X 2 1+(-1999128233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((409579571/1000000000 : ℝ)*X 0 0+(61599783/200000000 : ℝ)*X 0 1+(533827423/1000000000 : ℝ)*X 0 2+(409579571/1000000000 : ℝ)*X 1 0+(61599783/200000000 : ℝ)*X 1 1+(533827423/1000000000 : ℝ)*X 1 2+(409579571/1000000000 : ℝ)*X 2 0+(61599783/200000000 : ℝ)*X 2 1+(533827423/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-151458031/1000000000 : ℝ)*X 0 0+(4936070843/10000000000 : ℝ)*X 0 1+(2888119297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5200317817/10000000000 : ℝ)*X 1 0+(-568438339/5000000000 : ℝ)*X 1 1+(1155247701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5200317917/10000000000 : ℝ)*X 2 0+(1444059599/2500000000 : ℝ)*X 2 1+(-142109587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1025495457/2500000000 : ℝ)*X 0 0+(2640963813/5000000000 : ℝ)*X 0 1+(3138296583/10000000000 : ℝ)*X 0 2+(1025495457/2500000000 : ℝ)*X 1 0+(2640963813/5000000000 : ℝ)*X 1 1+(3138296583/10000000000 : ℝ)*X 1 2+(1025495457/2500000000 : ℝ)*X 2 0+(2640963813/5000000000 : ℝ)*X 2 1+(3138296583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12372777140123993205369/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60432361/50000000000000 : ℝ)*(base19) + (70035527/20000000000000 : ℝ)*(base23) + (3278429/12500000000000 : ℝ)*(base24) + (63625127/100000000000000 : ℝ)*(upper4) + (23866699/50000000000000 : ℝ)*(upper5) + (786313436340929/100000000000000 : ℝ)*(major0) + (786313436340929/100000000000000 : ℝ)*(major1) + (786313436340929/100000000000000 : ℝ)*(major2) + (1129809202309093/100000000000000 : ℝ)*(sp0) + (282452958954771/25000000000000 : ℝ)*(sp1) + (56490579013937/5000000000000 : ℝ)*(sp2) + (442814303751861/100000000000000 : ℝ)*(sp3) + (2754374713/100000000000000 : ℝ)*(sp4) + (546258043/100000000000000 : ℝ)*(sp7) + (27675928125619/6250000000000 : ℝ)*(f.failure) + (564905978341903/50000000000000 : ℝ)*(f.sum) + (33388256941373/12500000000000000000000000000 : ℝ)*base66 + (117825443383627/25000000000000000000000000000 : ℝ)*base67 + (90225449508627/25000000000000000000000000000 : ℝ)*base69 + (8803258591373/25000000000000000000000000000 : ℝ)*base72 + (8381922308627/12500000000000000000000000000 : ℝ)*base73 + (48866085783627/25000000000000000000000000000 : ℝ)*base75 + (16151850608627/25000000000000000000000000000 : ℝ)*base77 + (86498935741373/25000000000000000000000000000 : ℝ)*base80 + (31658413471127/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (239699/125000000000000000000 : ℝ)*base89 + (239699/125000000000000000000 : ℝ)*base91 + (239699/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6556240752193724019243/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (391384443/50000000000000 : ℝ)*(base19) + (812668477/100000000000000 : ℝ)*(base23) + (55247639/100000000000000 : ℝ)*(base32) + (123102977/100000000000000 : ℝ)*(upper3) + (406249/500000000000 : ℝ)*(upper5) + (207092052934531/25000000000000 : ℝ)*(major0) + (207092052934531/25000000000000 : ℝ)*(major1) + (207092052934531/25000000000000 : ℝ)*(major2) + (1141934561/50000000000000 : ℝ)*(sp1) + (2434774887/100000000000000 : ℝ)*(sp2) + (297559539106083/25000000000000 : ℝ)*(sp4) + (297558772446581/25000000000000 : ℝ)*(sp5) + (148779363622621/12500000000000 : ℝ)*(sp6) + (2332490359689/500000000000 : ℝ)*(sp7) + (233249063592719/50000000000000 : ℝ)*(f.failure) + (297559539106083/25000000000000 : ℝ)*(f.sum) + (2050441005647/3125000000000000000000000000 : ℝ)*base66 + (76722421855647/6250000000000000000000000000 : ℝ)*base68 + (14053621430647/6250000000000000000000000000 : ℝ)*base70 + (52148650268147/6250000000000000000000000000 : ℝ)*base72 + (12622894380647/3125000000000000000000000000 : ℝ)*base74 + (40584073593147/6250000000000000000000000000 : ℝ)*base76 + (39673581711897/6250000000000000000000000000 : ℝ)*base78 + (70004379443147/6250000000000000000000000000 : ℝ)*base80 + (2919783872807/781250000000000000000000000 : ℝ)*base81 + (4171201/1000000000000000000000 : ℝ)*base90 + (4171201/1000000000000000000000 : ℝ)*base92 + (4171201/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1639_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1157/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23593/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1639_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1639_s1_0 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12676979/78125000 : ℝ)*x 0 + (5504783379/10000000000 : ℝ)*x 1 + (5136576809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12676979/78125000 : ℝ)^4875 ≤ (1250635812933/12500000000000 : ℝ)^3851 := by
    have hnat : (12676979 : ℕ)^4875*12500000000000^3851 ≤ 1250635812933^3851*78125000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12676979 78125000 1250635812933 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504783379/10000000000 : ℝ)^4875 ≤ (23483984232511/50000000000000 : ℝ)^3851 := by
    have hnat : (5504783379 : ℕ)^4875*50000000000000^3851 ≤ 23483984232511^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504783379 10000000000 23483984232511 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136576809/10000000000 : ℝ)^4875 ≤ (43026945014561/100000000000000 : ℝ)^3851 := by
    have hnat : (5136576809 : ℕ)^4875*100000000000000^3851 ≤ 43026945014561^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136576809 10000000000 43026945014561 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12676979/78125000 : ℝ), (5504783379/10000000000 : ℝ), (5136576809/10000000000 : ℝ)] ![(1250635812933/12500000000000 : ℝ), (23483984232511/50000000000000 : ℝ), (43026945014561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12676979/78125000 : ℝ)|^4875 ≤ (1250635812933/12500000000000 : ℝ)^3851
        have hw : |(-12676979/78125000 : ℝ)|=(12676979/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504783379/10000000000 : ℝ)|^4875 ≤ (23483984232511/50000000000000 : ℝ)^3851
        have hw : |(5504783379/10000000000 : ℝ)|=(5504783379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136576809/10000000000 : ℝ)|^4875 ≤ (43026945014561/100000000000000 : ℝ)^3851
        have hw : |(5136576809/10000000000 : ℝ)|=(5136576809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_1 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363642883/10000000000 : ℝ)*x 0 + (-1814362273/10000000000 : ℝ)*x 1 + (5136576601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363642883/10000000000 : ℝ)^4875 ≤ (22724372107403/50000000000000 : ℝ)^3851 := by
    have hnat : (5363642883 : ℕ)^4875*50000000000000^3851 ≤ 22724372107403^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363642883 10000000000 22724372107403 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814362273/10000000000 : ℝ)^4875 ≤ (2304862591817/20000000000000 : ℝ)^3851 := by
    have hnat : (1814362273 : ℕ)^4875*20000000000000^3851 ≤ 2304862591817^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814362273 10000000000 2304862591817 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136576601/10000000000 : ℝ)^4875 ≤ (21513471404469/50000000000000 : ℝ)^3851 := by
    have hnat : (5136576601 : ℕ)^4875*50000000000000^3851 ≤ 21513471404469^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136576601 10000000000 21513471404469 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363642883/10000000000 : ℝ), (-1814362273/10000000000 : ℝ), (5136576601/10000000000 : ℝ)] ![(22724372107403/50000000000000 : ℝ), (2304862591817/20000000000000 : ℝ), (21513471404469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363642883/10000000000 : ℝ)|^4875 ≤ (22724372107403/50000000000000 : ℝ)^3851
        have hw : |(5363642883/10000000000 : ℝ)|=(5363642883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1814362273/10000000000 : ℝ)|^4875 ≤ (2304862591817/20000000000000 : ℝ)^3851
        have hw : |(-1814362273/10000000000 : ℝ)|=(1814362273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136576601/10000000000 : ℝ)|^4875 ≤ (21513471404469/50000000000000 : ℝ)^3851
        have hw : |(5136576601/10000000000 : ℝ)|=(5136576601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_2 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670455493/1250000000 : ℝ)*x 0 + (5136575357/10000000000 : ℝ)*x 1 + (-907181249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670455493/1250000000 : ℝ)^4875 ≤ (11362188898939/25000000000000 : ℝ)^3851 := by
    have hnat : (670455493 : ℕ)^4875*25000000000000^3851 ≤ 11362188898939^3851*1250000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670455493 1250000000 11362188898939 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136575357/10000000000 : ℝ)^4875 ≤ (2151346480881/5000000000000 : ℝ)^3851 := by
    have hnat : (5136575357 : ℕ)^4875*5000000000000^3851 ≤ 2151346480881^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136575357 10000000000 2151346480881 5000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907181249/5000000000 : ℝ)^4875 ≤ (2881078692059/25000000000000 : ℝ)^3851 := by
    have hnat : (907181249 : ℕ)^4875*25000000000000^3851 ≤ 2881078692059^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907181249 5000000000 2881078692059 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670455493/1250000000 : ℝ), (5136575357/10000000000 : ℝ), (-907181249/5000000000 : ℝ)] ![(11362188898939/25000000000000 : ℝ), (2151346480881/5000000000000 : ℝ), (2881078692059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670455493/1250000000 : ℝ)|^4875 ≤ (11362188898939/25000000000000 : ℝ)^3851
        have hw : |(670455493/1250000000 : ℝ)|=(670455493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136575357/10000000000 : ℝ)|^4875 ≤ (2151346480881/5000000000000 : ℝ)^3851
        have hw : |(5136575357/10000000000 : ℝ)|=(5136575357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-907181249/5000000000 : ℝ)|^4875 ≤ (2881078692059/25000000000000 : ℝ)^3851
        have hw : |(-907181249/5000000000 : ℝ)|=(907181249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_3 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167237727/400000000 : ℝ)*x 0 + (3730616831/10000000000 : ℝ)*x 1 + (2335036409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167237727/400000000 : ℝ)^4875 ≤ (16578270360891/50000000000000 : ℝ)^3851 := by
    have hnat : (167237727 : ℕ)^4875*50000000000000^3851 ≤ 16578270360891^3851*400000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167237727 400000000 16578270360891 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3730616831/10000000000 : ℝ)^4875 ≤ (14351093676639/50000000000000 : ℝ)^3851 := by
    have hnat : (3730616831 : ℕ)^4875*50000000000000^3851 ≤ 14351093676639^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3730616831 10000000000 14351093676639 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2335036409/5000000000 : ℝ)^4875 ≤ (7628254380491/20000000000000 : ℝ)^3851 := by
    have hnat : (2335036409 : ℕ)^4875*20000000000000^3851 ≤ 7628254380491^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335036409 5000000000 7628254380491 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167237727/400000000 : ℝ), (3730616831/10000000000 : ℝ), (2335036409/5000000000 : ℝ)] ![(16578270360891/50000000000000 : ℝ), (14351093676639/50000000000000 : ℝ), (7628254380491/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167237727/400000000 : ℝ)|^4875 ≤ (16578270360891/50000000000000 : ℝ)^3851
        have hw : |(167237727/400000000 : ℝ)|=(167237727/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3730616831/10000000000 : ℝ)|^4875 ≤ (14351093676639/50000000000000 : ℝ)^3851
        have hw : |(3730616831/10000000000 : ℝ)|=(3730616831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2335036409/5000000000 : ℝ)|^4875 ≤ (7628254380491/20000000000000 : ℝ)^3851
        have hw : |(2335036409/5000000000 : ℝ)|=(2335036409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_4 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-811412691/5000000000 : ℝ)*x 0 + (2570189897/5000000000 : ℝ)*x 1 + (1100184937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811412691/5000000000 : ℝ)^4875 ≤ (10006429600807/100000000000000 : ℝ)^3851 := by
    have hnat : (811412691 : ℕ)^4875*100000000000000^3851 ≤ 10006429600807^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811412691 5000000000 10006429600807 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570189897/5000000000 : ℝ)^4875 ≤ (43067275660563/100000000000000 : ℝ)^3851 := by
    have hnat : (2570189897 : ℕ)^4875*100000000000000^3851 ≤ 43067275660563^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570189897 5000000000 43067275660563 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100184937/2000000000 : ℝ)^4875 ≤ (9385258944577/20000000000000 : ℝ)^3851 := by
    have hnat : (1100184937 : ℕ)^4875*20000000000000^3851 ≤ 9385258944577^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100184937 2000000000 9385258944577 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-811412691/5000000000 : ℝ), (2570189897/5000000000 : ℝ), (1100184937/2000000000 : ℝ)] ![(10006429600807/100000000000000 : ℝ), (43067275660563/100000000000000 : ℝ), (9385258944577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-811412691/5000000000 : ℝ)|^4875 ≤ (10006429600807/100000000000000 : ℝ)^3851
        have hw : |(-811412691/5000000000 : ℝ)|=(811412691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570189897/5000000000 : ℝ)|^4875 ≤ (43067275660563/100000000000000 : ℝ)^3851
        have hw : |(2570189897/5000000000 : ℝ)|=(2570189897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100184937/2000000000 : ℝ)|^4875 ≤ (9385258944577/20000000000000 : ℝ)^3851
        have hw : |(1100184937/2000000000 : ℝ)|=(1100184937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_5 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632655661/5000000000 : ℝ)*x 0 + (-725006901/5000000000 : ℝ)*x 1 + (5500924679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632655661/5000000000 : ℝ)^4875 ≤ (11099140218273/25000000000000 : ℝ)^3851 := by
    have hnat : (2632655661 : ℕ)^4875*25000000000000^3851 ≤ 11099140218273^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632655661 5000000000 11099140218273 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (725006901/5000000000 : ℝ)^4875 ≤ (1694754777/19531250000 : ℝ)^3851 := by
    have hnat : (725006901 : ℕ)^4875*19531250000^3851 ≤ 1694754777^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725006901 5000000000 1694754777 19531250000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500924679/10000000000 : ℝ)^4875 ≤ (46926294658091/100000000000000 : ℝ)^3851 := by
    have hnat : (5500924679 : ℕ)^4875*100000000000000^3851 ≤ 46926294658091^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500924679 10000000000 46926294658091 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632655661/5000000000 : ℝ), (-725006901/5000000000 : ℝ), (5500924679/10000000000 : ℝ)] ![(11099140218273/25000000000000 : ℝ), (1694754777/19531250000 : ℝ), (46926294658091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632655661/5000000000 : ℝ)|^4875 ≤ (11099140218273/25000000000000 : ℝ)^3851
        have hw : |(2632655661/5000000000 : ℝ)|=(2632655661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-725006901/5000000000 : ℝ)|^4875 ≤ (1694754777/19531250000 : ℝ)^3851
        have hw : |(-725006901/5000000000 : ℝ)|=(725006901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500924679/10000000000 : ℝ)|^4875 ≤ (46926294658091/100000000000000 : ℝ)^3851
        have hw : |(5500924679/10000000000 : ℝ)|=(5500924679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_6 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632655597/5000000000 : ℝ)*x 0 + (44007399/80000000 : ℝ)*x 1 + (-725006851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632655597/5000000000 : ℝ)^4875 ≤ (44396559506823/100000000000000 : ℝ)^3851 := by
    have hnat : (2632655597 : ℕ)^4875*100000000000000^3851 ≤ 44396559506823^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632655597 5000000000 44396559506823 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44007399/80000000 : ℝ)^4875 ≤ (23463148387343/50000000000000 : ℝ)^3851 := by
    have hnat : (44007399 : ℕ)^4875*50000000000000^3851 ≤ 23463148387343^3851*80000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44007399 80000000 23463148387343 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (725006851/5000000000 : ℝ)^4875 ≤ (86771437007/1000000000000 : ℝ)^3851 := by
    have hnat : (725006851 : ℕ)^4875*1000000000000^3851 ≤ 86771437007^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725006851 5000000000 86771437007 1000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632655597/5000000000 : ℝ), (44007399/80000000 : ℝ), (-725006851/5000000000 : ℝ)] ![(44396559506823/100000000000000 : ℝ), (23463148387343/50000000000000 : ℝ), (86771437007/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632655597/5000000000 : ℝ)|^4875 ≤ (44396559506823/100000000000000 : ℝ)^3851
        have hw : |(2632655597/5000000000 : ℝ)|=(2632655597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44007399/80000000 : ℝ)|^4875 ≤ (23463148387343/50000000000000 : ℝ)^3851
        have hw : |(44007399/80000000 : ℝ)|=(44007399/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-725006851/5000000000 : ℝ)|^4875 ≤ (86771437007/1000000000000 : ℝ)^3851
        have hw : |(-725006851/5000000000 : ℝ)|=(725006851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s1_7 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418137903/1000000000 : ℝ)*x 0 + (932073699/2000000000 : ℝ)*x 1 + (3740462807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418137903/1000000000 : ℝ)^4875 ≤ (663218327743/2000000000000 : ℝ)^3851 := by
    have hnat : (418137903 : ℕ)^4875*2000000000000^3851 ≤ 663218327743^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418137903 1000000000 663218327743 2000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932073699/2000000000 : ℝ)^4875 ≤ (4755121000803/12500000000000 : ℝ)^3851 := by
    have hnat : (932073699 : ℕ)^4875*12500000000000^3851 ≤ 4755121000803^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932073699 2000000000 4755121000803 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3740462807/10000000000 : ℝ)^4875 ≤ (2879811559621/10000000000000 : ℝ)^3851 := by
    have hnat : (3740462807 : ℕ)^4875*10000000000000^3851 ≤ 2879811559621^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740462807 10000000000 2879811559621 10000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418137903/1000000000 : ℝ), (932073699/2000000000 : ℝ), (3740462807/10000000000 : ℝ)] ![(663218327743/2000000000000 : ℝ), (4755121000803/12500000000000 : ℝ), (2879811559621/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418137903/1000000000 : ℝ)|^4875 ≤ (663218327743/2000000000000 : ℝ)^3851
        have hw : |(418137903/1000000000 : ℝ)|=(418137903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932073699/2000000000 : ℝ)|^4875 ≤ (4755121000803/12500000000000 : ℝ)^3851
        have hw : |(932073699/2000000000 : ℝ)|=(932073699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3740462807/10000000000 : ℝ)|^4875 ≤ (2879811559621/10000000000000 : ℝ)^3851
        have hw : |(3740462807/10000000000 : ℝ)|=(3740462807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1639_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1157/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4801/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17419/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1157/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23593/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1157/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1157/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23593/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1157/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1157/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23593/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1157/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1157/25000 : ℝ) ^ (4871/1024 : ℝ) ≤ (8964480396599/20000000000000000000 : ℝ) := by
    have hpowers : (1157/25000 : ℝ)^4871 ≤ (8964480396599/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1157 : ℕ)^4871*20000000000000000000^1024 ≤ 8964480396599^1024*25000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1157 25000 8964480396599 20000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1157/25000 : ℝ)) (X := (8964480396599/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23593/100000 : ℝ) ^ (4871/1024 : ℝ) ≤ (20771240162407041/20000000000000000000 : ℝ) := by
    have hpowers : (23593/100000 : ℝ)^4871 ≤ (20771240162407041/20000000000000000000 : ℝ)^1024 := by
      have hnat : (23593 : ℕ)^4871*20000000000000000000^1024 ≤ 20771240162407041^1024*100000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23593 100000 20771240162407041 20000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23593/100000 : ℝ)) (X := (20771240162407041/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000008964480396599/10000000000000000000 : ℝ) ≤ (2500000471136557/2500000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (10000008964480396599/10000000000000000000 : ℝ)^1024 ≤ (2500000471136557/2500000000000000 : ℝ)^4871 := by
      have hnat : (10000008964480396599 : ℕ)^1024*2500000000000000^4871 ≤ 2500000471136557^4871*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000008964480396599 10000000000000000000 2500000471136557 2500000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000471136557/2500000000000000 : ℝ)) (X := (10000008964480396599/10000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500519505116070091/500000000000000000 : ℝ) ≤ (2500545837722509/2500000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (500519505116070091/500000000000000000 : ℝ)^1024 ≤ (2500545837722509/2500000000000000 : ℝ)^4871 := by
      have hnat : (500519505116070091 : ℕ)^1024*2500000000000000^4871 ≤ 2500545837722509^4871*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500519505116070091 500000000000000000 2500545837722509 2500000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500545837722509/2500000000000000 : ℝ)) (X := (500519505116070091/500000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10020771240162407041/10000000000000000000 : ℝ) ≤ (2501091204308461/2500000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (10020771240162407041/10000000000000000000 : ℝ)^1024 ≤ (2501091204308461/2500000000000000 : ℝ)^4871 := by
      have hnat : (10020771240162407041 : ℕ)^1024*2500000000000000^4871 ≤ 2501091204308461^4871*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10020771240162407041 10000000000000000000 2501091204308461 2500000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501091204308461/2500000000000000 : ℝ)) (X := (10020771240162407041/10000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8964480396599/20000000000000000000 : ℝ) ≤ ((47407461021985231793/47412500000000000000 : ℝ)+2*(17042705811/14816406250000 : ℝ)*(1157/25000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (47407461021985231793/47412500000000000000 : ℝ)+2*(17042705811/14816406250000 : ℝ)*(1157/25000 : ℝ)=(2500000471136557/2500000000000000 : ℝ) by norm_num, show 1+2*(8964480396599/20000000000000000000 : ℝ)=(10000008964480396599/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20771240162407041/20000000000000000000 : ℝ)+(8964480396599/20000000000000000000 : ℝ) ≤ ((47407461021985231793/47412500000000000000 : ℝ)+(17042705811/14816406250000 : ℝ)*((23593/100000 : ℝ)+(1157/25000 : ℝ)))^(4871/1024 : ℝ) := by
    rw [show (47407461021985231793/47412500000000000000 : ℝ)+(17042705811/14816406250000 : ℝ)*((23593/100000 : ℝ)+(1157/25000 : ℝ))=(2500545837722509/2500000000000000 : ℝ) by norm_num, show 1+(20771240162407041/20000000000000000000 : ℝ)+(8964480396599/20000000000000000000 : ℝ)=(500519505116070091/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20771240162407041/20000000000000000000 : ℝ) ≤ ((47407461021985231793/47412500000000000000 : ℝ)+2*(17042705811/14816406250000 : ℝ)*(23593/100000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (47407461021985231793/47412500000000000000 : ℝ)+2*(17042705811/14816406250000 : ℝ)*(23593/100000 : ℝ)=(2501091204308461/2500000000000000 : ℝ) by norm_num, show 1+2*(20771240162407041/20000000000000000000 : ℝ)=(10020771240162407041/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (47407461021985231793/47412500000000000000 : ℝ)*(X 1 0+X 2 0)+(17042705811/14816406250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (1157/25000 : ℝ)) (hi := (23593/100000 : ℝ)) (c := (47407461021985231793/47412500000000000000 : ℝ)) (alpha := (17042705811/14816406250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (47407461021985231793/47412500000000000000 : ℝ)*(X 0 1+X 2 1)+(17042705811/14816406250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (1157/25000 : ℝ)) (hi := (23593/100000 : ℝ)) (c := (47407461021985231793/47412500000000000000 : ℝ)) (alpha := (17042705811/14816406250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (47407461021985231793/47412500000000000000 : ℝ)*(X 0 2+X 1 2)+(17042705811/14816406250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (1157/25000 : ℝ)) (hi := (23593/100000 : ℝ)) (c := (47407461021985231793/47412500000000000000 : ℝ)) (alpha := (17042705811/14816406250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-12676979/78125000 : ℝ)*X 0 0+(5504783379/10000000000 : ℝ)*X 0 1+(5136576809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363642883/10000000000 : ℝ)*X 1 0+(-1814362273/10000000000 : ℝ)*X 1 1+(5136576601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((670455493/1250000000 : ℝ)*X 2 0+(5136575357/10000000000 : ℝ)*X 2 1+(-907181249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((167237727/400000000 : ℝ)*X 0 0+(3730616831/10000000000 : ℝ)*X 0 1+(2335036409/5000000000 : ℝ)*X 0 2+(167237727/400000000 : ℝ)*X 1 0+(3730616831/10000000000 : ℝ)*X 1 1+(2335036409/5000000000 : ℝ)*X 1 2+(167237727/400000000 : ℝ)*X 2 0+(3730616831/10000000000 : ℝ)*X 2 1+(2335036409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-811412691/5000000000 : ℝ)*X 0 0+(2570189897/5000000000 : ℝ)*X 0 1+(1100184937/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632655661/5000000000 : ℝ)*X 1 0+(-725006901/5000000000 : ℝ)*X 1 1+(5500924679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2632655597/5000000000 : ℝ)*X 2 0+(44007399/80000000 : ℝ)*X 2 1+(-725006851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((418137903/1000000000 : ℝ)*X 0 0+(932073699/2000000000 : ℝ)*X 0 1+(3740462807/10000000000 : ℝ)*X 0 2+(418137903/1000000000 : ℝ)*X 1 0+(932073699/2000000000 : ℝ)*X 1 1+(3740462807/10000000000 : ℝ)*X 1 2+(418137903/1000000000 : ℝ)*X 2 0+(932073699/2000000000 : ℝ)*X 2 1+(3740462807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20764217001925682453689703787/2370625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (587457091/100000000000000 : ℝ)*(base1) + (497789867/50000000000000 : ℝ)*(base19) + (9580087/625000000000 : ℝ)*(base23) + (115938521/100000000000000 : ℝ)*(upper3) + (63316337/100000000000000 : ℝ)*(upper5) + (1890157122813451/100000000000000 : ℝ)*(major0) + (1890157122813451/100000000000000 : ℝ)*(major1) + (1890157122813451/100000000000000 : ℝ)*(major2) + (678966605321913/25000000000000 : ℝ)*(sp0) + (678966278262119/25000000000000 : ℝ)*(sp1) + (271586457581429/10000000000000 : ℝ)*(sp2) + (21288921069437/2000000000000 : ℝ)*(sp3) + (274797649/100000000000000 : ℝ)*(sp4) + (240820861/20000000000000 : ℝ)*(sp7) + (33263995157289/3125000000000 : ℝ)*(f.failure) + (271586610862821/10000000000000 : ℝ)*(f.sum) + (11657283487971/47412500000000000000000000000 : ℝ)*base66 + (19926339208715302357/4741250000000000000000000000000000 : ℝ)*base68 + (11839505462586552357/4741250000000000000000000000000000 : ℝ)*base70 + (21453616588611552357/4741250000000000000000000000000000 : ℝ)*base72 + (98967357187617/94825000000000000000000000000 : ℝ)*base74 + (29168689073960302357/4741250000000000000000000000000000 : ℝ)*base76 + (5787405055406552357/4741250000000000000000000000000000 : ℝ)*base78 + (64288371662450302357/4741250000000000000000000000000000 : ℝ)*base80 + (268678375285967/94825000000000000000000000000 : ℝ)*base82 + (160769/62500000000000000000 : ℝ)*base89 + (160769/62500000000000000000 : ℝ)*base91 + (160769/62500000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (901278370489310190685184733/296328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (660557653/100000000000000 : ℝ)*(base19) + (83050691/12500000000000 : ℝ)*(base23) + (7097309/25000000000000 : ℝ)*(upper2) + (37407523/50000000000000 : ℝ)*(upper3) + (87865621/100000000000000 : ℝ)*(upper5) + (241290458169951/12500000000000 : ℝ)*(major0) + (241290458169951/12500000000000 : ℝ)*(major1) + (241290458169951/12500000000000 : ℝ)*(major2) + (6057687233/100000000000000 : ℝ)*(sp1) + (3493484269/50000000000000 : ℝ)*(sp2) + (1386789735656459/50000000000000 : ℝ)*(sp4) + (677141785417/24414062500 : ℝ)*(sp5) + (693392954984713/25000000000000 : ℝ)*(sp6) + (543533879011683/50000000000000 : ℝ)*(sp7) + (543533879011683/50000000000000 : ℝ)*(f.failure) + (1386789735656459/50000000000000 : ℝ)*(f.sum) + (1319324640149/1481640625000000000000000000 : ℝ)*base66 + (60822163243285357/592656250000000000000000000000000 : ℝ)*base68 + (2742115275913597857/592656250000000000000000000000000 : ℝ)*base70 + (832516480339058393/592656250000000000000000000000000 : ℝ)*base71 + (456180879174239/94825000000000000000000000000 : ℝ)*base73 + (1209160061270316607/592656250000000000000000000000000 : ℝ)*base76 + (202896729001722857/592656250000000000000000000000000 : ℝ)*base78 + (4821323223006097857/592656250000000000000000000000000 : ℝ)*base80 + (111306936657143/47412500000000000000000000000 : ℝ)*base82 + (7187757/1000000000000000000000 : ℝ)*base90 + (7187757/1000000000000000000000 : ℝ)*base92 + (7187757/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1639_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23593/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1157/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4801/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17419/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1639_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1639_s2_0 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-81652771/500000000 : ℝ)*x 0 + (1091020533/2000000000 : ℝ)*x 1 + (5179408951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81652771/500000000 : ℝ)^4875 ≤ (10086348404863/100000000000000 : ℝ)^3851 := by
    have hnat : (81652771 : ℕ)^4875*100000000000000^3851 ≤ 10086348404863^3851*500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81652771 500000000 10086348404863 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091020533/2000000000 : ℝ)^4875 ≤ (46432013999109/100000000000000 : ℝ)^3851 := by
    have hnat : (1091020533 : ℕ)^4875*100000000000000^3851 ≤ 46432013999109^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091020533 2000000000 46432013999109 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179408951/10000000000 : ℝ)^4875 ≤ (43481637580577/100000000000000 : ℝ)^3851 := by
    have hnat : (5179408951 : ℕ)^4875*100000000000000^3851 ≤ 43481637580577^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179408951 10000000000 43481637580577 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81652771/500000000 : ℝ), (1091020533/2000000000 : ℝ), (5179408951/10000000000 : ℝ)] ![(10086348404863/100000000000000 : ℝ), (46432013999109/100000000000000 : ℝ), (43481637580577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81652771/500000000 : ℝ)|^4875 ≤ (10086348404863/100000000000000 : ℝ)^3851
        have hw : |(-81652771/500000000 : ℝ)|=(81652771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091020533/2000000000 : ℝ)|^4875 ≤ (46432013999109/100000000000000 : ℝ)^3851
        have hw : |(1091020533/2000000000 : ℝ)|=(1091020533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179408951/10000000000 : ℝ)|^4875 ≤ (43481637580577/100000000000000 : ℝ)^3851
        have hw : |(5179408951/10000000000 : ℝ)|=(5179408951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_1 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350543659/10000000000 : ℝ)*x 0 + (-443792011/2500000000 : ℝ)*x 1 + (5179409693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350543659/10000000000 : ℝ)^4875 ≤ (4530827939029/10000000000000 : ℝ)^3851 := by
    have hnat : (5350543659 : ℕ)^4875*10000000000000^3851 ≤ 4530827939029^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350543659 10000000000 4530827939029 10000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443792011/2500000000 : ℝ)^4875 ≤ (2242015025179/20000000000000 : ℝ)^3851 := by
    have hnat : (443792011 : ℕ)^4875*20000000000000^3851 ≤ 2242015025179^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443792011 2500000000 2242015025179 20000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179409693/10000000000 : ℝ)^4875 ≤ (5435205683263/12500000000000 : ℝ)^3851 := by
    have hnat : (5179409693 : ℕ)^4875*12500000000000^3851 ≤ 5435205683263^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179409693 10000000000 5435205683263 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350543659/10000000000 : ℝ), (-443792011/2500000000 : ℝ), (5179409693/10000000000 : ℝ)] ![(4530827939029/10000000000000 : ℝ), (2242015025179/20000000000000 : ℝ), (5435205683263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350543659/10000000000 : ℝ)|^4875 ≤ (4530827939029/10000000000000 : ℝ)^3851
        have hw : |(5350543659/10000000000 : ℝ)|=(5350543659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-443792011/2500000000 : ℝ)|^4875 ≤ (2242015025179/20000000000000 : ℝ)^3851
        have hw : |(-443792011/2500000000 : ℝ)|=(443792011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179409693/10000000000 : ℝ)|^4875 ≤ (5435205683263/12500000000000 : ℝ)^3851
        have hw : |(5179409693/10000000000 : ℝ)|=(5179409693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_2 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350546101/10000000000 : ℝ)*x 0 + (5179408373/10000000000 : ℝ)*x 1 + (-71006661/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350546101/10000000000 : ℝ)^4875 ≤ (22654152783843/50000000000000 : ℝ)^3851 := by
    have hnat : (5350546101 : ℕ)^4875*50000000000000^3851 ≤ 22654152783843^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350546101 10000000000 22654152783843 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179408373/10000000000 : ℝ)^4875 ≤ (43481631437943/100000000000000 : ℝ)^3851 := by
    have hnat : (5179408373 : ℕ)^4875*100000000000000^3851 ≤ 43481631437943^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179408373 10000000000 43481631437943 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71006661/400000000 : ℝ)^4875 ≤ (5605031491421/50000000000000 : ℝ)^3851 := by
    have hnat : (71006661 : ℕ)^4875*50000000000000^3851 ≤ 5605031491421^3851*400000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71006661 400000000 5605031491421 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350546101/10000000000 : ℝ), (5179408373/10000000000 : ℝ), (-71006661/400000000 : ℝ)] ![(22654152783843/50000000000000 : ℝ), (43481631437943/100000000000000 : ℝ), (5605031491421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350546101/10000000000 : ℝ)|^4875 ≤ (22654152783843/50000000000000 : ℝ)^3851
        have hw : |(5350546101/10000000000 : ℝ)|=(5350546101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179408373/10000000000 : ℝ)|^4875 ≤ (43481631437943/100000000000000 : ℝ)^3851
        have hw : |(5179408373/10000000000 : ℝ)|=(5179408373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71006661/400000000 : ℝ)|^4875 ≤ (5605031491421/50000000000000 : ℝ)^3851
        have hw : |(-71006661/400000000 : ℝ)|=(71006661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_3 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (418867553/1000000000 : ℝ)*x 0 + (3847849621/10000000000 : ℝ)*x 1 + (4551264181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418867553/1000000000 : ℝ)^4875 ≤ (16617092956187/50000000000000 : ℝ)^3851 := by
    have hnat : (418867553 : ℕ)^4875*50000000000000^3851 ≤ 16617092956187^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418867553 1000000000 16617092956187 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3847849621/10000000000 : ℝ)^4875 ≤ (373108838489/1250000000000 : ℝ)^3851 := by
    have hnat : (3847849621 : ℕ)^4875*1250000000000^3851 ≤ 373108838489^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3847849621 10000000000 373108838489 1250000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4551264181/10000000000 : ℝ)^4875 ≤ (18458553502109/50000000000000 : ℝ)^3851 := by
    have hnat : (4551264181 : ℕ)^4875*50000000000000^3851 ≤ 18458553502109^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551264181 10000000000 18458553502109 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(418867553/1000000000 : ℝ), (3847849621/10000000000 : ℝ), (4551264181/10000000000 : ℝ)] ![(16617092956187/50000000000000 : ℝ), (373108838489/1250000000000 : ℝ), (18458553502109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(418867553/1000000000 : ℝ)|^4875 ≤ (16617092956187/50000000000000 : ℝ)^3851
        have hw : |(418867553/1000000000 : ℝ)|=(418867553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3847849621/10000000000 : ℝ)|^4875 ≤ (373108838489/1250000000000 : ℝ)^3851
        have hw : |(3847849621/10000000000 : ℝ)|=(3847849621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4551264181/10000000000 : ℝ)|^4875 ≤ (18458553502109/50000000000000 : ℝ)^3851
        have hw : |(4551264181/10000000000 : ℝ)|=(4551264181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_4 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1633126477/10000000000 : ℝ)*x 0 + (5181548083/10000000000 : ℝ)*x 1 + (5452941037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633126477/10000000000 : ℝ)^4875 ≤ (10086903980923/100000000000000 : ℝ)^3851 := by
    have hnat : (1633126477 : ℕ)^4875*100000000000000^3851 ≤ 10086903980923^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633126477 10000000000 10086903980923 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181548083/10000000000 : ℝ)^4875 ≤ (43504372227769/100000000000000 : ℝ)^3851 := by
    have hnat : (5181548083 : ℕ)^4875*100000000000000^3851 ≤ 43504372227769^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181548083 10000000000 43504372227769 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452941037/10000000000 : ℝ)^4875 ≤ (23204361884781/50000000000000 : ℝ)^3851 := by
    have hnat : (5452941037 : ℕ)^4875*50000000000000^3851 ≤ 23204361884781^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452941037 10000000000 23204361884781 50000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1633126477/10000000000 : ℝ), (5181548083/10000000000 : ℝ), (5452941037/10000000000 : ℝ)] ![(10086903980923/100000000000000 : ℝ), (43504372227769/100000000000000 : ℝ), (23204361884781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1633126477/10000000000 : ℝ)|^4875 ≤ (10086903980923/100000000000000 : ℝ)^3851
        have hw : |(-1633126477/10000000000 : ℝ)|=(1633126477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181548083/10000000000 : ℝ)|^4875 ≤ (43504372227769/100000000000000 : ℝ)^3851
        have hw : |(5181548083/10000000000 : ℝ)|=(5181548083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452941037/10000000000 : ℝ)|^4875 ≤ (23204361884781/50000000000000 : ℝ)^3851
        have hw : |(5452941037/10000000000 : ℝ)|=(5452941037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_5 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527698903/1000000000 : ℝ)*x 0 + (-300326933/2000000000 : ℝ)*x 1 + (5452941281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527698903/1000000000 : ℝ)^4875 ≤ (11130311306767/25000000000000 : ℝ)^3851 := by
    have hnat : (527698903 : ℕ)^4875*25000000000000^3851 ≤ 11130311306767^3851*1000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527698903 1000000000 11130311306767 25000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300326933/2000000000 : ℝ)^4875 ≤ (283438386107/3125000000000 : ℝ)^3851 := by
    have hnat : (300326933 : ℕ)^4875*3125000000000^3851 ≤ 283438386107^3851*2000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300326933 2000000000 283438386107 3125000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452941281/10000000000 : ℝ)^4875 ≤ (5801090799797/12500000000000 : ℝ)^3851 := by
    have hnat : (5452941281 : ℕ)^4875*12500000000000^3851 ≤ 5801090799797^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452941281 10000000000 5801090799797 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527698903/1000000000 : ℝ), (-300326933/2000000000 : ℝ), (5452941281/10000000000 : ℝ)] ![(11130311306767/25000000000000 : ℝ), (283438386107/3125000000000 : ℝ), (5801090799797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527698903/1000000000 : ℝ)|^4875 ≤ (11130311306767/25000000000000 : ℝ)^3851
        have hw : |(527698903/1000000000 : ℝ)|=(527698903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-300326933/2000000000 : ℝ)|^4875 ≤ (283438386107/3125000000000 : ℝ)^3851
        have hw : |(-300326933/2000000000 : ℝ)|=(300326933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452941281/10000000000 : ℝ)|^4875 ≤ (5801090799797/12500000000000 : ℝ)^3851
        have hw : |(5452941281/10000000000 : ℝ)|=(5452941281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_6 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638494969/5000000000 : ℝ)*x 0 + (340808779/625000000 : ℝ)*x 1 + (-375408637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638494969/5000000000 : ℝ)^4875 ≤ (44521254924753/100000000000000 : ℝ)^3851 := by
    have hnat : (2638494969 : ℕ)^4875*100000000000000^3851 ≤ 44521254924753^3851*5000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638494969 5000000000 44521254924753 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340808779/625000000 : ℝ)^4875 ≤ (18128405311/39062500000 : ℝ)^3851 := by
    have hnat : (340808779 : ℕ)^4875*39062500000^3851 ≤ 18128405311^3851*625000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340808779 625000000 18128405311 39062500000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375408637/2500000000 : ℝ)^4875 ≤ (9070027460819/100000000000000 : ℝ)^3851 := by
    have hnat : (375408637 : ℕ)^4875*100000000000000^3851 ≤ 9070027460819^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375408637 2500000000 9070027460819 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638494969/5000000000 : ℝ), (340808779/625000000 : ℝ), (-375408637/2500000000 : ℝ)] ![(44521254924753/100000000000000 : ℝ), (18128405311/39062500000 : ℝ), (9070027460819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638494969/5000000000 : ℝ)|^4875 ≤ (44521254924753/100000000000000 : ℝ)^3851
        have hw : |(2638494969/5000000000 : ℝ)|=(2638494969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340808779/625000000 : ℝ)|^4875 ≤ (18128405311/39062500000 : ℝ)^3851
        have hw : |(340808779/625000000 : ℝ)|=(340808779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-375408637/2500000000 : ℝ)|^4875 ≤ (9070027460819/100000000000000 : ℝ)^3851
        have hw : |(-375408637/2500000000 : ℝ)|=(375408637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1639_s2_7 (p : ℝ) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047214709/2500000000 : ℝ)*x 0 + (4545808727/10000000000 : ℝ)*x 1 + (240835293/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047214709/2500000000 : ℝ)^4875 ≤ (33236027060093/100000000000000 : ℝ)^3851 := by
    have hnat : (1047214709 : ℕ)^4875*100000000000000^3851 ≤ 33236027060093^3851*2500000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047214709 2500000000 33236027060093 100000000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4545808727/10000000000 : ℝ)^4875 ≤ (4607637241523/12500000000000 : ℝ)^3851 := by
    have hnat : (4545808727 : ℕ)^4875*12500000000000^3851 ≤ 4607637241523^3851*10000000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545808727 10000000000 4607637241523 12500000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240835293/625000000 : ℝ)^4875 ≤ (934464843293/3125000000000 : ℝ)^3851 := by
    have hnat : (240835293 : ℕ)^4875*3125000000000^3851 ≤ 934464843293^3851*625000000^4875 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240835293 625000000 934464843293 3125000000000 4875 3851 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4875/1024 : ℝ)) 4875 3851 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047214709/2500000000 : ℝ), (4545808727/10000000000 : ℝ), (240835293/625000000 : ℝ)] ![(33236027060093/100000000000000 : ℝ), (4607637241523/12500000000000 : ℝ), (934464843293/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047214709/2500000000 : ℝ)|^4875 ≤ (33236027060093/100000000000000 : ℝ)^3851
        have hw : |(1047214709/2500000000 : ℝ)|=(1047214709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4545808727/10000000000 : ℝ)|^4875 ≤ (4607637241523/12500000000000 : ℝ)^3851
        have hw : |(4545808727/10000000000 : ℝ)|=(4545808727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240835293/625000000 : ℝ)|^4875 ≤ (934464843293/3125000000000 : ℝ)^3851
        have hw : |(240835293/625000000 : ℝ)|=(240835293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1639_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4801/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16383/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17419/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4801/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17419/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4801/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17419/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4801/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17419/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4801/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17419/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4801/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17419/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4801/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4801/50000 : ℝ) ^ (4871/1024 : ℝ) ≤ (360746045974263/25000000000000000000 : ℝ) := by
    have hpowers : (4801/50000 : ℝ)^4871 ≤ (360746045974263/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4801 : ℕ)^4871*25000000000000000000^1024 ≤ 360746045974263^1024*50000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4801 50000 360746045974263 25000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4801/50000 : ℝ)) (X := (360746045974263/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17419/100000 : ℝ) ^ (4871/1024 : ℝ) ≤ (24528555502677619/100000000000000000000 : ℝ) := by
    have hpowers : (17419/100000 : ℝ)^4871 ≤ (24528555502677619/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17419 : ℕ)^4871*100000000000000000000^1024 ≤ 24528555502677619^1024*100000^4871 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17419 100000 24528555502677619 100000000000000000000 4871 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17419/100000 : ℝ)) (X := (24528555502677619/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500360746045974263/12500000000000000000 : ℝ) ≤ (5000030334612301/5000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (12500360746045974263/12500000000000000000 : ℝ)^1024 ≤ (5000030334612301/5000000000000000 : ℝ)^4871 := by
      have hnat : (12500360746045974263 : ℕ)^1024*5000000000000000^4871 ≤ 5000030334612301^4871*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500360746045974263 12500000000000000000 5000030334612301 5000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000030334612301/5000000000000000 : ℝ)) (X := (12500360746045974263/12500000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025971539686574671/100000000000000000000 : ℝ) ≤ (5000272963760341/5000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (100025971539686574671/100000000000000000000 : ℝ)^1024 ≤ (5000272963760341/5000000000000000 : ℝ)^4871 := by
      have hnat : (100025971539686574671 : ℕ)^1024*5000000000000000^4871 ≤ 5000272963760341^4871*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025971539686574671 100000000000000000000 5000272963760341 5000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000272963760341/5000000000000000 : ℝ)) (X := (100025971539686574671/100000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024528555502677619/50000000000000000000 : ℝ) ≤ (5000515592908381/5000000000000000 : ℝ) ^ (4871/1024 : ℝ) := by
    have hpowers : (50024528555502677619/50000000000000000000 : ℝ)^1024 ≤ (5000515592908381/5000000000000000 : ℝ)^4871 := by
      have hnat : (50024528555502677619 : ℕ)^1024*5000000000000000^4871 ≤ 5000515592908381^4871*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024528555502677619 50000000000000000000 5000515592908381 5000000000000000 1024 4871 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000515592908381/5000000000000000 : ℝ)) (X := (50024528555502677619/50000000000000000000 : ℝ)) (by norm_num) 4871 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(360746045974263/25000000000000000000 : ℝ) ≤ ((39080577675505396757/39085000000000000000 : ℝ)+2*(6065728701/9771250000000 : ℝ)*(4801/50000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (39080577675505396757/39085000000000000000 : ℝ)+2*(6065728701/9771250000000 : ℝ)*(4801/50000 : ℝ)=(5000030334612301/5000000000000000 : ℝ) by norm_num, show 1+2*(360746045974263/25000000000000000000 : ℝ)=(12500360746045974263/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24528555502677619/100000000000000000000 : ℝ)+(360746045974263/25000000000000000000 : ℝ) ≤ ((39080577675505396757/39085000000000000000 : ℝ)+(6065728701/9771250000000 : ℝ)*((17419/100000 : ℝ)+(4801/50000 : ℝ)))^(4871/1024 : ℝ) := by
    rw [show (39080577675505396757/39085000000000000000 : ℝ)+(6065728701/9771250000000 : ℝ)*((17419/100000 : ℝ)+(4801/50000 : ℝ))=(5000272963760341/5000000000000000 : ℝ) by norm_num, show 1+(24528555502677619/100000000000000000000 : ℝ)+(360746045974263/25000000000000000000 : ℝ)=(100025971539686574671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24528555502677619/100000000000000000000 : ℝ) ≤ ((39080577675505396757/39085000000000000000 : ℝ)+2*(6065728701/9771250000000 : ℝ)*(17419/100000 : ℝ))^(4871/1024 : ℝ) := by
    rw [show (39080577675505396757/39085000000000000000 : ℝ)+2*(6065728701/9771250000000 : ℝ)*(17419/100000 : ℝ)=(5000515592908381/5000000000000000 : ℝ) by norm_num, show 1+2*(24528555502677619/100000000000000000000 : ℝ)=(50024528555502677619/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39080577675505396757/39085000000000000000 : ℝ)*(X 1 0+X 2 0)+(6065728701/9771250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (4801/50000 : ℝ)) (hi := (17419/100000 : ℝ)) (c := (39080577675505396757/39085000000000000000 : ℝ)) (alpha := (6065728701/9771250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39080577675505396757/39085000000000000000 : ℝ)*(X 0 1+X 2 1)+(6065728701/9771250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (4801/50000 : ℝ)) (hi := (17419/100000 : ℝ)) (c := (39080577675505396757/39085000000000000000 : ℝ)) (alpha := (6065728701/9771250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39080577675505396757/39085000000000000000 : ℝ)*(X 0 2+X 1 2)+(6065728701/9771250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4871/1024 : ℝ)) (lo := (4801/50000 : ℝ)) (hi := (17419/100000 : ℝ)) (c := (39080577675505396757/39085000000000000000 : ℝ)) (alpha := (6065728701/9771250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81652771/500000000 : ℝ)*X 0 0+(1091020533/2000000000 : ℝ)*X 0 1+(5179408951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350543659/10000000000 : ℝ)*X 1 0+(-443792011/2500000000 : ℝ)*X 1 1+(5179409693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350546101/10000000000 : ℝ)*X 2 0+(5179408373/10000000000 : ℝ)*X 2 1+(-71006661/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((418867553/1000000000 : ℝ)*X 0 0+(3847849621/10000000000 : ℝ)*X 0 1+(4551264181/10000000000 : ℝ)*X 0 2+(418867553/1000000000 : ℝ)*X 1 0+(3847849621/10000000000 : ℝ)*X 1 1+(4551264181/10000000000 : ℝ)*X 1 2+(418867553/1000000000 : ℝ)*X 2 0+(3847849621/10000000000 : ℝ)*X 2 1+(4551264181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1633126477/10000000000 : ℝ)*X 0 0+(5181548083/10000000000 : ℝ)*X 0 1+(5452941037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527698903/1000000000 : ℝ)*X 1 0+(-300326933/2000000000 : ℝ)*X 1 1+(5452941281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638494969/5000000000 : ℝ)*X 2 0+(340808779/625000000 : ℝ)*X 2 1+(-375408637/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1047214709/2500000000 : ℝ)*X 0 0+(4545808727/10000000000 : ℝ)*X 0 1+(240835293/625000000 : ℝ)*X 0 2+(1047214709/2500000000 : ℝ)*X 1 0+(4545808727/10000000000 : ℝ)*X 1 1+(240835293/625000000 : ℝ)*X 1 2+(1047214709/2500000000 : ℝ)*X 2 0+(4545808727/10000000000 : ℝ)*X 2 1+(240835293/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1639_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (787791803592525572290656399/97712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16883637/6250000000000 : ℝ)*(base19) + (1987153969/100000000000000 : ℝ)*(base23) + (73201903/100000000000000 : ℝ)*(upper4) + (64804659/12500000000000 : ℝ)*(upper5) + (252445201446231/10000000000000 : ℝ)*(major0) + (252445201446231/10000000000000 : ℝ)*(major1) + (252445201446231/10000000000000 : ℝ)*(major2) + (906805437935073/25000000000000 : ℝ)*(sp0) + (725447216371593/20000000000000 : ℝ)*(sp1) + (3627248792831/100000000000 : ℝ)*(sp2) + (56865808792121/4000000000000 : ℝ)*(sp3) + (29028244677/100000000000000 : ℝ)*(sp4) + (3606997203/25000000000000 : ℝ)*(sp5) + (1552078363/20000000000000 : ℝ)*(sp7) + (35541324504871/2500000000000 : ℝ)*(f.failure) + (3627250779984969/100000000000000 : ℝ)*(f.sum) + (27092959285197/7817000000000000000000000000 : ℝ)*base66 + (2150227002100422867/390850000000000000000000000000000 : ℝ)*base67 + (1429388372053172867/390850000000000000000000000000000 : ℝ)*base69 + (2334013863329022867/390850000000000000000000000000000 : ℝ)*base71 + (1821851124107/781700000000000000000000000 : ℝ)*base74 + (1183567495113572867/390850000000000000000000000000000 : ℝ)*base75 + (927943905620227133/390850000000000000000000000000000 : ℝ)*base78 + (2332917863255772867/390850000000000000000000000000000 : ℝ)*base79 + (954445776641/1563400000000000000000000000 : ℝ)*base82 + (242409/50000000000000000000 : ℝ)*base90 + (242409/50000000000000000000 : ℝ)*base92 + (242409/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2143785519655571403094705449/195425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (548891301/50000000000000 : ℝ)*(base19) + (2333996593/100000000000000 : ℝ)*(base23) + (215896351/100000000000000 : ℝ)*(upper3) + (230926953/100000000000000 : ℝ)*(lower4) + (512885364929319/20000000000000 : ℝ)*(major0) + (512885364929319/20000000000000 : ℝ)*(major1) + (512885364929319/20000000000000 : ℝ)*(major2) + (13642966867/100000000000000 : ℝ)*(sp1) + (636257561/2500000000000 : ℝ)*(sp2) + (311264607/20000000000000 : ℝ)*(sp3) + (14393313926251/390625000000 : ℝ)*(sp4) + (1842336812185393/50000000000000 : ℝ)*(sp5) + (460582572602653/12500000000000 : ℝ)*(sp6) + (72208168109389/5000000000000 : ℝ)*(sp7) + (722082459255407/50000000000000 : ℝ)*(f.failure) + (14393313926251/390625000000 : ℝ)*(f.sum) + (6371448971343/3908500000000000000000000000 : ℝ)*base66 + (7298611087280281517/781700000000000000000000000000000 : ℝ)*base68 + (5376662810487081517/781700000000000000000000000000000 : ℝ)*base70 + (2610971265035718483/781700000000000000000000000000000 : ℝ)*base71 + (37237791371349/7817000000000000000000000000 : ℝ)*base74 + (9648741818469581517/781700000000000000000000000000000 : ℝ)*base76 + (9809621549036581517/781700000000000000000000000000000 : ℝ)*base78 + (16113583094493881517/781700000000000000000000000000000 : ℝ)*base80 + (10339285391671/7817000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (4816353/1000000000000000000000 : ℝ)*base90 + (4816353/1000000000000000000000 : ℝ)*base92 + (4816353/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1639_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17419/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4801/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1639_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1639_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1639_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1639_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1639_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4871/1024 : ℝ) ≤ p) (hpb : p ≤ (4875/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35514321/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1639_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

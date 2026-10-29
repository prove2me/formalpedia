-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:45.705776+00:00
-- url     : https://prove2.me/submissions/985b8b53-78a2-4518-a34a-029283869503

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
theorem support_rectangle_w1364_s0_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-449052913/2500000000 : ℝ)*x 0 + (5987469003/10000000000 : ℝ)*x 1 + (4816130887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449052913/2500000000 : ℝ)^1081 ≤ (2635860327887/25000000000000 : ℝ)^825 := by
    have hnat : (449052913 : ℕ)^1081*25000000000000^825 ≤ 2635860327887^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449052913 2500000000 2635860327887 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5987469003/10000000000 : ℝ)^1081 ≤ (10212949581737/20000000000000 : ℝ)^825 := by
    have hnat : (5987469003 : ℕ)^1081*20000000000000^825 ≤ 10212949581737^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987469003 10000000000 10212949581737 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4816130887/10000000000 : ℝ)^1081 ≤ (7678362152787/20000000000000 : ℝ)^825 := by
    have hnat : (4816130887 : ℕ)^1081*20000000000000^825 ≤ 7678362152787^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816130887 10000000000 7678362152787 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449052913/2500000000 : ℝ), (5987469003/10000000000 : ℝ), (4816130887/10000000000 : ℝ)] ![(2635860327887/25000000000000 : ℝ), (10212949581737/20000000000000 : ℝ), (7678362152787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449052913/2500000000 : ℝ)|^1081 ≤ (2635860327887/25000000000000 : ℝ)^825
        have hw : |(-449052913/2500000000 : ℝ)|=(449052913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5987469003/10000000000 : ℝ)|^1081 ≤ (10212949581737/20000000000000 : ℝ)^825
        have hw : |(5987469003/10000000000 : ℝ)|=(5987469003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4816130887/10000000000 : ℝ)|^1081 ≤ (7678362152787/20000000000000 : ℝ)^825
        have hw : |(4816130887/10000000000 : ℝ)|=(4816130887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1099870103/2000000000 : ℝ)*x 0 + (-1230468707/5000000000 : ℝ)*x 1 + (963226283/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099870103/2000000000 : ℝ)^1081 ≤ (2284016551029/5000000000000 : ℝ)^825 := by
    have hnat : (1099870103 : ℕ)^1081*5000000000000^825 ≤ 2284016551029^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099870103 2000000000 2284016551029 5000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230468707/5000000000 : ℝ)^1081 ≤ (15927852687567/100000000000000 : ℝ)^825 := by
    have hnat : (1230468707 : ℕ)^1081*100000000000000^825 ≤ 15927852687567^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230468707 5000000000 15927852687567 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963226283/2000000000 : ℝ)^1081 ≤ (38391816278941/100000000000000 : ℝ)^825 := by
    have hnat : (963226283 : ℕ)^1081*100000000000000^825 ≤ 38391816278941^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963226283 2000000000 38391816278941 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099870103/2000000000 : ℝ), (-1230468707/5000000000 : ℝ), (963226283/2000000000 : ℝ)] ![(2284016551029/5000000000000 : ℝ), (15927852687567/100000000000000 : ℝ), (38391816278941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099870103/2000000000 : ℝ)|^1081 ≤ (2284016551029/5000000000000 : ℝ)^825
        have hw : |(1099870103/2000000000 : ℝ)|=(1099870103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1230468707/5000000000 : ℝ)|^1081 ≤ (15927852687567/100000000000000 : ℝ)^825
        have hw : |(-1230468707/5000000000 : ℝ)|=(1230468707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963226283/2000000000 : ℝ)|^1081 ≤ (38391816278941/100000000000000 : ℝ)^825
        have hw : |(963226283/2000000000 : ℝ)|=(963226283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2749675197/5000000000 : ℝ)*x 0 + (4816130859/10000000000 : ℝ)*x 1 + (-492187651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749675197/5000000000 : ℝ)^1081 ≤ (45680329703613/100000000000000 : ℝ)^825 := by
    have hnat : (2749675197 : ℕ)^1081*100000000000000^825 ≤ 45680329703613^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749675197 5000000000 45680329703613 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4816130859/10000000000 : ℝ)^1081 ≤ (38391810471473/100000000000000 : ℝ)^825 := by
    have hnat : (4816130859 : ℕ)^1081*100000000000000^825 ≤ 38391810471473^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816130859 10000000000 38391810471473 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492187651/2000000000 : ℝ)^1081 ≤ (7963929909891/50000000000000 : ℝ)^825 := by
    have hnat : (492187651 : ℕ)^1081*50000000000000^825 ≤ 7963929909891^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492187651 2000000000 7963929909891 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749675197/5000000000 : ℝ), (4816130859/10000000000 : ℝ), (-492187651/2000000000 : ℝ)] ![(45680329703613/100000000000000 : ℝ), (38391810471473/100000000000000 : ℝ), (7963929909891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749675197/5000000000 : ℝ)|^1081 ≤ (45680329703613/100000000000000 : ℝ)^825
        have hw : |(2749675197/5000000000 : ℝ)|=(2749675197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4816130859/10000000000 : ℝ)|^1081 ≤ (38391810471473/100000000000000 : ℝ)^825
        have hw : |(4816130859/10000000000 : ℝ)|=(4816130859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492187651/2000000000 : ℝ)|^1081 ≤ (7963929909891/50000000000000 : ℝ)^825
        have hw : |(-492187651/2000000000 : ℝ)|=(492187651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4175472009/10000000000 : ℝ)*x 0 + (3105546843/10000000000 : ℝ)*x 1 + (557932199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175472009/10000000000 : ℝ)^1081 ≤ (31842662055437/100000000000000 : ℝ)^825 := by
    have hnat : (4175472009 : ℕ)^1081*100000000000000^825 ≤ 31842662055437^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175472009 10000000000 31842662055437 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105546843/10000000000 : ℝ)^1081 ≤ (10802318979357/50000000000000 : ℝ)^825 := by
    have hnat : (3105546843 : ℕ)^1081*50000000000000^825 ≤ 10802318979357^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105546843 10000000000 10802318979357 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557932199/1000000000 : ℝ)^1081 ≤ (46552699972287/100000000000000 : ℝ)^825 := by
    have hnat : (557932199 : ℕ)^1081*100000000000000^825 ≤ 46552699972287^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557932199 1000000000 46552699972287 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175472009/10000000000 : ℝ), (3105546843/10000000000 : ℝ), (557932199/1000000000 : ℝ)] ![(31842662055437/100000000000000 : ℝ), (10802318979357/50000000000000 : ℝ), (46552699972287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175472009/10000000000 : ℝ)|^1081 ≤ (31842662055437/100000000000000 : ℝ)^825
        have hw : |(4175472009/10000000000 : ℝ)|=(4175472009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105546843/10000000000 : ℝ)|^1081 ≤ (10802318979357/50000000000000 : ℝ)^825
        have hw : |(3105546843/10000000000 : ℝ)|=(3105546843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(557932199/1000000000 : ℝ)|^1081 ≤ (46552699972287/100000000000000 : ℝ)^825
        have hw : |(557932199/1000000000 : ℝ)|=(557932199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1800554147/10000000000 : ℝ)*x 0 + (4846237453/10000000000 : ℝ)*x 1 + (5956286707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800554147/10000000000 : ℝ)^1081 ≤ (10576853023417/100000000000000 : ℝ)^825 := by
    have hnat : (1800554147 : ℕ)^1081*100000000000000^825 ≤ 10576853023417^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800554147 10000000000 10576853023417 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4846237453/10000000000 : ℝ)^1081 ≤ (38706581021729/100000000000000 : ℝ)^825 := by
    have hnat : (4846237453 : ℕ)^1081*100000000000000^825 ≤ 38706581021729^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846237453 10000000000 38706581021729 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5956286707/10000000000 : ℝ)^1081 ≤ (25358282973219/50000000000000 : ℝ)^825 := by
    have hnat : (5956286707 : ℕ)^1081*50000000000000^825 ≤ 25358282973219^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956286707 10000000000 25358282973219 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1800554147/10000000000 : ℝ), (4846237453/10000000000 : ℝ), (5956286707/10000000000 : ℝ)] ![(10576853023417/100000000000000 : ℝ), (38706581021729/100000000000000 : ℝ), (25358282973219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1800554147/10000000000 : ℝ)|^1081 ≤ (10576853023417/100000000000000 : ℝ)^825
        have hw : |(-1800554147/10000000000 : ℝ)|=(1800554147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4846237453/10000000000 : ℝ)|^1081 ≤ (38706581021729/100000000000000 : ℝ)^825
        have hw : |(4846237453/10000000000 : ℝ)|=(4846237453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5956286707/10000000000 : ℝ)|^1081 ≤ (25358282973219/50000000000000 : ℝ)^825
        have hw : |(5956286707/10000000000 : ℝ)|=(5956286707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5179988551/10000000000 : ℝ)*x 0 + (-660392113/5000000000 : ℝ)*x 1 + (1489071463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5179988551/10000000000 : ℝ)^1081 ≤ (42236134166113/100000000000000 : ℝ)^825 := by
    have hnat : (5179988551 : ℕ)^1081*100000000000000^825 ≤ 42236134166113^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179988551 10000000000 42236134166113 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660392113/5000000000 : ℝ)^1081 ≤ (7047309414541/100000000000000 : ℝ)^825 := by
    have hnat : (660392113 : ℕ)^1081*100000000000000^825 ≤ 7047309414541^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660392113 5000000000 7047309414541 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489071463/2500000000 : ℝ)^1081 ≤ (10143311281447/20000000000000 : ℝ)^825 := by
    have hnat : (1489071463 : ℕ)^1081*20000000000000^825 ≤ 10143311281447^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489071463 2500000000 10143311281447 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5179988551/10000000000 : ℝ), (-660392113/5000000000 : ℝ), (1489071463/2500000000 : ℝ)] ![(42236134166113/100000000000000 : ℝ), (7047309414541/100000000000000 : ℝ), (10143311281447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5179988551/10000000000 : ℝ)|^1081 ≤ (42236134166113/100000000000000 : ℝ)^825
        have hw : |(5179988551/10000000000 : ℝ)|=(5179988551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660392113/5000000000 : ℝ)|^1081 ≤ (7047309414541/100000000000000 : ℝ)^825
        have hw : |(-660392113/5000000000 : ℝ)|=(660392113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1489071463/2500000000 : ℝ)|^1081 ≤ (10143311281447/20000000000000 : ℝ)^825
        have hw : |(1489071463/2500000000 : ℝ)|=(1489071463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (647498521/1250000000 : ℝ)*x 0 + (5956287101/10000000000 : ℝ)*x 1 + (-1320782817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647498521/1250000000 : ℝ)^1081 ≤ (8447226014841/20000000000000 : ℝ)^825 := by
    have hnat : (647498521 : ℕ)^1081*20000000000000^825 ≤ 8447226014841^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647498521 1250000000 8447226014841 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5956287101/10000000000 : ℝ)^1081 ≤ (25358285171141/50000000000000 : ℝ)^825 := by
    have hnat : (5956287101 : ℕ)^1081*50000000000000^825 ≤ 25358285171141^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956287101 10000000000 25358285171141 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320782817/10000000000 : ℝ)^1081 ≤ (3523649781841/50000000000000 : ℝ)^825 := by
    have hnat : (1320782817 : ℕ)^1081*50000000000000^825 ≤ 3523649781841^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320782817 10000000000 3523649781841 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647498521/1250000000 : ℝ), (5956287101/10000000000 : ℝ), (-1320782817/10000000000 : ℝ)] ![(8447226014841/20000000000000 : ℝ), (25358285171141/50000000000000 : ℝ), (3523649781841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647498521/1250000000 : ℝ)|^1081 ≤ (8447226014841/20000000000000 : ℝ)^825
        have hw : |(647498521/1250000000 : ℝ)|=(647498521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5956287101/10000000000 : ℝ)|^1081 ≤ (25358285171141/50000000000000 : ℝ)^825
        have hw : |(5956287101/10000000000 : ℝ)|=(5956287101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1320782817/10000000000 : ℝ)|^1081 ≤ (3523649781841/50000000000000 : ℝ)^825
        have hw : |(-1320782817/10000000000 : ℝ)|=(1320782817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s0_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4184637899/10000000000 : ℝ)*x 0 + (5515741269/10000000000 : ℝ)*x 1 + (1585700949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184637899/10000000000 : ℝ)^1081 ≤ (31934283680771/100000000000000 : ℝ)^825 := by
    have hnat : (4184637899 : ℕ)^1081*100000000000000^825 ≤ 31934283680771^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184637899 10000000000 31934283680771 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5515741269/10000000000 : ℝ)^1081 ≤ (45858810859141/100000000000000 : ℝ)^825 := by
    have hnat : (5515741269 : ℕ)^1081*100000000000000^825 ≤ 45858810859141^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515741269 10000000000 45858810859141 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1585700949/5000000000 : ℝ)^1081 ≤ (4441381086533/20000000000000 : ℝ)^825 := by
    have hnat : (1585700949 : ℕ)^1081*20000000000000^825 ≤ 4441381086533^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585700949 5000000000 4441381086533 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184637899/10000000000 : ℝ), (5515741269/10000000000 : ℝ), (1585700949/5000000000 : ℝ)] ![(31934283680771/100000000000000 : ℝ), (45858810859141/100000000000000 : ℝ), (4441381086533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184637899/10000000000 : ℝ)|^1081 ≤ (31934283680771/100000000000000 : ℝ)^825
        have hw : |(4184637899/10000000000 : ℝ)|=(4184637899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5515741269/10000000000 : ℝ)|^1081 ≤ (45858810859141/100000000000000 : ℝ)^825
        have hw : |(5515741269/10000000000 : ℝ)|=(5515741269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1585700949/5000000000 : ℝ)|^1081 ≤ (4441381086533/20000000000000 : ℝ)^825
        have hw : |(1585700949/5000000000 : ℝ)|=(1585700949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (789/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13357/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4323/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4323 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4323*1^1024 ≤ 0^1024*1^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4323/1024 : ℝ) ≤ (2089415194107674361/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4323 ≤ (2089415194107674361/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4323*100000000000000000000^1024 ≤ 2089415194107674361^1024*5^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2089415194107674361 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2089415194107674361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4323 := by
      have hnat : (1 : ℕ)^1024*1^4323 ≤ 1^4323*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102089415194107674361/100000000000000000000 : ℝ) ≤ (10049102708723153/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (102089415194107674361/100000000000000000000 : ℝ)^1024 ≤ (10049102708723153/10000000000000000 : ℝ)^4323 := by
      have hnat : (102089415194107674361 : ℕ)^1024*10000000000000000^4323 ≤ 10049102708723153^4323*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102089415194107674361 100000000000000000000 10049102708723153 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10049102708723153/10000000000000000 : ℝ)) (X := (102089415194107674361/100000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52089415194107674361/50000000000000000000 : ℝ) ≤ (5049102708723153/5000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (52089415194107674361/50000000000000000000 : ℝ)^1024 ≤ (5049102708723153/5000000000000000 : ℝ)^4323 := by
      have hnat : (52089415194107674361 : ℕ)^1024*5000000000000000^4323 ≤ 5049102708723153^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52089415194107674361 50000000000000000000 5049102708723153 5000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5049102708723153/5000000000000000 : ℝ)) (X := (52089415194107674361/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(49102708723153/4000000000000000 : ℝ)*(0 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49102708723153/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2089415194107674361/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(49102708723153/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (1 : ℝ)+(49102708723153/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10049102708723153/10000000000000000 : ℝ) by norm_num, show 1+(2089415194107674361/100000000000000000000 : ℝ)+(0 : ℝ)=(102089415194107674361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2089415194107674361/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(49102708723153/4000000000000000 : ℝ)*(2/5 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(49102708723153/4000000000000000 : ℝ)*(2/5 : ℝ)=(5049102708723153/5000000000000000 : ℝ) by norm_num, show 1+2*(2089415194107674361/100000000000000000000 : ℝ)=(52089415194107674361/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(49102708723153/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49102708723153/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(49102708723153/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49102708723153/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(49102708723153/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (49102708723153/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-449052913/2500000000 : ℝ)*X 0 0+(5987469003/10000000000 : ℝ)*X 0 1+(4816130887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1099870103/2000000000 : ℝ)*X 1 0+(-1230468707/5000000000 : ℝ)*X 1 1+(963226283/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2749675197/5000000000 : ℝ)*X 2 0+(4816130859/10000000000 : ℝ)*X 2 1+(-492187651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4175472009/10000000000 : ℝ)*X 0 0+(3105546843/10000000000 : ℝ)*X 0 1+(557932199/1000000000 : ℝ)*X 0 2+(4175472009/10000000000 : ℝ)*X 1 0+(3105546843/10000000000 : ℝ)*X 1 1+(557932199/1000000000 : ℝ)*X 1 2+(4175472009/10000000000 : ℝ)*X 2 0+(3105546843/10000000000 : ℝ)*X 2 1+(557932199/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1800554147/10000000000 : ℝ)*X 0 0+(4846237453/10000000000 : ℝ)*X 0 1+(5956286707/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5179988551/10000000000 : ℝ)*X 1 0+(-660392113/5000000000 : ℝ)*X 1 1+(1489071463/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647498521/1250000000 : ℝ)*X 2 0+(5956287101/10000000000 : ℝ)*X 2 1+(-1320782817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4184637899/10000000000 : ℝ)*X 0 0+(5515741269/10000000000 : ℝ)*X 0 1+(1585700949/5000000000 : ℝ)*X 0 2+(4184637899/10000000000 : ℝ)*X 1 0+(5515741269/10000000000 : ℝ)*X 1 1+(1585700949/5000000000 : ℝ)*X 1 2+(4184637899/10000000000 : ℝ)*X 2 0+(5515741269/10000000000 : ℝ)*X 2 1+(1585700949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135034525701930610252773/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171695651/100000000000000 : ℝ)*(base1) + (3129207/250000000000 : ℝ)*(base19) + (1232898501/100000000000000 : ℝ)*(base23) + (233329967/100000000000000 : ℝ)*(upper3) + (10619231/100000000000000 : ℝ)*(upper5) + (157247050555153/25000000000000 : ℝ)*(major0) + (157247050555153/25000000000000 : ℝ)*(major1) + (157247050555153/25000000000000 : ℝ)*(major2) + (1707458027241/200000000000 : ℝ)*(sp0) + (853730904807713/100000000000000 : ℝ)*(sp1) + (853730923592011/100000000000000 : ℝ)*(sp2) + (101060456906961/25000000000000 : ℝ)*(sp3) + (3314565663/100000000000000 : ℝ)*(sp4) + (82743247/4000000000000 : ℝ)*(sp7) + (40424406790467/10000000000000 : ℝ)*(f.failure) + (53358259780657/6250000000000 : ℝ)*(f.sum) + (155531961557409/50000000000000000000000000000 : ℝ)*base65 + (256919893957409/100000000000000000000000000000 : ℝ)*base67 + (404055939457409/100000000000000000000000000000 : ℝ)*base69 + (590355222957409/100000000000000000000000000000 : ℝ)*base71 + (54977234692591/50000000000000000000000000000 : ℝ)*base74 + (467888074057409/100000000000000000000000000000 : ℝ)*base75 + (877797209057409/100000000000000000000000000000 : ℝ)*base77 + (1227996932957409/100000000000000000000000000000 : ℝ)*base79 + (20259510692591/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4888417/1000000000000000000000 : ℝ)*base90 + (4888417/1000000000000000000000 : ℝ)*base92 + (4888417/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1889189730086074532380743/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (655607947/50000000000000 : ℝ)*(base19) + (1708831027/100000000000000 : ℝ)*(base23) + (229639303/50000000000000 : ℝ)*(base39) + (92744939/100000000000000 : ℝ)*(upper3) + (164860821/50000000000000 : ℝ)*(upper5) + (663708986446707/100000000000000 : ℝ)*(major0) + (663708986446707/100000000000000 : ℝ)*(major1) + (663708527168101/100000000000000 : ℝ)*(major2) + (3161412851/100000000000000 : ℝ)*(sp1) + (854536571/25000000000000 : ℝ)*(sp2) + (900858449891153/100000000000000 : ℝ)*(sp4) + (900853977262409/100000000000000 : ℝ)*(sp5) + (14075840346757/1562500000000 : ℝ)*(sp6) + (106639687214673/25000000000000 : ℝ)*(sp7) + (106639687214673/25000000000000 : ℝ)*(f.failure) + (900858909169759/100000000000000 : ℝ)*(f.sum) + (72065063306203/50000000000000000000000000000 : ℝ)*base65 + (1120579318942453/400000000000000000000000000000 : ℝ)*base67 + (2414698216707171/400000000000000000000000000000 : ℝ)*base69 + (640498408942453/400000000000000000000000000000 : ℝ)*base71 + (211490774156203/50000000000000000000000000000 : ℝ)*base73 + (3062561168092829/400000000000000000000000000000 : ℝ)*base76 + (178954744307171/400000000000000000000000000000 : ℝ)*base77 + (322317910707171/400000000000000000000000000000 : ℝ)*base79 + (1004991055507171/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (19905723/2500000000000000000000 : ℝ)*base90 + (19905723/2500000000000000000000 : ℝ)*base92 + (19905723/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (789/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13357/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1364_s1_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-494463597/2500000000 : ℝ)*x 0 + (5632410663/10000000000 : ℝ)*x 1 + (5054839391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494463597/2500000000 : ℝ)^1081 ≤ (2392386119943/20000000000000 : ℝ)^825 := by
    have hnat : (494463597 : ℕ)^1081*20000000000000^825 ≤ 2392386119943^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494463597 2500000000 2392386119943 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5632410663/10000000000 : ℝ)^1081 ≤ (5891745985321/12500000000000 : ℝ)^825 := by
    have hnat : (5632410663 : ℕ)^1081*12500000000000^825 ≤ 5891745985321^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5632410663 10000000000 5891745985321 12500000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5054839391/10000000000 : ℝ)^1081 ≤ (40904101509613/100000000000000 : ℝ)^825 := by
    have hnat : (5054839391 : ℕ)^1081*100000000000000^825 ≤ 40904101509613^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054839391 10000000000 40904101509613 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494463597/2500000000 : ℝ), (5632410663/10000000000 : ℝ), (5054839391/10000000000 : ℝ)] ![(2392386119943/20000000000000 : ℝ), (5891745985321/12500000000000 : ℝ), (40904101509613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494463597/2500000000 : ℝ)|^1081 ≤ (2392386119943/20000000000000 : ℝ)^825
        have hw : |(-494463597/2500000000 : ℝ)|=(494463597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5632410663/10000000000 : ℝ)|^1081 ≤ (5891745985321/12500000000000 : ℝ)^825
        have hw : |(5632410663/10000000000 : ℝ)|=(5632410663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5054839391/10000000000 : ℝ)|^1081 ≤ (40904101509613/100000000000000 : ℝ)^825
        have hw : |(5054839391/10000000000 : ℝ)|=(5054839391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2701717303/5000000000 : ℝ)*x 0 + (-457097707/2000000000 : ℝ)*x 1 + (1010968089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701717303/5000000000 : ℝ)^1081 ≤ (22319608063897/50000000000000 : ℝ)^825 := by
    have hnat : (2701717303 : ℕ)^1081*50000000000000^825 ≤ 22319608063897^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701717303 5000000000 22319608063897 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457097707/2000000000 : ℝ)^1081 ≤ (7228335586839/50000000000000 : ℝ)^825 := by
    have hnat : (457097707 : ℕ)^1081*50000000000000^825 ≤ 7228335586839^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457097707 2000000000 7228335586839 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010968089/2000000000 : ℝ)^1081 ≤ (40904112685239/100000000000000 : ℝ)^825 := by
    have hnat : (1010968089 : ℕ)^1081*100000000000000^825 ≤ 40904112685239^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010968089 2000000000 40904112685239 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701717303/5000000000 : ℝ), (-457097707/2000000000 : ℝ), (1010968089/2000000000 : ℝ)] ![(22319608063897/50000000000000 : ℝ), (7228335586839/50000000000000 : ℝ), (40904112685239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701717303/5000000000 : ℝ)|^1081 ≤ (22319608063897/50000000000000 : ℝ)^825
        have hw : |(2701717303/5000000000 : ℝ)|=(2701717303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-457097707/2000000000 : ℝ)|^1081 ≤ (7228335586839/50000000000000 : ℝ)^825
        have hw : |(-457097707/2000000000 : ℝ)|=(457097707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1010968089/2000000000 : ℝ)|^1081 ≤ (40904112685239/100000000000000 : ℝ)^825
        have hw : |(1010968089/2000000000 : ℝ)|=(1010968089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (43227479/80000000 : ℝ)*x 0 + (5054839581/10000000000 : ℝ)*x 1 + (-2285489289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43227479/80000000 : ℝ)^1081 ≤ (8927843807931/20000000000000 : ℝ)^825 := by
    have hnat : (43227479 : ℕ)^1081*20000000000000^825 ≤ 8927843807931^825*80000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43227479 80000000 8927843807931 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5054839581/10000000000 : ℝ)^1081 ≤ (20452051762097/50000000000000 : ℝ)^825 := by
    have hnat : (5054839581 : ℕ)^1081*50000000000000^825 ≤ 20452051762097^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054839581 10000000000 20452051762097 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285489289/10000000000 : ℝ)^1081 ≤ (14456677422993/100000000000000 : ℝ)^825 := by
    have hnat : (2285489289 : ℕ)^1081*100000000000000^825 ≤ 14456677422993^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285489289 10000000000 14456677422993 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43227479/80000000 : ℝ), (5054839581/10000000000 : ℝ), (-2285489289/10000000000 : ℝ)] ![(8927843807931/20000000000000 : ℝ), (20452051762097/50000000000000 : ℝ), (14456677422993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43227479/80000000 : ℝ)|^1081 ≤ (8927843807931/20000000000000 : ℝ)^825
        have hw : |(43227479/80000000 : ℝ)|=(43227479/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5054839581/10000000000 : ℝ)|^1081 ≤ (20452051762097/50000000000000 : ℝ)^825
        have hw : |(5054839581/10000000000 : ℝ)|=(5054839581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285489289/10000000000 : ℝ)|^1081 ≤ (14456677422993/100000000000000 : ℝ)^825
        have hw : |(-2285489289/10000000000 : ℝ)|=(2285489289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4288374379/10000000000 : ℝ)*x 0 + (3718293661/10000000000 : ℝ)*x 1 + (493807521/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4288374379/10000000000 : ℝ)^1081 ≤ (16487773216457/50000000000000 : ℝ)^825 := by
    have hnat : (4288374379 : ℕ)^1081*50000000000000^825 ≤ 16487773216457^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4288374379 10000000000 16487773216457 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3718293661/10000000000 : ℝ)^1081 ≤ (27353948823527/100000000000000 : ℝ)^825 := by
    have hnat : (3718293661 : ℕ)^1081*100000000000000^825 ≤ 27353948823527^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3718293661 10000000000 27353948823527 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493807521/1000000000 : ℝ)^1081 ≤ (39670504723631/100000000000000 : ℝ)^825 := by
    have hnat : (493807521 : ℕ)^1081*100000000000000^825 ≤ 39670504723631^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493807521 1000000000 39670504723631 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4288374379/10000000000 : ℝ), (3718293661/10000000000 : ℝ), (493807521/1000000000 : ℝ)] ![(16487773216457/50000000000000 : ℝ), (27353948823527/100000000000000 : ℝ), (39670504723631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4288374379/10000000000 : ℝ)|^1081 ≤ (16487773216457/50000000000000 : ℝ)^825
        have hw : |(4288374379/10000000000 : ℝ)|=(4288374379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3718293661/10000000000 : ℝ)|^1081 ≤ (27353948823527/100000000000000 : ℝ)^825
        have hw : |(3718293661/10000000000 : ℝ)|=(3718293661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(493807521/1000000000 : ℝ)|^1081 ≤ (39670504723631/100000000000000 : ℝ)^825
        have hw : |(493807521/1000000000 : ℝ)|=(493807521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1978352107/10000000000 : ℝ)*x 0 + (5061965199/10000000000 : ℝ)*x 1 + (5625157433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1978352107/10000000000 : ℝ)^1081 ≤ (2991468747507/25000000000000 : ℝ)^825 := by
    have hnat : (1978352107 : ℕ)^1081*25000000000000^825 ≤ 2991468747507^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978352107 10000000000 2991468747507 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5061965199/10000000000 : ℝ)^1081 ≤ (40979673403243/100000000000000 : ℝ)^825 := by
    have hnat : (5061965199 : ℕ)^1081*100000000000000^825 ≤ 40979673403243^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061965199 10000000000 40979673403243 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5625157433/10000000000 : ℝ)^1081 ≤ (11763612899551/25000000000000 : ℝ)^825 := by
    have hnat : (5625157433 : ℕ)^1081*25000000000000^825 ≤ 11763612899551^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625157433 10000000000 11763612899551 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1978352107/10000000000 : ℝ), (5061965199/10000000000 : ℝ), (5625157433/10000000000 : ℝ)] ![(2991468747507/25000000000000 : ℝ), (40979673403243/100000000000000 : ℝ), (11763612899551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1978352107/10000000000 : ℝ)|^1081 ≤ (2991468747507/25000000000000 : ℝ)^825
        have hw : |(-1978352107/10000000000 : ℝ)|=(1978352107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5061965199/10000000000 : ℝ)|^1081 ≤ (40979673403243/100000000000000 : ℝ)^825
        have hw : |(5061965199/10000000000 : ℝ)|=(5061965199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5625157433/10000000000 : ℝ)|^1081 ≤ (11763612899551/25000000000000 : ℝ)^825
        have hw : |(5625157433/10000000000 : ℝ)|=(5625157433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (262664543/500000000 : ℝ)*x 0 + (-1715171359/10000000000 : ℝ)*x 1 + (5625157507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262664543/500000000 : ℝ)^1081 ≤ (10755249427853/25000000000000 : ℝ)^825 := by
    have hnat : (262664543 : ℕ)^1081*25000000000000^825 ≤ 10755249427853^825*500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262664543 500000000 10755249427853 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1715171359/10000000000 : ℝ)^1081 ≤ (4962274929369/50000000000000 : ℝ)^825 := by
    have hnat : (1715171359 : ℕ)^1081*50000000000000^825 ≤ 4962274929369^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715171359 10000000000 4962274929369 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5625157507/10000000000 : ℝ)^1081 ≤ (9410890481859/20000000000000 : ℝ)^825 := by
    have hnat : (5625157507 : ℕ)^1081*20000000000000^825 ≤ 9410890481859^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625157507 10000000000 9410890481859 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262664543/500000000 : ℝ), (-1715171359/10000000000 : ℝ), (5625157507/10000000000 : ℝ)] ![(10755249427853/25000000000000 : ℝ), (4962274929369/50000000000000 : ℝ), (9410890481859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262664543/500000000 : ℝ)|^1081 ≤ (10755249427853/25000000000000 : ℝ)^825
        have hw : |(262664543/500000000 : ℝ)|=(262664543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1715171359/10000000000 : ℝ)|^1081 ≤ (4962274929369/50000000000000 : ℝ)^825
        have hw : |(-1715171359/10000000000 : ℝ)|=(1715171359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5625157507/10000000000 : ℝ)|^1081 ≤ (9410890481859/20000000000000 : ℝ)^825
        have hw : |(5625157507/10000000000 : ℝ)|=(5625157507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5253290753/10000000000 : ℝ)*x 0 + (5625157599/10000000000 : ℝ)*x 1 + (-1715171379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253290753/10000000000 : ℝ)^1081 ≤ (21510498281623/50000000000000 : ℝ)^825 := by
    have hnat : (5253290753 : ℕ)^1081*50000000000000^825 ≤ 21510498281623^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253290753 10000000000 21510498281623 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5625157599/10000000000 : ℝ)^1081 ≤ (23527226708839/50000000000000 : ℝ)^825 := by
    have hnat : (5625157599 : ℕ)^1081*50000000000000^825 ≤ 23527226708839^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625157599 10000000000 23527226708839 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1715171379/10000000000 : ℝ)^1081 ≤ (79396400083/800000000000 : ℝ)^825 := by
    have hnat : (1715171379 : ℕ)^1081*800000000000^825 ≤ 79396400083^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715171379 10000000000 79396400083 800000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253290753/10000000000 : ℝ), (5625157599/10000000000 : ℝ), (-1715171379/10000000000 : ℝ)] ![(21510498281623/50000000000000 : ℝ), (23527226708839/50000000000000 : ℝ), (79396400083/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253290753/10000000000 : ℝ)|^1081 ≤ (21510498281623/50000000000000 : ℝ)^825
        have hw : |(5253290753/10000000000 : ℝ)|=(5253290753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5625157599/10000000000 : ℝ)|^1081 ≤ (23527226708839/50000000000000 : ℝ)^825
        have hw : |(5625157599/10000000000 : ℝ)|=(5625157599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1715171379/10000000000 : ℝ)|^1081 ≤ (79396400083/800000000000 : ℝ)^825
        have hw : |(-1715171379/10000000000 : ℝ)|=(1715171379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s1_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4289426213/10000000000 : ℝ)*x 0 + (984605541/2000000000 : ℝ)*x 1 + (933402231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289426213/10000000000 : ℝ)^1081 ≤ (32986144698159/100000000000000 : ℝ)^825 := by
    have hnat : (4289426213 : ℕ)^1081*100000000000000^825 ≤ 32986144698159^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289426213 10000000000 32986144698159 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984605541/2000000000 : ℝ)^1081 ≤ (7902436582649/20000000000000 : ℝ)^825 := by
    have hnat : (984605541 : ℕ)^1081*20000000000000^825 ≤ 7902436582649^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984605541 2000000000 7902436582649 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933402231/2500000000 : ℝ)^1081 ≤ (27501672373137/100000000000000 : ℝ)^825 := by
    have hnat : (933402231 : ℕ)^1081*100000000000000^825 ≤ 27501672373137^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933402231 2500000000 27501672373137 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289426213/10000000000 : ℝ), (984605541/2000000000 : ℝ), (933402231/2500000000 : ℝ)] ![(32986144698159/100000000000000 : ℝ), (7902436582649/20000000000000 : ℝ), (27501672373137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289426213/10000000000 : ℝ)|^1081 ≤ (32986144698159/100000000000000 : ℝ)^825
        have hw : |(4289426213/10000000000 : ℝ)|=(4289426213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(984605541/2000000000 : ℝ)|^1081 ≤ (7902436582649/20000000000000 : ℝ)^825
        have hw : |(984605541/2000000000 : ℝ)|=(984605541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933402231/2500000000 : ℝ)|^1081 ≤ (27501672373137/100000000000000 : ℝ)^825
        have hw : |(933402231/2500000000 : ℝ)|=(933402231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (789/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (7091/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19299/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (789/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (789/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (789/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (789/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (789/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (789/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (789/50000 : ℝ) ^ (4323/1024 : ℝ) ≤ (2471638310031/100000000000000000000 : ℝ) := by
    have hpowers : (789/50000 : ℝ)^4323 ≤ (2471638310031/100000000000000000000 : ℝ)^1024 := by
      have hnat : (789 : ℕ)^4323*100000000000000000000^1024 ≤ 2471638310031^1024*50000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        789 50000 2471638310031 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (789/50000 : ℝ)) (X := (2471638310031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13357/50000 : ℝ) ^ (4323/1024 : ℝ) ≤ (380080290929872609/100000000000000000000 : ℝ) := by
    have hpowers : (13357/50000 : ℝ)^4323 ≤ (380080290929872609/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13357 : ℕ)^4323*100000000000000000000^1024 ≤ 380080290929872609^1024*50000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13357 50000 380080290929872609 100000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13357/50000 : ℝ)) (X := (380080290929872609/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000002471638310031/50000000000000000000 : ℝ) ≤ (1250000014636581/1250000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50000002471638310031/50000000000000000000 : ℝ)^1024 ≤ (1250000014636581/1250000000000000 : ℝ)^4323 := by
      have hnat : (50000002471638310031 : ℕ)^1024*1250000000000000^4323 ≤ 1250000014636581^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000002471638310031 50000000000000000000 1250000014636581 1250000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000014636581/1250000000000000 : ℝ)) (X := (50000002471638310031/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1254751034532102283/1250000000000000000 : ℝ) ≤ (10008990089269831/10000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (1254751034532102283/1250000000000000000 : ℝ)^1024 ≤ (10008990089269831/10000000000000000 : ℝ)^4323 := by
      have hnat : (1254751034532102283 : ℕ)^1024*10000000000000000^4323 ≤ 10008990089269831^4323*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1254751034532102283 1250000000000000000 10008990089269831 10000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008990089269831/10000000000000000 : ℝ)) (X := (1254751034532102283/1250000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50380080290929872609/50000000000000000000 : ℝ) ≤ (5008990030723507/5000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (50380080290929872609/50000000000000000000 : ℝ)^1024 ≤ (5008990030723507/5000000000000000 : ℝ)^4323 := by
      have hnat : (50380080290929872609 : ℕ)^1024*5000000000000000^4323 ≤ 5008990030723507^4323*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50380080290929872609 50000000000000000000 5008990030723507 5000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008990030723507/5000000000000000 : ℝ)) (X := (50380080290929872609/50000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2471638310031/100000000000000000000 : ℝ) ≤ ((12566581529552480529/12568000000000000000 : ℝ)+2*(8989972177183/2513600000000000 : ℝ)*(789/50000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (12566581529552480529/12568000000000000000 : ℝ)+2*(8989972177183/2513600000000000 : ℝ)*(789/50000 : ℝ)=(1250000014636581/1250000000000000 : ℝ) by norm_num, show 1+2*(2471638310031/100000000000000000000 : ℝ)=(50000002471638310031/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(380080290929872609/100000000000000000000 : ℝ)+(2471638310031/100000000000000000000 : ℝ) ≤ ((12566581529552480529/12568000000000000000 : ℝ)+(8989972177183/2513600000000000 : ℝ)*((13357/50000 : ℝ)+(789/50000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (12566581529552480529/12568000000000000000 : ℝ)+(8989972177183/2513600000000000 : ℝ)*((13357/50000 : ℝ)+(789/50000 : ℝ))=(10008990089269831/10000000000000000 : ℝ) by norm_num, show 1+(380080290929872609/100000000000000000000 : ℝ)+(2471638310031/100000000000000000000 : ℝ)=(1254751034532102283/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(380080290929872609/100000000000000000000 : ℝ) ≤ ((12566581529552480529/12568000000000000000 : ℝ)+2*(8989972177183/2513600000000000 : ℝ)*(13357/50000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (12566581529552480529/12568000000000000000 : ℝ)+2*(8989972177183/2513600000000000 : ℝ)*(13357/50000 : ℝ)=(5008990030723507/5000000000000000 : ℝ) by norm_num, show 1+2*(380080290929872609/100000000000000000000 : ℝ)=(50380080290929872609/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12566581529552480529/12568000000000000000 : ℝ)*(X 1 0+X 2 0)+(8989972177183/2513600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (789/50000 : ℝ)) (hi := (13357/50000 : ℝ)) (c := (12566581529552480529/12568000000000000000 : ℝ)) (alpha := (8989972177183/2513600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12566581529552480529/12568000000000000000 : ℝ)*(X 0 1+X 2 1)+(8989972177183/2513600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (789/50000 : ℝ)) (hi := (13357/50000 : ℝ)) (c := (12566581529552480529/12568000000000000000 : ℝ)) (alpha := (8989972177183/2513600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12566581529552480529/12568000000000000000 : ℝ)*(X 0 2+X 1 2)+(8989972177183/2513600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (789/50000 : ℝ)) (hi := (13357/50000 : ℝ)) (c := (12566581529552480529/12568000000000000000 : ℝ)) (alpha := (8989972177183/2513600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-494463597/2500000000 : ℝ)*X 0 0+(5632410663/10000000000 : ℝ)*X 0 1+(5054839391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2701717303/5000000000 : ℝ)*X 1 0+(-457097707/2000000000 : ℝ)*X 1 1+(1010968089/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((43227479/80000000 : ℝ)*X 2 0+(5054839581/10000000000 : ℝ)*X 2 1+(-2285489289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4288374379/10000000000 : ℝ)*X 0 0+(3718293661/10000000000 : ℝ)*X 0 1+(493807521/1000000000 : ℝ)*X 0 2+(4288374379/10000000000 : ℝ)*X 1 0+(3718293661/10000000000 : ℝ)*X 1 1+(493807521/1000000000 : ℝ)*X 1 2+(4288374379/10000000000 : ℝ)*X 2 0+(3718293661/10000000000 : ℝ)*X 2 1+(493807521/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1978352107/10000000000 : ℝ)*X 0 0+(5061965199/10000000000 : ℝ)*X 0 1+(5625157433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262664543/500000000 : ℝ)*X 1 0+(-1715171359/10000000000 : ℝ)*X 1 1+(5625157507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253290753/10000000000 : ℝ)*X 2 0+(5625157599/10000000000 : ℝ)*X 2 1+(-1715171379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289426213/10000000000 : ℝ)*X 0 0+(984605541/2000000000 : ℝ)*X 0 1+(933402231/2500000000 : ℝ)*X 0 2+(4289426213/10000000000 : ℝ)*X 1 0+(984605541/2000000000 : ℝ)*X 1 1+(933402231/2500000000 : ℝ)*X 1 2+(4289426213/10000000000 : ℝ)*X 2 0+(984605541/2000000000 : ℝ)*X 2 1+(933402231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4971146976291173182048941789/628400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20071017/100000000000000 : ℝ)*(base16) + (152197387/12500000000000 : ℝ)*(base19) + (333086597/25000000000000 : ℝ)*(base23) + (4593637/100000000000000 : ℝ)*(upper2) + (117863839/50000000000000 : ℝ)*(upper3) + (1275617871795647/100000000000000 : ℝ)*(major0) + (1275617871795647/100000000000000 : ℝ)*(major1) + (1275617871795647/100000000000000 : ℝ)*(major2) + (865699956699991/50000000000000 : ℝ)*(sp0) + (1731408121875367/100000000000000 : ℝ)*(sp1) + (432852006794773/25000000000000 : ℝ)*(sp2) + (819821868359457/100000000000000 : ℝ)*(sp3) + (4723062749/50000000000000 : ℝ)*(sp4) + (4252012999/100000000000000 : ℝ)*(sp7) + (102478265046557/12500000000000 : ℝ)*(f.failure) + (1731409359525479/100000000000000 : ℝ)*(f.sum) + (990336095334561/125680000000000000000000000000 : ℝ)*base65 + (3624215930625537737/1256800000000000000000000000000000 : ℝ)*base68 + (3356505090819137737/1256800000000000000000000000000000 : ℝ)*base70 + (4352374628180862263/1256800000000000000000000000000000 : ℝ)*base71 + (762066987769041/125680000000000000000000000000 : ℝ)*base73 + (1449940394458337737/1256800000000000000000000000000000 : ℝ)*base76 + (4456835950614462263/1256800000000000000000000000000000 : ℝ)*base77 + (11861142725956737737/1256800000000000000000000000000000 : ℝ)*base80 + (409132860320961/125680000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12591007/1250000000000000000000 : ℝ)*base90 + (12591007/1250000000000000000000 : ℝ)*base92 + (12591007/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (897320480950495823131719/125680000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74835491/100000000000000 : ℝ)*(base1) + (1448251837/100000000000000 : ℝ)*(base19) + (1411701809/100000000000000 : ℝ)*(base23) + (6747971/4000000000000 : ℝ)*(upper3) + (157865661/100000000000000 : ℝ)*(upper5) + (1308169738923743/100000000000000 : ℝ)*(major0) + (1308169738923743/100000000000000 : ℝ)*(major1) + (1308169738923743/100000000000000 : ℝ)*(major2) + (1910916587/25000000000000 : ℝ)*(sp1) + (1907548879/25000000000000 : ℝ)*(sp2) + (443898113363699/25000000000000 : ℝ)*(sp4) + (5548697770941/312500000000 : ℝ)*(sp5) + (1775583336721981/100000000000000 : ℝ)*(sp6) + (210186696600473/25000000000000 : ℝ)*(sp7) + (105093357654673/12500000000000 : ℝ)*(f.failure) + (355118475723861/20000000000000 : ℝ)*(f.sum) + (57506260475649/125680000000000000000000000000 : ℝ)*base65 + (4993666182807945047/1256800000000000000000000000000000 : ℝ)*base67 + (7182860197646345047/1256800000000000000000000000000000 : ℝ)*base69 + (5962489541031945047/1256800000000000000000000000000000 : ℝ)*base71 + (203026636147969/125680000000000000000000000000 : ℝ)*base73 + (5561411069771254953/1256800000000000000000000000000000 : ℝ)*base76 + (3581096798932054953/1256800000000000000000000000000000 : ℝ)*base78 + (4490596565416854953/1256800000000000000000000000000000 : ℝ)*base80 + (417612833417169/125680000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3154277/1250000000000000000000 : ℝ)*base89 + (3154277/1250000000000000000000 : ℝ)*base91 + (3154277/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1364_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (789/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7091/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19299/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1364_s2_0 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008065823/5000000000 : ℝ)*x 0 + (547388201/1000000000 : ℝ)*x 1 + (5188818721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008065823/5000000000 : ℝ)^1081 ≤ (6133085142877/50000000000000 : ℝ)^825 := by
    have hnat : (1008065823 : ℕ)^1081*50000000000000^825 ≤ 6133085142877^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008065823 5000000000 6133085142877 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547388201/1000000000 : ℝ)^1081 ≤ (45403330530279/100000000000000 : ℝ)^825 := by
    have hnat : (547388201 : ℕ)^1081*100000000000000^825 ≤ 45403330530279^825*1000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547388201 1000000000 45403330530279 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188818721/10000000000 : ℝ)^1081 ≤ (2645656198287/6250000000000 : ℝ)^825 := by
    have hnat : (5188818721 : ℕ)^1081*6250000000000^825 ≤ 2645656198287^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188818721 10000000000 2645656198287 6250000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008065823/5000000000 : ℝ), (547388201/1000000000 : ℝ), (5188818721/10000000000 : ℝ)] ![(6133085142877/50000000000000 : ℝ), (45403330530279/100000000000000 : ℝ), (2645656198287/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008065823/5000000000 : ℝ)|^1081 ≤ (6133085142877/50000000000000 : ℝ)^825
        have hw : |(-1008065823/5000000000 : ℝ)|=(1008065823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547388201/1000000000 : ℝ)|^1081 ≤ (45403330530279/100000000000000 : ℝ)^825
        have hw : |(547388201/1000000000 : ℝ)|=(547388201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188818721/10000000000 : ℝ)|^1081 ≤ (2645656198287/6250000000000 : ℝ)^825
        have hw : |(5188818721/10000000000 : ℝ)|=(5188818721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_1 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1341106461/2500000000 : ℝ)*x 0 + (-1081626431/5000000000 : ℝ)*x 1 + (2594409513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341106461/2500000000 : ℝ)^1081 ≤ (22108714634013/50000000000000 : ℝ)^825 := by
    have hnat : (1341106461 : ℕ)^1081*50000000000000^825 ≤ 22108714634013^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341106461 2500000000 22108714634013 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081626431/5000000000 : ℝ)^1081 ≤ (269041365749/2000000000000 : ℝ)^825 := by
    have hnat : (1081626431 : ℕ)^1081*2000000000000^825 ≤ 269041365749^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081626431 5000000000 269041365749 2000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594409513/5000000000 : ℝ)^1081 ≤ (10582625608221/25000000000000 : ℝ)^825 := by
    have hnat : (2594409513 : ℕ)^1081*25000000000000^825 ≤ 10582625608221^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594409513 5000000000 10582625608221 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341106461/2500000000 : ℝ), (-1081626431/5000000000 : ℝ), (2594409513/5000000000 : ℝ)] ![(22108714634013/50000000000000 : ℝ), (269041365749/2000000000000 : ℝ), (10582625608221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341106461/2500000000 : ℝ)|^1081 ≤ (22108714634013/50000000000000 : ℝ)^825
        have hw : |(1341106461/2500000000 : ℝ)|=(1341106461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081626431/5000000000 : ℝ)|^1081 ≤ (269041365749/2000000000000 : ℝ)^825
        have hw : |(-1081626431/5000000000 : ℝ)|=(1081626431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594409513/5000000000 : ℝ)|^1081 ≤ (10582625608221/25000000000000 : ℝ)^825
        have hw : |(2594409513/5000000000 : ℝ)|=(2594409513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_2 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5364425879/10000000000 : ℝ)*x 0 + (5188818977/10000000000 : ℝ)*x 1 + (-2163252879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364425879/10000000000 : ℝ)^1081 ≤ (22108714823021/50000000000000 : ℝ)^825 := by
    have hnat : (5364425879 : ℕ)^1081*50000000000000^825 ≤ 22108714823021^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364425879 10000000000 22108714823021 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188818977/10000000000 : ℝ)^1081 ≤ (423305019091/1000000000000 : ℝ)^825 := by
    have hnat : (5188818977 : ℕ)^1081*1000000000000^825 ≤ 423305019091^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188818977 10000000000 423305019091 1000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163252879/10000000000 : ℝ)^1081 ≤ (13452068425967/100000000000000 : ℝ)^825 := by
    have hnat : (2163252879 : ℕ)^1081*100000000000000^825 ≤ 13452068425967^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163252879 10000000000 13452068425967 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364425879/10000000000 : ℝ), (5188818977/10000000000 : ℝ), (-2163252879/10000000000 : ℝ)] ![(22108714823021/50000000000000 : ℝ), (423305019091/1000000000000 : ℝ), (13452068425967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364425879/10000000000 : ℝ)|^1081 ≤ (22108714823021/50000000000000 : ℝ)^825
        have hw : |(5364425879/10000000000 : ℝ)|=(5364425879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188818977/10000000000 : ℝ)|^1081 ≤ (423305019091/1000000000000 : ℝ)^825
        have hw : |(5188818977/10000000000 : ℝ)|=(5188818977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2163252879/10000000000 : ℝ)|^1081 ≤ (13452068425967/100000000000000 : ℝ)^825
        have hw : |(-2163252879/10000000000 : ℝ)|=(2163252879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_3 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (539400969/1250000000 : ℝ)*x 0 + (1005971423/2500000000 : ℝ)*x 1 + (1156479169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539400969/1250000000 : ℝ)^1081 ≤ (8311542736781/25000000000000 : ℝ)^825 := by
    have hnat : (539400969 : ℕ)^1081*25000000000000^825 ≤ 8311542736781^825*1250000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539400969 1250000000 8311542736781 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005971423/2500000000 : ℝ)^1081 ≤ (6067307039807/20000000000000 : ℝ)^825 := by
    have hnat : (1005971423 : ℕ)^1081*20000000000000^825 ≤ 6067307039807^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005971423 2500000000 6067307039807 20000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1156479169/2500000000 : ℝ)^1081 ≤ (36417293844371/100000000000000 : ℝ)^825 := by
    have hnat : (1156479169 : ℕ)^1081*100000000000000^825 ≤ 36417293844371^825*2500000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156479169 2500000000 36417293844371 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539400969/1250000000 : ℝ), (1005971423/2500000000 : ℝ), (1156479169/2500000000 : ℝ)] ![(8311542736781/25000000000000 : ℝ), (6067307039807/20000000000000 : ℝ), (36417293844371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539400969/1250000000 : ℝ)|^1081 ≤ (8311542736781/25000000000000 : ℝ)^825
        have hw : |(539400969/1250000000 : ℝ)|=(539400969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005971423/2500000000 : ℝ)|^1081 ≤ (6067307039807/20000000000000 : ℝ)^825
        have hw : |(1005971423/2500000000 : ℝ)|=(1005971423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1156479169/2500000000 : ℝ)|^1081 ≤ (36417293844371/100000000000000 : ℝ)^825
        have hw : |(1156479169/2500000000 : ℝ)|=(1156479169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_4 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008095767/5000000000 : ℝ)*x 0 + (5190564321/10000000000 : ℝ)*x 1 + (1094424207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008095767/5000000000 : ℝ)^1081 ≤ (3066661927277/25000000000000 : ℝ)^825 := by
    have hnat : (1008095767 : ℕ)^1081*25000000000000^825 ≤ 3066661927277^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008095767 5000000000 3066661927277 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190564321/10000000000 : ℝ)^1081 ≤ (42349159705237/100000000000000 : ℝ)^825 := by
    have hnat : (5190564321 : ℕ)^1081*100000000000000^825 ≤ 42349159705237^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190564321 10000000000 42349159705237 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094424207/2000000000 : ℝ)^1081 ≤ (22692096287481/50000000000000 : ℝ)^825 := by
    have hnat : (1094424207 : ℕ)^1081*50000000000000^825 ≤ 22692096287481^825*2000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094424207 2000000000 22692096287481 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008095767/5000000000 : ℝ), (5190564321/10000000000 : ℝ), (1094424207/2000000000 : ℝ)] ![(3066661927277/25000000000000 : ℝ), (42349159705237/100000000000000 : ℝ), (22692096287481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008095767/5000000000 : ℝ)|^1081 ≤ (3066661927277/25000000000000 : ℝ)^825
        have hw : |(-1008095767/5000000000 : ℝ)|=(1008095767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190564321/10000000000 : ℝ)|^1081 ≤ (42349159705237/100000000000000 : ℝ)^825
        have hw : |(5190564321/10000000000 : ℝ)|=(5190564321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094424207/2000000000 : ℝ)|^1081 ≤ (22692096287481/50000000000000 : ℝ)^825
        have hw : |(1094424207/2000000000 : ℝ)|=(1094424207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_5 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5290778159/10000000000 : ℝ)*x 0 + (-939975289/5000000000 : ℝ)*x 1 + (5472120981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290778159/10000000000 : ℝ)^1081 ≤ (21711850282239/50000000000000 : ℝ)^825 := by
    have hnat : (5290778159 : ℕ)^1081*50000000000000^825 ≤ 21711850282239^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290778159 10000000000 21711850282239 50000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939975289/5000000000 : ℝ)^1081 ≤ (1119210744143/10000000000000 : ℝ)^825 := by
    have hnat : (939975289 : ℕ)^1081*10000000000000^825 ≤ 1119210744143^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939975289 5000000000 1119210744143 10000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472120981/10000000000 : ℝ)^1081 ≤ (45384191988129/100000000000000 : ℝ)^825 := by
    have hnat : (5472120981 : ℕ)^1081*100000000000000^825 ≤ 45384191988129^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472120981 10000000000 45384191988129 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290778159/10000000000 : ℝ), (-939975289/5000000000 : ℝ), (5472120981/10000000000 : ℝ)] ![(21711850282239/50000000000000 : ℝ), (1119210744143/10000000000000 : ℝ), (45384191988129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290778159/10000000000 : ℝ)|^1081 ≤ (21711850282239/50000000000000 : ℝ)^825
        have hw : |(5290778159/10000000000 : ℝ)|=(5290778159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-939975289/5000000000 : ℝ)|^1081 ≤ (1119210744143/10000000000000 : ℝ)^825
        have hw : |(-939975289/5000000000 : ℝ)|=(939975289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472120981/10000000000 : ℝ)|^1081 ≤ (45384191988129/100000000000000 : ℝ)^825
        have hw : |(5472120981/10000000000 : ℝ)|=(5472120981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_6 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5290778119/10000000000 : ℝ)*x 0 + (2736060519/5000000000 : ℝ)*x 1 + (-1879950553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290778119/10000000000 : ℝ)^1081 ≤ (43423700134309/100000000000000 : ℝ)^825 := by
    have hnat : (5290778119 : ℕ)^1081*100000000000000^825 ≤ 43423700134309^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290778119 10000000000 43423700134309 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736060519/5000000000 : ℝ)^1081 ≤ (11346048151891/25000000000000 : ℝ)^825 := by
    have hnat : (2736060519 : ℕ)^1081*25000000000000^825 ≤ 11346048151891^825*5000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736060519 5000000000 11346048151891 25000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1879950553/10000000000 : ℝ)^1081 ≤ (11192107246411/100000000000000 : ℝ)^825 := by
    have hnat : (1879950553 : ℕ)^1081*100000000000000^825 ≤ 11192107246411^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879950553 10000000000 11192107246411 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290778119/10000000000 : ℝ), (2736060519/5000000000 : ℝ), (-1879950553/10000000000 : ℝ)] ![(43423700134309/100000000000000 : ℝ), (11346048151891/25000000000000 : ℝ), (11192107246411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290778119/10000000000 : ℝ)|^1081 ≤ (43423700134309/100000000000000 : ℝ)^825
        have hw : |(5290778119/10000000000 : ℝ)|=(5290778119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736060519/5000000000 : ℝ)|^1081 ≤ (11346048151891/25000000000000 : ℝ)^825
        have hw : |(2736060519/5000000000 : ℝ)|=(2736060519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1879950553/10000000000 : ℝ)|^1081 ≤ (11192107246411/100000000000000 : ℝ)^825
        have hw : |(-1879950553/10000000000 : ℝ)|=(1879950553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1364_s2_7 (p : ℝ) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4315334489/10000000000 : ℝ)*x 0 + (4622230621/10000000000 : ℝ)*x 1 + (4027604197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315334489/10000000000 : ℝ)^1081 ≤ (207796564867/625000000000 : ℝ)^825 := by
    have hnat : (4315334489 : ℕ)^1081*625000000000^825 ≤ 207796564867^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315334489 10000000000 207796564867 625000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4622230621/10000000000 : ℝ)^1081 ≤ (36379275804959/100000000000000 : ℝ)^825 := by
    have hnat : (4622230621 : ℕ)^1081*100000000000000^825 ≤ 36379275804959^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622230621 10000000000 36379275804959 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027604197/10000000000 : ℝ)^1081 ≤ (30373273807931/100000000000000 : ℝ)^825 := by
    have hnat : (4027604197 : ℕ)^1081*100000000000000^825 ≤ 30373273807931^825*10000000000^1081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027604197 10000000000 30373273807931 100000000000000 1081 825 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1081/256 : ℝ)) 1081 825 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315334489/10000000000 : ℝ), (4622230621/10000000000 : ℝ), (4027604197/10000000000 : ℝ)] ![(207796564867/625000000000 : ℝ), (36379275804959/100000000000000 : ℝ), (30373273807931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315334489/10000000000 : ℝ)|^1081 ≤ (207796564867/625000000000 : ℝ)^825
        have hw : |(4315334489/10000000000 : ℝ)|=(4315334489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4622230621/10000000000 : ℝ)|^1081 ≤ (36379275804959/100000000000000 : ℝ)^825
        have hw : |(4622230621/10000000000 : ℝ)|=(4622230621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027604197/10000000000 : ℝ)|^1081 ≤ (30373273807931/100000000000000 : ℝ)^825
        have hw : |(4027604197/10000000000 : ℝ)|=(4027604197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1364_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7091/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1249/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (801/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7091/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7091/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7091/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7091/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7091/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7091/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7091/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (703113020361649/50000000000000000000 : ℝ) := by
    have hpowers : (7091/100000 : ℝ)^4323 ≤ (703113020361649/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7091 : ℕ)^4323*50000000000000000000^1024 ≤ 703113020361649^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7091 100000 703113020361649 50000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7091/100000 : ℝ)) (X := (703113020361649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19299/100000 : ℝ) ^ (4323/1024 : ℝ) ≤ (48164472464118353/50000000000000000000 : ℝ) := by
    have hpowers : (19299/100000 : ℝ)^4323 ≤ (48164472464118353/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19299 : ℕ)^4323*50000000000000000000^1024 ≤ 48164472464118353^1024*100000^4323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19299 100000 48164472464118353 50000000000000000000 4323 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19299/100000 : ℝ)) (X := (48164472464118353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000703113020361649/25000000000000000000 : ℝ) ≤ (500003330927627/500000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (25000703113020361649/25000000000000000000 : ℝ)^1024 ≤ (500003330927627/500000000000000 : ℝ)^4323 := by
      have hnat : (25000703113020361649 : ℕ)^1024*500000000000000^4323 ≤ 500003330927627^4323*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000703113020361649 25000000000000000000 500003330927627 500000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500003330927627/500000000000000 : ℝ)) (X := (25000703113020361649/25000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25024433792742240001/25000000000000000000 : ℝ) ≤ (1000231421499333/1000000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (25024433792742240001/25000000000000000000 : ℝ)^1024 ≤ (1000231421499333/1000000000000000 : ℝ)^4323 := by
      have hnat : (25024433792742240001 : ℕ)^1024*1000000000000000^4323 ≤ 1000231421499333^4323*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25024433792742240001 25000000000000000000 1000231421499333 1000000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000231421499333/1000000000000000 : ℝ)) (X := (25024433792742240001/25000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25048164472464118353/25000000000000000000 : ℝ) ≤ (250114045285853/250000000000000 : ℝ) ^ (4323/1024 : ℝ) := by
    have hpowers : (25048164472464118353/25000000000000000000 : ℝ)^1024 ≤ (250114045285853/250000000000000 : ℝ)^4323 := by
      have hnat : (25048164472464118353 : ℕ)^1024*250000000000000^4323 ≤ 250114045285853^4323*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25048164472464118353 25000000000000000000 250114045285853 250000000000000 1024 4323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250114045285853/250000000000000 : ℝ)) (X := (25048164472464118353/25000000000000000000 : ℝ)) (by norm_num) 4323 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(703113020361649/50000000000000000000 : ℝ) ≤ ((871778127618329461/872000000000000000 : ℝ)+2*(224759644079/122080000000000 : ℝ)*(7091/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (871778127618329461/872000000000000000 : ℝ)+2*(224759644079/122080000000000 : ℝ)*(7091/100000 : ℝ)=(500003330927627/500000000000000 : ℝ) by norm_num, show 1+2*(703113020361649/50000000000000000000 : ℝ)=(25000703113020361649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48164472464118353/50000000000000000000 : ℝ)+(703113020361649/50000000000000000000 : ℝ) ≤ ((871778127618329461/872000000000000000 : ℝ)+(224759644079/122080000000000 : ℝ)*((19299/100000 : ℝ)+(7091/100000 : ℝ)))^(4323/1024 : ℝ) := by
    rw [show (871778127618329461/872000000000000000 : ℝ)+(224759644079/122080000000000 : ℝ)*((19299/100000 : ℝ)+(7091/100000 : ℝ))=(1000231421499333/1000000000000000 : ℝ) by norm_num, show 1+(48164472464118353/50000000000000000000 : ℝ)+(703113020361649/50000000000000000000 : ℝ)=(25024433792742240001/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48164472464118353/50000000000000000000 : ℝ) ≤ ((871778127618329461/872000000000000000 : ℝ)+2*(224759644079/122080000000000 : ℝ)*(19299/100000 : ℝ))^(4323/1024 : ℝ) := by
    rw [show (871778127618329461/872000000000000000 : ℝ)+2*(224759644079/122080000000000 : ℝ)*(19299/100000 : ℝ)=(250114045285853/250000000000000 : ℝ) by norm_num, show 1+2*(48164472464118353/50000000000000000000 : ℝ)=(25048164472464118353/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (871778127618329461/872000000000000000 : ℝ)*(X 1 0+X 2 0)+(224759644079/122080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (7091/100000 : ℝ)) (hi := (19299/100000 : ℝ)) (c := (871778127618329461/872000000000000000 : ℝ)) (alpha := (224759644079/122080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (871778127618329461/872000000000000000 : ℝ)*(X 0 1+X 2 1)+(224759644079/122080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (7091/100000 : ℝ)) (hi := (19299/100000 : ℝ)) (c := (871778127618329461/872000000000000000 : ℝ)) (alpha := (224759644079/122080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (871778127618329461/872000000000000000 : ℝ)*(X 0 2+X 1 2)+(224759644079/122080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4323/1024 : ℝ)) (lo := (7091/100000 : ℝ)) (hi := (19299/100000 : ℝ)) (c := (871778127618329461/872000000000000000 : ℝ)) (alpha := (224759644079/122080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1008065823/5000000000 : ℝ)*X 0 0+(547388201/1000000000 : ℝ)*X 0 1+(5188818721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1341106461/2500000000 : ℝ)*X 1 0+(-1081626431/5000000000 : ℝ)*X 1 1+(2594409513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5364425879/10000000000 : ℝ)*X 2 0+(5188818977/10000000000 : ℝ)*X 2 1+(-2163252879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((539400969/1250000000 : ℝ)*X 0 0+(1005971423/2500000000 : ℝ)*X 0 1+(1156479169/2500000000 : ℝ)*X 0 2+(539400969/1250000000 : ℝ)*X 1 0+(1005971423/2500000000 : ℝ)*X 1 1+(1156479169/2500000000 : ℝ)*X 1 2+(539400969/1250000000 : ℝ)*X 2 0+(1005971423/2500000000 : ℝ)*X 2 1+(1156479169/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1008095767/5000000000 : ℝ)*X 0 0+(5190564321/10000000000 : ℝ)*X 0 1+(1094424207/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290778159/10000000000 : ℝ)*X 1 0+(-939975289/5000000000 : ℝ)*X 1 1+(5472120981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290778119/10000000000 : ℝ)*X 2 0+(2736060519/5000000000 : ℝ)*X 2 1+(-1879950553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315334489/10000000000 : ℝ)*X 0 0+(4622230621/10000000000 : ℝ)*X 0 1+(4027604197/10000000000 : ℝ)*X 0 2+(4315334489/10000000000 : ℝ)*X 1 0+(4622230621/10000000000 : ℝ)*X 1 1+(4027604197/10000000000 : ℝ)*X 1 2+(4315334489/10000000000 : ℝ)*X 2 0+(4622230621/10000000000 : ℝ)*X 2 1+(4027604197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1364_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9709898162409216022355031/1220800000000000000000000000000 : ℝ) := by norm_num
    linear_combination (669991917/50000000000000 : ℝ)*(base19) + (654199741/50000000000000 : ℝ)*(base23) + (29221303/100000000000000 : ℝ)*(lower2) + (93671239/50000000000000 : ℝ)*(upper3) + (66962013/50000000000000 : ℝ)*(upper5) + (10338189629317/400000000000 : ℝ)*(major0) + (10338189629317/400000000000 : ℝ)*(major1) + (10338189629317/400000000000 : ℝ)*(major2) + (1754006667253389/50000000000000 : ℝ)*(sp0) + (350803191469231/10000000000000 : ℝ)*(sp1) + (3508031946276663/100000000000000 : ℝ)*(sp2) + (1661052293074881/100000000000000 : ℝ)*(sp3) + (19920169367/100000000000000 : ℝ)*(sp4) + (9001783549/100000000000000 : ℝ)*(sp7) + (1661061294858429/100000000000000 : ℝ)*(f.failure) + (219252078417259/6250000000000 : ℝ)*(f.sum) + (13843978112789/3052000000000000000000000000 : ℝ)*base66 + (41676180935181841/2441600000000000000000000000000 : ℝ)*base68 + (42052727719860241/2441600000000000000000000000000 : ℝ)*base70 + (17846612834493841/2441600000000000000000000000000 : ℝ)*base72 + (5555057276397/3052000000000000000000000000 : ℝ)*base74 + (61958516978583441/2441600000000000000000000000000 : ℝ)*base76 + (36448924292193041/2441600000000000000000000000000 : ℝ)*base78 + (52717133159604241/2441600000000000000000000000000 : ℝ)*base80 + (7147720803089/3052000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (52589921/10000000000000000000000 : ℝ)*base89 + (52589921/10000000000000000000000 : ℝ)*base91 + (52589921/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56891148823067366392947477/5450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418711707/20000000000000 : ℝ)*(base19) + (227970027/10000000000000 : ℝ)*(base23) + (239417171/100000000000000 : ℝ)*(upper3) + (89042561/100000000000000 : ℝ)*(lower4) + (11877787/6250000000000 : ℝ)*(upper5) + (327088038531527/12500000000000 : ℝ)*(major0) + (327088038531527/12500000000000 : ℝ)*(major1) + (327088038531527/12500000000000 : ℝ)*(major2) + (1520775187/6250000000000 : ℝ)*(sp1) + (6885821347/25000000000000 : ℝ)*(sp2) + (1775840036713709/50000000000000 : ℝ)*(sp4) + (355165364746589/10000000000000 : ℝ)*(sp5) + (22197814065261/625000000000 : ℝ)*(sp6) + (16817281951189/1000000000000 : ℝ)*(sp7) + (16817281951189/1000000000000 : ℝ)*(f.failure) + (1775840036713709/50000000000000 : ℝ)*(f.sum) + (390166370727/109000000000000000000000000 : ℝ)*base65 + (25357004747166947/10900000000000000000000000000000 : ℝ)*base67 + (167220822460366947/10900000000000000000000000000000 : ℝ)*base69 + (90908800545166947/10900000000000000000000000000000 : ℝ)*base71 + (71427296707/21800000000000000000000000 : ℝ)*base73 + (289777956313566947/10900000000000000000000000000000 : ℝ)*base75 + (106775017844566947/10900000000000000000000000000000 : ℝ)*base77 + (49151685366966947/10900000000000000000000000000000 : ℝ)*base79 + (766495947007/109000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1628839/100000000000000000000 : ℝ)*base90 + (1628839/100000000000000000000 : ℝ)*base92 + (1628839/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1364_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7091/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (801/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1364_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1364_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (801/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1364_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1364_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1364_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4323/1024 : ℝ) ≤ p) (hpb : p ≤ (1081/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155596149/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1249/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (801/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1364_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

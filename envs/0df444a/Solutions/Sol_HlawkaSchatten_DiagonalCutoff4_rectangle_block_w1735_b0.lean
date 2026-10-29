-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1735_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:07:32.256724+00:00
-- url     : https://prove2.me/submissions/0f1bab27-1d19-44c1-accb-810d8ded37fd

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
theorem support_rectangle_w1735_s0_0 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156593067/1250000000 : ℝ)*x 0 + (5679813003/10000000000 : ℝ)*x 1 + (2476517779/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156593067/1250000000 : ℝ)^5535 ≤ (7817658742589/100000000000000 : ℝ)^4511 := by
    have hnat : (156593067 : ℕ)^5535*100000000000000^4511 ≤ 7817658742589^4511*1250000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156593067 1250000000 7817658742589 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5679813003/10000000000 : ℝ)^5535 ≤ (24976852269481/50000000000000 : ℝ)^4511 := by
    have hnat : (5679813003 : ℕ)^5535*50000000000000^4511 ≤ 24976852269481^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5679813003 10000000000 24976852269481 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2476517779/5000000000 : ℝ)^5535 ≤ (21114318354813/50000000000000 : ℝ)^4511 := by
    have hnat : (2476517779 : ℕ)^5535*50000000000000^4511 ≤ 21114318354813^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476517779 5000000000 21114318354813 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156593067/1250000000 : ℝ), (5679813003/10000000000 : ℝ), (2476517779/5000000000 : ℝ)] ![(7817658742589/100000000000000 : ℝ), (24976852269481/50000000000000 : ℝ), (21114318354813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156593067/1250000000 : ℝ)|^5535 ≤ (7817658742589/100000000000000 : ℝ)^4511
        have hw : |(-156593067/1250000000 : ℝ)|=(156593067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5679813003/10000000000 : ℝ)|^5535 ≤ (24976852269481/50000000000000 : ℝ)^4511
        have hw : |(5679813003/10000000000 : ℝ)|=(5679813003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2476517779/5000000000 : ℝ)|^5535 ≤ (21114318354813/50000000000000 : ℝ)^4511
        have hw : |(2476517779/5000000000 : ℝ)|=(2476517779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_1 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390054281/10000000000 : ℝ)*x 0 + (-329144929/2000000000 : ℝ)*x 1 + (4953035743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390054281/10000000000 : ℝ)^5535 ≤ (2342257332271/5000000000000 : ℝ)^4511 := by
    have hnat : (5390054281 : ℕ)^5535*5000000000000^4511 ≤ 2342257332271^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390054281 10000000000 2342257332271 5000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329144929/2000000000 : ℝ)^5535 ≤ (546310734687/5000000000000 : ℝ)^4511 := by
    have hnat : (329144929 : ℕ)^5535*5000000000000^4511 ≤ 546310734687^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329144929 2000000000 546310734687 5000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4953035743/10000000000 : ℝ)^5535 ≤ (42228638644943/100000000000000 : ℝ)^4511 := by
    have hnat : (4953035743 : ℕ)^5535*100000000000000^4511 ≤ 42228638644943^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4953035743 10000000000 42228638644943 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390054281/10000000000 : ℝ), (-329144929/2000000000 : ℝ), (4953035743/10000000000 : ℝ)] ![(2342257332271/5000000000000 : ℝ), (546310734687/5000000000000 : ℝ), (42228638644943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390054281/10000000000 : ℝ)|^5535 ≤ (2342257332271/5000000000000 : ℝ)^4511
        have hw : |(5390054281/10000000000 : ℝ)|=(5390054281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329144929/2000000000 : ℝ)|^5535 ≤ (546310734687/5000000000000 : ℝ)^4511
        have hw : |(-329144929/2000000000 : ℝ)|=(329144929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4953035743/10000000000 : ℝ)|^5535 ≤ (42228638644943/100000000000000 : ℝ)^4511
        have hw : |(4953035743/10000000000 : ℝ)|=(4953035743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_2 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390053791/10000000000 : ℝ)*x 0 + (1238259033/2500000000 : ℝ)*x 1 + (-1645724787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390053791/10000000000 : ℝ)^5535 ≤ (46845141420107/100000000000000 : ℝ)^4511 := by
    have hnat : (5390053791 : ℕ)^5535*100000000000000^4511 ≤ 46845141420107^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390053791 10000000000 46845141420107 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238259033/2500000000 : ℝ)^5535 ≤ (2111432135717/5000000000000 : ℝ)^4511 := by
    have hnat : (1238259033 : ℕ)^5535*5000000000000^4511 ≤ 2111432135717^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238259033 2500000000 2111432135717 5000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1645724787/10000000000 : ℝ)^5535 ≤ (10926215850507/100000000000000 : ℝ)^4511 := by
    have hnat : (1645724787 : ℕ)^5535*100000000000000^4511 ≤ 10926215850507^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645724787 10000000000 10926215850507 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390053791/10000000000 : ℝ), (1238259033/2500000000 : ℝ), (-1645724787/10000000000 : ℝ)] ![(46845141420107/100000000000000 : ℝ), (2111432135717/5000000000000 : ℝ), (10926215850507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390053791/10000000000 : ℝ)|^5535 ≤ (46845141420107/100000000000000 : ℝ)^4511
        have hw : |(5390053791/10000000000 : ℝ)|=(5390053791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1238259033/2500000000 : ℝ)|^5535 ≤ (2111432135717/5000000000000 : ℝ)^4511
        have hw : |(1238259033/2500000000 : ℝ)|=(1238259033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1645724787/10000000000 : ℝ)|^5535 ≤ (10926215850507/100000000000000 : ℝ)^4511
        have hw : |(-1645724787/10000000000 : ℝ)|=(1645724787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_3 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4000202663/10000000000 : ℝ)*x 0 + (742602987/2500000000 : ℝ)*x 1 + (5212578577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4000202663/10000000000 : ℝ)^5535 ≤ (16245173241839/50000000000000 : ℝ)^4511 := by
    have hnat : (4000202663 : ℕ)^5535*50000000000000^4511 ≤ 16245173241839^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000202663 10000000000 16245173241839 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742602987/2500000000 : ℝ)^5535 ≤ (5637489269439/25000000000000 : ℝ)^4511 := by
    have hnat : (742602987 : ℕ)^5535*25000000000000^4511 ≤ 5637489269439^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742602987 2500000000 5637489269439 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212578577/10000000000 : ℝ)^5535 ≤ (8991939285927/20000000000000 : ℝ)^4511 := by
    have hnat : (5212578577 : ℕ)^5535*20000000000000^4511 ≤ 8991939285927^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212578577 10000000000 8991939285927 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4000202663/10000000000 : ℝ), (742602987/2500000000 : ℝ), (5212578577/10000000000 : ℝ)] ![(16245173241839/50000000000000 : ℝ), (5637489269439/25000000000000 : ℝ), (8991939285927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4000202663/10000000000 : ℝ)|^5535 ≤ (16245173241839/50000000000000 : ℝ)^4511
        have hw : |(4000202663/10000000000 : ℝ)|=(4000202663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742602987/2500000000 : ℝ)|^5535 ≤ (5637489269439/25000000000000 : ℝ)^4511
        have hw : |(742602987/2500000000 : ℝ)|=(742602987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212578577/10000000000 : ℝ)|^5535 ≤ (8991939285927/20000000000000 : ℝ)^4511
        have hw : |(5212578577/10000000000 : ℝ)|=(5212578577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_4 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-125447231/1000000000 : ℝ)*x 0 + (4971999111/10000000000 : ℝ)*x 1 + (5660187969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125447231/1000000000 : ℝ)^5535 ≤ (7830890388743/100000000000000 : ℝ)^4511 := by
    have hnat : (125447231 : ℕ)^5535*100000000000000^4511 ≤ 7830890388743^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125447231 1000000000 7830890388743 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4971999111/10000000000 : ℝ)^5535 ≤ (21213551927133/50000000000000 : ℝ)^4511 := by
    have hnat : (4971999111 : ℕ)^5535*50000000000000^4511 ≤ 21213551927133^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4971999111 10000000000 21213551927133 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660187969/10000000000 : ℝ)^5535 ≤ (1989680229937/4000000000000 : ℝ)^4511 := by
    have hnat : (5660187969 : ℕ)^5535*4000000000000^4511 ≤ 1989680229937^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660187969 10000000000 1989680229937 4000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125447231/1000000000 : ℝ), (4971999111/10000000000 : ℝ), (5660187969/10000000000 : ℝ)] ![(7830890388743/100000000000000 : ℝ), (21213551927133/50000000000000 : ℝ), (1989680229937/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125447231/1000000000 : ℝ)|^5535 ≤ (7830890388743/100000000000000 : ℝ)^4511
        have hw : |(-125447231/1000000000 : ℝ)|=(125447231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4971999111/10000000000 : ℝ)|^5535 ≤ (21213551927133/50000000000000 : ℝ)^4511
        have hw : |(4971999111/10000000000 : ℝ)|=(4971999111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660187969/10000000000 : ℝ)|^5535 ≤ (1989680229937/4000000000000 : ℝ)^4511
        have hw : |(5660187969/10000000000 : ℝ)|=(5660187969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_5 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194882247/10000000000 : ℝ)*x 0 + (-469286287/5000000000 : ℝ)*x 1 + (2830093711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194882247/10000000000 : ℝ)^5535 ≤ (44772485483447/100000000000000 : ℝ)^4511 := by
    have hnat : (5194882247 : ℕ)^5535*100000000000000^4511 ≤ 44772485483447^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194882247 10000000000 44772485483447 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469286287/5000000000 : ℝ)^5535 ≤ (5485514663541/100000000000000 : ℝ)^4511 := by
    have hnat : (469286287 : ℕ)^5535*100000000000000^4511 ≤ 5485514663541^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469286287 5000000000 5485514663541 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2830093711/5000000000 : ℝ)^5535 ≤ (49741999850157/100000000000000 : ℝ)^4511 := by
    have hnat : (2830093711 : ℕ)^5535*100000000000000^4511 ≤ 49741999850157^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830093711 5000000000 49741999850157 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194882247/10000000000 : ℝ), (-469286287/5000000000 : ℝ), (2830093711/5000000000 : ℝ)] ![(44772485483447/100000000000000 : ℝ), (5485514663541/100000000000000 : ℝ), (49741999850157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194882247/10000000000 : ℝ)|^5535 ≤ (44772485483447/100000000000000 : ℝ)^4511
        have hw : |(5194882247/10000000000 : ℝ)|=(5194882247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469286287/5000000000 : ℝ)|^5535 ≤ (5485514663541/100000000000000 : ℝ)^4511
        have hw : |(-469286287/5000000000 : ℝ)|=(469286287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2830093711/5000000000 : ℝ)|^5535 ≤ (49741999850157/100000000000000 : ℝ)^4511
        have hw : |(2830093711/5000000000 : ℝ)|=(2830093711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_6 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194881371/10000000000 : ℝ)*x 0 + (1415047073/2500000000 : ℝ)*x 1 + (-234643139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194881371/10000000000 : ℝ)^5535 ≤ (44772476219749/100000000000000 : ℝ)^4511 := by
    have hnat : (5194881371 : ℕ)^5535*100000000000000^4511 ≤ 44772476219749^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194881371 10000000000 44772476219749 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415047073/2500000000 : ℝ)^5535 ≤ (9948401846263/20000000000000 : ℝ)^4511 := by
    have hnat : (1415047073 : ℕ)^5535*20000000000000^4511 ≤ 9948401846263^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415047073 2500000000 9948401846263 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234643139/2500000000 : ℝ)^5535 ≤ (5485514534459/100000000000000 : ℝ)^4511 := by
    have hnat : (234643139 : ℕ)^5535*100000000000000^4511 ≤ 5485514534459^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234643139 2500000000 5485514534459 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194881371/10000000000 : ℝ), (1415047073/2500000000 : ℝ), (-234643139/2500000000 : ℝ)] ![(44772476219749/100000000000000 : ℝ), (9948401846263/20000000000000 : ℝ), (5485514534459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194881371/10000000000 : ℝ)|^5535 ≤ (44772476219749/100000000000000 : ℝ)^4511
        have hw : |(5194881371/10000000000 : ℝ)|=(5194881371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415047073/2500000000 : ℝ)|^5535 ≤ (9948401846263/20000000000000 : ℝ)^4511
        have hw : |(1415047073/2500000000 : ℝ)|=(1415047073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-234643139/2500000000 : ℝ)|^5535 ≤ (5485514534459/100000000000000 : ℝ)^4511
        have hw : |(-234643139/2500000000 : ℝ)|=(234643139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s0_7 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (400553101/1000000000 : ℝ)*x 0 + (1030814961/2000000000 : ℝ)*x 1 + (3030956017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400553101/1000000000 : ℝ)^5535 ≤ (1016983011201/3125000000000 : ℝ)^4511 := by
    have hnat : (400553101 : ℕ)^5535*3125000000000^4511 ≤ 1016983011201^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400553101 1000000000 1016983011201 3125000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030814961/2000000000 : ℝ)^5535 ≤ (44341332398301/100000000000000 : ℝ)^4511 := by
    have hnat : (1030814961 : ℕ)^5535*100000000000000^4511 ≤ 44341332398301^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030814961 2000000000 44341332398301 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3030956017/10000000000 : ℝ)^5535 ≤ (4623042246223/20000000000000 : ℝ)^4511 := by
    have hnat : (3030956017 : ℕ)^5535*20000000000000^4511 ≤ 4623042246223^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030956017 10000000000 4623042246223 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(400553101/1000000000 : ℝ), (1030814961/2000000000 : ℝ), (3030956017/10000000000 : ℝ)] ![(1016983011201/3125000000000 : ℝ), (44341332398301/100000000000000 : ℝ), (4623042246223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(400553101/1000000000 : ℝ)|^5535 ≤ (1016983011201/3125000000000 : ℝ)^4511
        have hw : |(400553101/1000000000 : ℝ)|=(400553101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030814961/2000000000 : ℝ)|^5535 ≤ (44341332398301/100000000000000 : ℝ)^4511
        have hw : |(1030814961/2000000000 : ℝ)|=(1030814961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3030956017/10000000000 : ℝ)|^5535 ≤ (4623042246223/20000000000000 : ℝ)^4511
        have hw : |(3030956017/10000000000 : ℝ)|=(3030956017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1735_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6059/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21711/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5519/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5519 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5519*1^1024 ≤ 0^1024*1^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5519/1024 : ℝ) ≤ (716544643898248437/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5519 ≤ (716544643898248437/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5519*100000000000000000000^1024 ≤ 716544643898248437^1024*5^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 716544643898248437 100000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (716544643898248437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5519 := by
      have hnat : (1 : ℕ)^1024*1^5519 ≤ 1^5519*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100716544643898248437/100000000000000000000 : ℝ) ≤ (10013256204073409/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (100716544643898248437/100000000000000000000 : ℝ)^1024 ≤ (10013256204073409/10000000000000000 : ℝ)^5519 := by
      have hnat : (100716544643898248437 : ℕ)^1024*10000000000000000^5519 ≤ 10013256204073409^5519*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100716544643898248437 100000000000000000000 10013256204073409 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013256204073409/10000000000000000 : ℝ)) (X := (100716544643898248437/100000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50716544643898248437/50000000000000000000 : ℝ) ≤ (5013256204073409/5000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (50716544643898248437/50000000000000000000 : ℝ)^1024 ≤ (5013256204073409/5000000000000000 : ℝ)^5519 := by
      have hnat : (50716544643898248437 : ℕ)^1024*5000000000000000^5519 ≤ 5013256204073409^5519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50716544643898248437 50000000000000000000 5013256204073409 5000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013256204073409/5000000000000000 : ℝ)) (X := (50716544643898248437/50000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13256204073409/4000000000000000 : ℝ)*(0 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13256204073409/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(716544643898248437/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13256204073409/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5519/1024 : ℝ) := by
    rw [show (1 : ℝ)+(13256204073409/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10013256204073409/10000000000000000 : ℝ) by norm_num, show 1+(716544643898248437/100000000000000000000 : ℝ)+(0 : ℝ)=(100716544643898248437/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(716544643898248437/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13256204073409/4000000000000000 : ℝ)*(2/5 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13256204073409/4000000000000000 : ℝ)*(2/5 : ℝ)=(5013256204073409/5000000000000000 : ℝ) by norm_num, show 1+2*(716544643898248437/100000000000000000000 : ℝ)=(50716544643898248437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13256204073409/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13256204073409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13256204073409/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13256204073409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13256204073409/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13256204073409/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-156593067/1250000000 : ℝ)*X 0 0+(5679813003/10000000000 : ℝ)*X 0 1+(2476517779/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5390054281/10000000000 : ℝ)*X 1 0+(-329144929/2000000000 : ℝ)*X 1 1+(4953035743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5390053791/10000000000 : ℝ)*X 2 0+(1238259033/2500000000 : ℝ)*X 2 1+(-1645724787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4000202663/10000000000 : ℝ)*X 0 0+(742602987/2500000000 : ℝ)*X 0 1+(5212578577/10000000000 : ℝ)*X 0 2+(4000202663/10000000000 : ℝ)*X 1 0+(742602987/2500000000 : ℝ)*X 1 1+(5212578577/10000000000 : ℝ)*X 1 2+(4000202663/10000000000 : ℝ)*X 2 0+(742602987/2500000000 : ℝ)*X 2 1+(5212578577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-125447231/1000000000 : ℝ)*X 0 0+(4971999111/10000000000 : ℝ)*X 0 1+(5660187969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194882247/10000000000 : ℝ)*X 1 0+(-469286287/5000000000 : ℝ)*X 1 1+(2830093711/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5194881371/10000000000 : ℝ)*X 2 0+(1415047073/2500000000 : ℝ)*X 2 1+(-234643139/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((400553101/1000000000 : ℝ)*X 0 0+(1030814961/2000000000 : ℝ)*X 0 1+(3030956017/10000000000 : ℝ)*X 0 2+(400553101/1000000000 : ℝ)*X 1 0+(1030814961/2000000000 : ℝ)*X 1 1+(3030956017/10000000000 : ℝ)*X 1 2+(400553101/1000000000 : ℝ)*X 2 0+(1030814961/2000000000 : ℝ)*X 2 1+(3030956017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (272034430480722296597481/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26502303/100000000000000 : ℝ)*(base1) + (65670803/10000000000000 : ℝ)*(base19) + (66452947/12500000000000 : ℝ)*(base23) + (148803087/100000000000000 : ℝ)*(upper3) + (16480211/25000000000000 : ℝ)*(upper5) + (455485580401597/50000000000000 : ℝ)*(major0) + (455485580401597/50000000000000 : ℝ)*(major1) + (455485580401597/50000000000000 : ℝ)*(major2) + (275188130010909/20000000000000 : ℝ)*(sp0) + (137594272386481/10000000000000 : ℝ)*(sp1) + (85996428059329/6250000000000 : ℝ)*(sp2) + (445997883020999/100000000000000 : ℝ)*(sp3) + (2757020599/100000000000000 : ℝ)*(sp4) + (470416049/50000000000000 : ℝ)*(sp7) + (2229994251777/500000000000 : ℝ)*(f.failure) + (34398584514321/2500000000000 : ℝ)*(f.sum) + (40395461865827/100000000000000000000000000000 : ℝ)*base66 + (635024875634173/200000000000000000000000000000 : ℝ)*base67 + (210841837165827/200000000000000000000000000000 : ℝ)*base70 + (1426163303434173/200000000000000000000000000000 : ℝ)*base71 + (79095039634173/100000000000000000000000000000 : ℝ)*base73 + (1337074305034173/200000000000000000000000000000 : ℝ)*base75 + (1269341660634173/200000000000000000000000000000 : ℝ)*base77 + (987050730834173/200000000000000000000000000000 : ℝ)*base79 + (205087043265827/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2491/1000000000000000000 : ℝ)*base89 + (2491/1000000000000000000 : ℝ)*base91 + (2491/1000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (655105670710569853938033/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13496721/800000000000 : ℝ)*(base19) + (784105837/50000000000000 : ℝ)*(base23) + (15787049/25000000000000 : ℝ)*(upper2) + (49150267/20000000000000 : ℝ)*(upper3) + (17831877/6250000000000 : ℝ)*(upper5) + (962047132021207/100000000000000 : ℝ)*(major0) + (962047132021207/100000000000000 : ℝ)*(major1) + (962047132021207/100000000000000 : ℝ)*(major2) + (2877248241/50000000000000 : ℝ)*(sp1) + (5876752223/100000000000000 : ℝ)*(sp2) + (1453089107942497/100000000000000 : ℝ)*(sp4) + (145308166635589/10000000000000 : ℝ)*(sp5) + (7265408314893/500000000000 : ℝ)*(sp6) + (235502468865677/50000000000000 : ℝ)*(sp7) + (235502468865677/50000000000000 : ℝ)*(f.failure) + (1453089107942497/100000000000000 : ℝ)*(f.sum) + (182726878784663/200000000000000000000000000000 : ℝ)*base65 + (3117010317984663/400000000000000000000000000000 : ℝ)*base67 + (1530602528384663/400000000000000000000000000000 : ℝ)*base69 + (792348047984663/400000000000000000000000000000 : ℝ)*base71 + (1242357528784663/200000000000000000000000000000 : ℝ)*base73 + (88941283184663/400000000000000000000000000000 : ℝ)*base75 + (827522559584663/400000000000000000000000000000 : ℝ)*base77 + (2007509330384663/400000000000000000000000000000 : ℝ)*base79 + (547811989384663/200000000000000000000000000000 : ℝ)*base81 + (603809/100000000000000000000 : ℝ)*base90 + (603809/100000000000000000000 : ℝ)*base92 + (603809/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1735_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6059/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1735_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1735_s1_0 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1309222623/10000000000 : ℝ)*x 0 + (2762286869/5000000000 : ℝ)*x 1 + (5070811243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309222623/10000000000 : ℝ)^5535 ≤ (825229944937/10000000000000 : ℝ)^4511 := by
    have hnat : (1309222623 : ℕ)^5535*10000000000000^4511 ≤ 825229944937^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309222623 10000000000 825229944937 10000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762286869/5000000000 : ℝ)^5535 ≤ (48283686901221/100000000000000 : ℝ)^4511 := by
    have hnat : (2762286869 : ℕ)^5535*100000000000000^4511 ≤ 48283686901221^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762286869 5000000000 48283686901221 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5070811243/10000000000 : ℝ)^5535 ≤ (5433001705507/12500000000000 : ℝ)^4511 := by
    have hnat : (5070811243 : ℕ)^5535*12500000000000^4511 ≤ 5433001705507^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5070811243 10000000000 5433001705507 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1309222623/10000000000 : ℝ), (2762286869/5000000000 : ℝ), (5070811243/10000000000 : ℝ)] ![(825229944937/10000000000000 : ℝ), (48283686901221/100000000000000 : ℝ), (5433001705507/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1309222623/10000000000 : ℝ)|^5535 ≤ (825229944937/10000000000000 : ℝ)^4511
        have hw : |(-1309222623/10000000000 : ℝ)|=(1309222623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2762286869/5000000000 : ℝ)|^5535 ≤ (48283686901221/100000000000000 : ℝ)^4511
        have hw : |(2762286869/5000000000 : ℝ)|=(2762286869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5070811243/10000000000 : ℝ)|^5535 ≤ (5433001705507/12500000000000 : ℝ)^4511
        have hw : |(5070811243/10000000000 : ℝ)|=(5070811243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_1 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337162653/2500000000 : ℝ)*x 0 + (-1547552743/10000000000 : ℝ)*x 1 + (507081087/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337162653/2500000000 : ℝ)^5535 ≤ (2900250472927/6250000000000 : ℝ)^4511 := by
    have hnat : (1337162653 : ℕ)^5535*6250000000000^4511 ≤ 2900250472927^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337162653 2500000000 2900250472927 6250000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1547552743/10000000000 : ℝ)^5535 ≤ (10131982703659/100000000000000 : ℝ)^4511 := by
    have hnat : (1547552743 : ℕ)^5535*100000000000000^4511 ≤ 10131982703659^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1547552743 10000000000 10131982703659 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507081087/1000000000 : ℝ)^5535 ≤ (43464009721167/100000000000000 : ℝ)^4511 := by
    have hnat : (507081087 : ℕ)^5535*100000000000000^4511 ≤ 43464009721167^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507081087 1000000000 43464009721167 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337162653/2500000000 : ℝ), (-1547552743/10000000000 : ℝ), (507081087/1000000000 : ℝ)] ![(2900250472927/6250000000000 : ℝ), (10131982703659/100000000000000 : ℝ), (43464009721167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337162653/2500000000 : ℝ)|^5535 ≤ (2900250472927/6250000000000 : ℝ)^4511
        have hw : |(1337162653/2500000000 : ℝ)|=(1337162653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1547552743/10000000000 : ℝ)|^5535 ≤ (10131982703659/100000000000000 : ℝ)^4511
        have hw : |(-1547552743/10000000000 : ℝ)|=(1547552743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507081087/1000000000 : ℝ)|^5535 ≤ (43464009721167/100000000000000 : ℝ)^4511
        have hw : |(507081087/1000000000 : ℝ)|=(507081087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_2 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337162499/2500000000 : ℝ)*x 0 + (2535405759/5000000000 : ℝ)*x 1 + (-154755271/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337162499/2500000000 : ℝ)^5535 ≤ (11601000252339/25000000000000 : ℝ)^4511 := by
    have hnat : (1337162499 : ℕ)^5535*25000000000000^4511 ≤ 11601000252339^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337162499 2500000000 11601000252339 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2535405759/5000000000 : ℝ)^5535 ≤ (21732008268133/50000000000000 : ℝ)^4511 := by
    have hnat : (2535405759 : ℕ)^5535*50000000000000^4511 ≤ 21732008268133^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535405759 5000000000 21732008268133 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (154755271/1000000000 : ℝ)^5535 ≤ (63324890241/625000000000 : ℝ)^4511 := by
    have hnat : (154755271 : ℕ)^5535*625000000000^4511 ≤ 63324890241^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154755271 1000000000 63324890241 625000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337162499/2500000000 : ℝ), (2535405759/5000000000 : ℝ), (-154755271/1000000000 : ℝ)] ![(11601000252339/25000000000000 : ℝ), (21732008268133/50000000000000 : ℝ), (63324890241/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337162499/2500000000 : ℝ)|^5535 ≤ (11601000252339/25000000000000 : ℝ)^4511
        have hw : |(1337162499/2500000000 : ℝ)|=(1337162499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2535405759/5000000000 : ℝ)|^5535 ≤ (21732008268133/50000000000000 : ℝ)^4511
        have hw : |(2535405759/5000000000 : ℝ)|=(2535405759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-154755271/1000000000 : ℝ)|^5535 ≤ (63324890241/625000000000 : ℝ)^4511
        have hw : |(-154755271/1000000000 : ℝ)|=(154755271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_3 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4051929147/10000000000 : ℝ)*x 0 + (677460729/2000000000 : ℝ)*x 1 + (4787197277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4051929147/10000000000 : ℝ)^5535 ≤ (4125825283409/12500000000000 : ℝ)^4511 := by
    have hnat : (4051929147 : ℕ)^5535*12500000000000^4511 ≤ 4125825283409^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4051929147 10000000000 4125825283409 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677460729/2000000000 : ℝ)^5535 ≤ (1059718937809/4000000000000 : ℝ)^4511 := by
    have hnat : (677460729 : ℕ)^5535*4000000000000^4511 ≤ 1059718937809^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677460729 2000000000 1059718937809 4000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4787197277/10000000000 : ℝ)^5535 ≤ (40500424271723/100000000000000 : ℝ)^4511 := by
    have hnat : (4787197277 : ℕ)^5535*100000000000000^4511 ≤ 40500424271723^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787197277 10000000000 40500424271723 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4051929147/10000000000 : ℝ), (677460729/2000000000 : ℝ), (4787197277/10000000000 : ℝ)] ![(4125825283409/12500000000000 : ℝ), (1059718937809/4000000000000 : ℝ), (40500424271723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4051929147/10000000000 : ℝ)|^5535 ≤ (4125825283409/12500000000000 : ℝ)^4511
        have hw : |(4051929147/10000000000 : ℝ)|=(4051929147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677460729/2000000000 : ℝ)|^5535 ≤ (1059718937809/4000000000000 : ℝ)^4511
        have hw : |(677460729/2000000000 : ℝ)|=(677460729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4787197277/10000000000 : ℝ)|^5535 ≤ (40500424271723/100000000000000 : ℝ)^4511
        have hw : |(4787197277/10000000000 : ℝ)|=(4787197277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_4 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130963969/1000000000 : ℝ)*x 0 + (1015639397/2000000000 : ℝ)*x 1 + (5517027127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130963969/1000000000 : ℝ)^5535 ≤ (8255525177823/100000000000000 : ℝ)^4511 := by
    have hnat : (130963969 : ℕ)^5535*100000000000000^4511 ≤ 8255525177823^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130963969 1000000000 8255525177823 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015639397/2000000000 : ℝ)^5535 ≤ (21770851639203/50000000000000 : ℝ)^4511 := by
    have hnat : (1015639397 : ℕ)^5535*50000000000000^4511 ≤ 21770851639203^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015639397 2000000000 21770851639203 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5517027127/10000000000 : ℝ)^5535 ≤ (9640554305293/20000000000000 : ℝ)^4511 := by
    have hnat : (5517027127 : ℕ)^5535*20000000000000^4511 ≤ 9640554305293^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517027127 10000000000 9640554305293 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130963969/1000000000 : ℝ), (1015639397/2000000000 : ℝ), (5517027127/10000000000 : ℝ)] ![(8255525177823/100000000000000 : ℝ), (21770851639203/50000000000000 : ℝ), (9640554305293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130963969/1000000000 : ℝ)|^5535 ≤ (8255525177823/100000000000000 : ℝ)^4511
        have hw : |(-130963969/1000000000 : ℝ)|=(130963969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015639397/2000000000 : ℝ)|^5535 ≤ (21770851639203/50000000000000 : ℝ)^4511
        have hw : |(1015639397/2000000000 : ℝ)|=(1015639397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5517027127/10000000000 : ℝ)|^5535 ≤ (9640554305293/20000000000000 : ℝ)^4511
        have hw : |(5517027127/10000000000 : ℝ)|=(5517027127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_5 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613976707/5000000000 : ℝ)*x 0 + (-550668839/5000000000 : ℝ)*x 1 + (1103405439/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613976707/5000000000 : ℝ)^5535 ≤ (45122465292963/100000000000000 : ℝ)^4511 := by
    have hnat : (2613976707 : ℕ)^5535*100000000000000^4511 ≤ 45122465292963^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613976707 5000000000 45122465292963 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550668839/5000000000 : ℝ)^5535 ≤ (6674762431479/100000000000000 : ℝ)^4511 := by
    have hnat : (550668839 : ℕ)^5535*100000000000000^4511 ≤ 6674762431479^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550668839 5000000000 6674762431479 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103405439/2000000000 : ℝ)^5535 ≤ (48202772255453/100000000000000 : ℝ)^4511 := by
    have hnat : (1103405439 : ℕ)^5535*100000000000000^4511 ≤ 48202772255453^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103405439 2000000000 48202772255453 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613976707/5000000000 : ℝ), (-550668839/5000000000 : ℝ), (1103405439/2000000000 : ℝ)] ![(45122465292963/100000000000000 : ℝ), (6674762431479/100000000000000 : ℝ), (48202772255453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613976707/5000000000 : ℝ)|^5535 ≤ (45122465292963/100000000000000 : ℝ)^4511
        have hw : |(2613976707/5000000000 : ℝ)|=(2613976707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550668839/5000000000 : ℝ)|^5535 ≤ (6674762431479/100000000000000 : ℝ)^4511
        have hw : |(-550668839/5000000000 : ℝ)|=(550668839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103405439/2000000000 : ℝ)|^5535 ≤ (48202772255453/100000000000000 : ℝ)^4511
        have hw : |(1103405439/2000000000 : ℝ)|=(1103405439/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_6 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613976811/5000000000 : ℝ)*x 0 + (137925681/250000000 : ℝ)*x 1 + (-550668659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613976811/5000000000 : ℝ)^5535 ≤ (45122467495733/100000000000000 : ℝ)^4511 := by
    have hnat : (2613976811 : ℕ)^5535*100000000000000^4511 ≤ 45122467495733^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613976811 5000000000 45122467495733 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137925681/250000000 : ℝ)^5535 ≤ (3012673296117/6250000000000 : ℝ)^4511 := by
    have hnat : (137925681 : ℕ)^5535*6250000000000^4511 ≤ 3012673296117^4511*250000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137925681 250000000 3012673296117 6250000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550668659/5000000000 : ℝ)^5535 ≤ (834344969299/12500000000000 : ℝ)^4511 := by
    have hnat : (550668659 : ℕ)^5535*12500000000000^4511 ≤ 834344969299^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550668659 5000000000 834344969299 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613976811/5000000000 : ℝ), (137925681/250000000 : ℝ), (-550668659/5000000000 : ℝ)] ![(45122467495733/100000000000000 : ℝ), (3012673296117/6250000000000 : ℝ), (834344969299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613976811/5000000000 : ℝ)|^5535 ≤ (45122467495733/100000000000000 : ℝ)^4511
        have hw : |(2613976811/5000000000 : ℝ)|=(2613976811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137925681/250000000 : ℝ)|^5535 ≤ (3012673296117/6250000000000 : ℝ)^4511
        have hw : |(137925681/250000000 : ℝ)|=(137925681/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550668659/5000000000 : ℝ)|^5535 ≤ (834344969299/12500000000000 : ℝ)^4511
        have hw : |(-550668659/5000000000 : ℝ)|=(550668659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s1_7 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (126662873/312500000 : ℝ)*x 0 + (2382205343/5000000000 : ℝ)*x 1 + (682116813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126662873/312500000 : ℝ)^5535 ≤ (6603884846569/20000000000000 : ℝ)^4511 := by
    have hnat : (126662873 : ℕ)^5535*20000000000000^4511 ≤ 6603884846569^4511*312500000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126662873 312500000 6603884846569 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2382205343/5000000000 : ℝ)^5535 ≤ (20132006705671/50000000000000 : ℝ)^4511 := by
    have hnat : (2382205343 : ℕ)^5535*50000000000000^4511 ≤ 20132006705671^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382205343 5000000000 20132006705671 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682116813/2000000000 : ℝ)^5535 ≤ (1335828117137/5000000000000 : ℝ)^4511 := by
    have hnat : (682116813 : ℕ)^5535*5000000000000^4511 ≤ 1335828117137^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682116813 2000000000 1335828117137 5000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(126662873/312500000 : ℝ), (2382205343/5000000000 : ℝ), (682116813/2000000000 : ℝ)] ![(6603884846569/20000000000000 : ℝ), (20132006705671/50000000000000 : ℝ), (1335828117137/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(126662873/312500000 : ℝ)|^5535 ≤ (6603884846569/20000000000000 : ℝ)^4511
        have hw : |(126662873/312500000 : ℝ)|=(126662873/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2382205343/5000000000 : ℝ)|^5535 ≤ (20132006705671/50000000000000 : ℝ)^4511
        have hw : |(2382205343/5000000000 : ℝ)|=(2382205343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682116813/2000000000 : ℝ)|^5535 ≤ (1335828117137/5000000000000 : ℝ)^4511
        have hw : |(682116813/2000000000 : ℝ)|=(682116813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1735_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4353/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18407/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6059/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6059/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6059/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6059/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6059/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6059/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6059/100000 : ℝ) ^ (5519/1024 : ℝ) ≤ (3423569976637/12500000000000000000 : ℝ) := by
    have hpowers : (6059/100000 : ℝ)^5519 ≤ (3423569976637/12500000000000000000 : ℝ)^1024 := by
      have hnat : (6059 : ℕ)^5519*12500000000000000000^1024 ≤ 3423569976637^1024*100000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6059 100000 3423569976637 12500000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6059/100000 : ℝ)) (X := (3423569976637/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21711/100000 : ℝ) ^ (5519/1024 : ℝ) ≤ (13301709907742941/50000000000000000000 : ℝ) := by
    have hpowers : (21711/100000 : ℝ)^5519 ≤ (13301709907742941/50000000000000000000 : ℝ)^1024 := by
      have hnat : (21711 : ℕ)^5519*50000000000000000000^1024 ≤ 13301709907742941^1024*100000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21711 100000 13301709907742941 50000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21711/100000 : ℝ)) (X := (13301709907742941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250003423569976637/6250000000000000000 : ℝ) ≤ (2500000254084789/2500000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (6250003423569976637/6250000000000000000 : ℝ)^1024 ≤ (2500000254084789/2500000000000000 : ℝ)^5519 := by
      have hnat : (6250003423569976637 : ℕ)^1024*2500000000000000^5519 ≤ 2500000254084789^5519*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250003423569976637 6250000000000000000 2500000254084789 2500000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000254084789/2500000000000000 : ℝ)) (X := (6250003423569976637/6250000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013315404187649489/50000000000000000000 : ℝ) ≤ (10000494056728881/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (50013315404187649489/50000000000000000000 : ℝ)^1024 ≤ (10000494056728881/10000000000000000 : ℝ)^5519 := by
      have hnat : (50013315404187649489 : ℕ)^1024*10000000000000000^5519 ≤ 10000494056728881^5519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013315404187649489 50000000000000000000 10000494056728881 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000494056728881/10000000000000000 : ℝ)) (X := (50013315404187649489/50000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013301709907742941/25000000000000000000 : ℝ) ≤ (5000493548559303/5000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (25013301709907742941/25000000000000000000 : ℝ)^1024 ≤ (5000493548559303/5000000000000000 : ℝ)^5519 := by
      have hnat : (25013301709907742941 : ℕ)^1024*5000000000000000^5519 ≤ 5000493548559303^5519*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013301709907742941 25000000000000000000 5000493548559303 5000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000493548559303/5000000000000000 : ℝ)) (X := (25013301709907742941/25000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3423569976637/12500000000000000000 : ℝ) ≤ ((139994670164845959/140000000000000000 : ℝ)+2*(35280171/112000000000 : ℝ)*(6059/100000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (139994670164845959/140000000000000000 : ℝ)+2*(35280171/112000000000 : ℝ)*(6059/100000 : ℝ)=(2500000254084789/2500000000000000 : ℝ) by norm_num, show 1+2*(3423569976637/12500000000000000000 : ℝ)=(6250003423569976637/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13301709907742941/50000000000000000000 : ℝ)+(3423569976637/12500000000000000000 : ℝ) ≤ ((139994670164845959/140000000000000000 : ℝ)+(35280171/112000000000 : ℝ)*((21711/100000 : ℝ)+(6059/100000 : ℝ)))^(5519/1024 : ℝ) := by
    rw [show (139994670164845959/140000000000000000 : ℝ)+(35280171/112000000000 : ℝ)*((21711/100000 : ℝ)+(6059/100000 : ℝ))=(10000494056728881/10000000000000000 : ℝ) by norm_num, show 1+(13301709907742941/50000000000000000000 : ℝ)+(3423569976637/12500000000000000000 : ℝ)=(50013315404187649489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13301709907742941/50000000000000000000 : ℝ) ≤ ((139994670164845959/140000000000000000 : ℝ)+2*(35280171/112000000000 : ℝ)*(21711/100000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (139994670164845959/140000000000000000 : ℝ)+2*(35280171/112000000000 : ℝ)*(21711/100000 : ℝ)=(5000493548559303/5000000000000000 : ℝ) by norm_num, show 1+2*(13301709907742941/50000000000000000000 : ℝ)=(25013301709907742941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139994670164845959/140000000000000000 : ℝ)*(X 1 0+X 2 0)+(35280171/112000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (6059/100000 : ℝ)) (hi := (21711/100000 : ℝ)) (c := (139994670164845959/140000000000000000 : ℝ)) (alpha := (35280171/112000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139994670164845959/140000000000000000 : ℝ)*(X 0 1+X 2 1)+(35280171/112000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (6059/100000 : ℝ)) (hi := (21711/100000 : ℝ)) (c := (139994670164845959/140000000000000000 : ℝ)) (alpha := (35280171/112000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139994670164845959/140000000000000000 : ℝ)*(X 0 2+X 1 2)+(35280171/112000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (6059/100000 : ℝ)) (hi := (21711/100000 : ℝ)) (c := (139994670164845959/140000000000000000 : ℝ)) (alpha := (35280171/112000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1309222623/10000000000 : ℝ)*X 0 0+(2762286869/5000000000 : ℝ)*X 0 1+(5070811243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337162653/2500000000 : ℝ)*X 1 0+(-1547552743/10000000000 : ℝ)*X 1 1+(507081087/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337162499/2500000000 : ℝ)*X 2 0+(2535405759/5000000000 : ℝ)*X 2 1+(-154755271/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4051929147/10000000000 : ℝ)*X 0 0+(677460729/2000000000 : ℝ)*X 0 1+(4787197277/10000000000 : ℝ)*X 0 2+(4051929147/10000000000 : ℝ)*X 1 0+(677460729/2000000000 : ℝ)*X 1 1+(4787197277/10000000000 : ℝ)*X 1 2+(4051929147/10000000000 : ℝ)*X 2 0+(677460729/2000000000 : ℝ)*X 2 1+(4787197277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-130963969/1000000000 : ℝ)*X 0 0+(1015639397/2000000000 : ℝ)*X 0 1+(5517027127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2613976707/5000000000 : ℝ)*X 1 0+(-550668839/5000000000 : ℝ)*X 1 1+(1103405439/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2613976811/5000000000 : ℝ)*X 2 0+(137925681/250000000 : ℝ)*X 2 1+(-550668659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((126662873/312500000 : ℝ)*X 0 0+(2382205343/5000000000 : ℝ)*X 0 1+(682116813/2000000000 : ℝ)*X 0 2+(126662873/312500000 : ℝ)*X 1 0+(2382205343/5000000000 : ℝ)*X 1 1+(682116813/2000000000 : ℝ)*X 1 2+(126662873/312500000 : ℝ)*X 2 0+(2382205343/5000000000 : ℝ)*X 2 1+(682116813/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31127743865861849407061163/3500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218694227/12500000000000 : ℝ)*(base19) + (167608639/12500000000000 : ℝ)*(base23) + (16567179/20000000000000 : ℝ)*(lower2) + (130661913/50000000000000 : ℝ)*(upper3) + (12133557/10000000000000 : ℝ)*(upper5) + (729542106860481/50000000000000 : ℝ)*(major0) + (729542106860481/50000000000000 : ℝ)*(major1) + (729542106860481/50000000000000 : ℝ)*(major2) + (137738068817511/6250000000000 : ℝ)*(sp0) + (2203818979571083/100000000000000 : ℝ)*(sp1) + (2203819388255787/100000000000000 : ℝ)*(sp2) + (714343327719251/100000000000000 : ℝ)*(sp3) + (11628044723/100000000000000 : ℝ)*(sp4) + (4074143067/100000000000000 : ℝ)*(sp7) + (357173700931159/50000000000000 : ℝ)*(f.failure) + (2203820729124899/100000000000000 : ℝ)*(f.sum) + (40957003981/14000000000000000000000000 : ℝ)*base65 + (19553739016603721/7000000000000000000000000000000 : ℝ)*base68 + (53020408986396279/7000000000000000000000000000000 : ℝ)*base69 + (5743771551603721/7000000000000000000000000000000 : ℝ)*base72 + (27536233377/14000000000000000000000000 : ℝ)*base74 + (18379840639396279/7000000000000000000000000000000 : ℝ)*base75 + (1262710056396279/7000000000000000000000000000000 : ℝ)*base77 + (718424622396279/7000000000000000000000000000000 : ℝ)*base79 + (87171073687/14000000000000000000000000 : ℝ)*base81 + (198803/100000000000000000000 : ℝ)*base90 + (198803/100000000000000000000 : ℝ)*base92 + (198803/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29008721995614062784709899/3500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1254560993/100000000000000 : ℝ)*(base19) + (18182433/1000000000000 : ℝ)*(base23) + (206209721/100000000000000 : ℝ)*(upper2) + (288184163/100000000000000 : ℝ)*(upper3) + (362949353/100000000000000 : ℝ)*(upper5) + (1508715948244887/100000000000000 : ℝ)*(major0) + (1508715948244887/100000000000000 : ℝ)*(major1) + (1508715948244887/100000000000000 : ℝ)*(major2) + (3246495489/50000000000000 : ℝ)*(sp1) + (9896788671/100000000000000 : ℝ)*(sp2) + (1139392604620027/50000000000000 : ℝ)*(sp4) + (2278777461688083/100000000000000 : ℝ)*(sp5) + (1139386747104041/50000000000000 : ℝ)*(sp6) + (184661602744043/25000000000000 : ℝ)*(sp7) + (184661602744043/25000000000000 : ℝ)*(f.failure) + (1139392604620027/50000000000000 : ℝ)*(f.sum) + (10747502111/28000000000000000000000000 : ℝ)*base66 + (173763999187388367/14000000000000000000000000000000 : ℝ)*base68 + (27657740828611633/14000000000000000000000000000000 : ℝ)*base69 + (51898503099388367/14000000000000000000000000000000 : ℝ)*base72 + (114142663407/28000000000000000000000000 : ℝ)*base74 + (50739503789388367/14000000000000000000000000000000 : ℝ)*base76 + (23302445007388367/14000000000000000000000000000000 : ℝ)*base78 + (11039606139388367/14000000000000000000000000000000 : ℝ)*base80 + (119595270953/28000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (89431/50000000000000000000 : ℝ)*base90 + (89431/50000000000000000000 : ℝ)*base92 + (89431/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1735_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4353/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18407/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1735_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1735_s2_0 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1311194093/10000000000 : ℝ)*x 0 + (275915071/500000000 : ℝ)*x 1 + (2537877697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311194093/10000000000 : ℝ)^5535 ≤ (8267549477321/100000000000000 : ℝ)^4511 := by
    have hnat : (1311194093 : ℕ)^5535*100000000000000^4511 ≤ 8267549477321^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311194093 10000000000 8267549477321 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275915071/500000000 : ℝ)^5535 ≤ (2410821641861/5000000000000 : ℝ)^4511 := by
    have hnat : (275915071 : ℕ)^5535*5000000000000^4511 ≤ 2410821641861^4511*500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275915071 500000000 2410821641861 5000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2537877697/5000000000 : ℝ)^5535 ≤ (8703203533721/20000000000000 : ℝ)^4511 := by
    have hnat : (2537877697 : ℕ)^5535*20000000000000^4511 ≤ 8703203533721^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537877697 5000000000 8703203533721 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1311194093/10000000000 : ℝ), (275915071/500000000 : ℝ), (2537877697/5000000000 : ℝ)] ![(8267549477321/100000000000000 : ℝ), (2410821641861/5000000000000 : ℝ), (8703203533721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1311194093/10000000000 : ℝ)|^5535 ≤ (8267549477321/100000000000000 : ℝ)^4511
        have hw : |(-1311194093/10000000000 : ℝ)|=(1311194093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275915071/500000000 : ℝ)|^5535 ≤ (2410821641861/5000000000000 : ℝ)^4511
        have hw : |(275915071/500000000 : ℝ)|=(275915071/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2537877697/5000000000 : ℝ)|^5535 ≤ (8703203533721/20000000000000 : ℝ)^4511
        have hw : |(2537877697/5000000000 : ℝ)|=(2537877697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_1 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346931453/10000000000 : ℝ)*x 0 + (-308671089/2000000000 : ℝ)*x 1 + (1015151079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346931453/10000000000 : ℝ)^5535 ≤ (1855428293963/4000000000000 : ℝ)^4511 := by
    have hnat : (5346931453 : ℕ)^5535*4000000000000^4511 ≤ 1855428293963^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346931453 10000000000 1855428293963 4000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308671089/2000000000 : ℝ)^5535 ≤ (10098274952701/100000000000000 : ℝ)^4511 := by
    have hnat : (308671089 : ℕ)^5535*100000000000000^4511 ≤ 10098274952701^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308671089 2000000000 10098274952701 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015151079/2000000000 : ℝ)^5535 ≤ (10879004419781/25000000000000 : ℝ)^4511 := by
    have hnat : (1015151079 : ℕ)^5535*25000000000000^4511 ≤ 10879004419781^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015151079 2000000000 10879004419781 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346931453/10000000000 : ℝ), (-308671089/2000000000 : ℝ), (1015151079/2000000000 : ℝ)] ![(1855428293963/4000000000000 : ℝ), (10098274952701/100000000000000 : ℝ), (10879004419781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346931453/10000000000 : ℝ)|^5535 ≤ (1855428293963/4000000000000 : ℝ)^4511
        have hw : |(5346931453/10000000000 : ℝ)|=(5346931453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-308671089/2000000000 : ℝ)|^5535 ≤ (10098274952701/100000000000000 : ℝ)^4511
        have hw : |(-308671089/2000000000 : ℝ)|=(308671089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015151079/2000000000 : ℝ)|^5535 ≤ (10879004419781/25000000000000 : ℝ)^4511
        have hw : |(1015151079/2000000000 : ℝ)|=(1015151079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_2 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346931443/10000000000 : ℝ)*x 0 + (1015151079/2000000000 : ℝ)*x 1 + (-771677729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346931443/10000000000 : ℝ)^5535 ≤ (46385707242631/100000000000000 : ℝ)^4511 := by
    have hnat : (5346931443 : ℕ)^5535*100000000000000^4511 ≤ 46385707242631^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346931443 10000000000 46385707242631 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015151079/2000000000 : ℝ)^5535 ≤ (10879004419781/25000000000000 : ℝ)^4511 := by
    have hnat : (1015151079 : ℕ)^5535*25000000000000^4511 ≤ 10879004419781^4511*2000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015151079 2000000000 10879004419781 25000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771677729/5000000000 : ℝ)^5535 ≤ (10098275057069/100000000000000 : ℝ)^4511 := by
    have hnat : (771677729 : ℕ)^5535*100000000000000^4511 ≤ 10098275057069^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771677729 5000000000 10098275057069 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346931443/10000000000 : ℝ), (1015151079/2000000000 : ℝ), (-771677729/5000000000 : ℝ)] ![(46385707242631/100000000000000 : ℝ), (10879004419781/25000000000000 : ℝ), (10098275057069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346931443/10000000000 : ℝ)|^5535 ≤ (46385707242631/100000000000000 : ℝ)^4511
        have hw : |(5346931443/10000000000 : ℝ)|=(5346931443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1015151079/2000000000 : ℝ)|^5535 ≤ (10879004419781/25000000000000 : ℝ)^4511
        have hw : |(1015151079/2000000000 : ℝ)|=(1015151079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-771677729/5000000000 : ℝ)|^5535 ≤ (10098275057069/100000000000000 : ℝ)^4511
        have hw : |(-771677729/5000000000 : ℝ)|=(771677729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_3 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1013382249/2500000000 : ℝ)*x 0 + (851118699/2500000000 : ℝ)*x 1 + (2384883019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013382249/2500000000 : ℝ)^5535 ≤ (257989011801/781250000000 : ℝ)^4511 := by
    have hnat : (1013382249 : ℕ)^5535*781250000000^4511 ≤ 257989011801^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013382249 2500000000 257989011801 781250000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (851118699/2500000000 : ℝ)^5535 ≤ (26657854311339/100000000000000 : ℝ)^4511 := by
    have hnat : (851118699 : ℕ)^5535*100000000000000^4511 ≤ 26657854311339^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851118699 2500000000 26657854311339 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2384883019/5000000000 : ℝ)^5535 ≤ (1259986004953/3125000000000 : ℝ)^4511 := by
    have hnat : (2384883019 : ℕ)^5535*3125000000000^4511 ≤ 1259986004953^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384883019 5000000000 1259986004953 3125000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1013382249/2500000000 : ℝ), (851118699/2500000000 : ℝ), (2384883019/5000000000 : ℝ)] ![(257989011801/781250000000 : ℝ), (26657854311339/100000000000000 : ℝ), (1259986004953/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1013382249/2500000000 : ℝ)|^5535 ≤ (257989011801/781250000000 : ℝ)^4511
        have hw : |(1013382249/2500000000 : ℝ)|=(1013382249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(851118699/2500000000 : ℝ)|^5535 ≤ (26657854311339/100000000000000 : ℝ)^4511
        have hw : |(851118699/2500000000 : ℝ)|=(851118699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2384883019/5000000000 : ℝ)|^5535 ≤ (1259986004953/3125000000000 : ℝ)^4511
        have hw : |(2384883019/5000000000 : ℝ)|=(2384883019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_4 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-655789879/5000000000 : ℝ)*x 0 + (5082781323/10000000000 : ℝ)*x 1 + (5511127097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655789879/5000000000 : ℝ)^5535 ≤ (1033816667937/12500000000000 : ℝ)^4511 := by
    have hnat : (655789879 : ℕ)^5535*12500000000000^4511 ≤ 1033816667937^4511*5000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655789879 5000000000 1033816667937 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5082781323/10000000000 : ℝ)^5535 ≤ (5448742277893/12500000000000 : ℝ)^4511 := by
    have hnat : (5082781323 : ℕ)^5535*12500000000000^4511 ≤ 5448742277893^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5082781323 10000000000 5448742277893 12500000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511127097/10000000000 : ℝ)^5535 ≤ (1504360263207/3125000000000 : ℝ)^4511 := by
    have hnat : (5511127097 : ℕ)^5535*3125000000000^4511 ≤ 1504360263207^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511127097 10000000000 1504360263207 3125000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-655789879/5000000000 : ℝ), (5082781323/10000000000 : ℝ), (5511127097/10000000000 : ℝ)] ![(1033816667937/12500000000000 : ℝ), (5448742277893/12500000000000 : ℝ), (1504360263207/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-655789879/5000000000 : ℝ)|^5535 ≤ (1033816667937/12500000000000 : ℝ)^4511
        have hw : |(-655789879/5000000000 : ℝ)|=(655789879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5082781323/10000000000 : ℝ)|^5535 ≤ (5448742277893/12500000000000 : ℝ)^4511
        have hw : |(5082781323/10000000000 : ℝ)|=(5082781323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511127097/10000000000 : ℝ)|^5535 ≤ (1504360263207/3125000000000 : ℝ)^4511
        have hw : |(5511127097/10000000000 : ℝ)|=(5511127097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_5 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261462769/500000000 : ℝ)*x 0 + (-17312249/156250000 : ℝ)*x 1 + (5511126871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261462769/500000000 : ℝ)^5535 ≤ (45136253818463/100000000000000 : ℝ)^4511 := by
    have hnat : (261462769 : ℕ)^5535*100000000000000^4511 ≤ 45136253818463^4511*500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261462769 500000000 45136253818463 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17312249/156250000 : ℝ)^5535 ≤ (1344844033077/20000000000000 : ℝ)^4511 := by
    have hnat : (17312249 : ℕ)^5535*20000000000000^4511 ≤ 1344844033077^4511*156250000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17312249 156250000 1344844033077 20000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511126871/10000000000 : ℝ)^5535 ≤ (24069763000199/50000000000000 : ℝ)^4511 := by
    have hnat : (5511126871 : ℕ)^5535*50000000000000^4511 ≤ 24069763000199^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511126871 10000000000 24069763000199 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261462769/500000000 : ℝ), (-17312249/156250000 : ℝ), (5511126871/10000000000 : ℝ)] ![(45136253818463/100000000000000 : ℝ), (1344844033077/20000000000000 : ℝ), (24069763000199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261462769/500000000 : ℝ)|^5535 ≤ (45136253818463/100000000000000 : ℝ)^4511
        have hw : |(261462769/500000000 : ℝ)|=(261462769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17312249/156250000 : ℝ)|^5535 ≤ (1344844033077/20000000000000 : ℝ)^4511
        have hw : |(-17312249/156250000 : ℝ)|=(17312249/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511126871/10000000000 : ℝ)|^5535 ≤ (24069763000199/50000000000000 : ℝ)^4511
        have hw : |(5511126871/10000000000 : ℝ)|=(5511126871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_6 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229255341/10000000000 : ℝ)*x 0 + (8817803/16000000 : ℝ)*x 1 + (-1107983987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229255341/10000000000 : ℝ)^5535 ≤ (2256812670271/5000000000000 : ℝ)^4511 := by
    have hnat : (5229255341 : ℕ)^5535*5000000000000^4511 ≤ 2256812670271^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229255341 10000000000 2256812670271 5000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8817803/16000000 : ℝ)^5535 ≤ (48139526043269/100000000000000 : ℝ)^4511 := by
    have hnat : (8817803 : ℕ)^5535*100000000000000^4511 ≤ 48139526043269^4511*16000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8817803 16000000 48139526043269 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107983987/10000000000 : ℝ)^5535 ≤ (6724220545157/100000000000000 : ℝ)^4511 := by
    have hnat : (1107983987 : ℕ)^5535*100000000000000^4511 ≤ 6724220545157^4511*10000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107983987 10000000000 6724220545157 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229255341/10000000000 : ℝ), (8817803/16000000 : ℝ), (-1107983987/10000000000 : ℝ)] ![(2256812670271/5000000000000 : ℝ), (48139526043269/100000000000000 : ℝ), (6724220545157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229255341/10000000000 : ℝ)|^5535 ≤ (2256812670271/5000000000000 : ℝ)^4511
        have hw : |(5229255341/10000000000 : ℝ)|=(5229255341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8817803/16000000 : ℝ)|^5535 ≤ (48139526043269/100000000000000 : ℝ)^4511
        have hw : |(8817803/16000000 : ℝ)|=(8817803/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1107983987/10000000000 : ℝ)|^5535 ≤ (6724220545157/100000000000000 : ℝ)^4511
        have hw : |(-1107983987/10000000000 : ℝ)|=(1107983987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1735_s2_7 (p : ℝ) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1013679677/2500000000 : ℝ)*x 0 + (1187022593/2500000000 : ℝ)*x 1 + (342660859/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1013679677/2500000000 : ℝ)^5535 ≤ (33034486170471/100000000000000 : ℝ)^4511 := by
    have hnat : (1013679677 : ℕ)^5535*100000000000000^4511 ≤ 33034486170471^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013679677 2500000000 33034486170471 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1187022593/2500000000 : ℝ)^5535 ≤ (20047423887191/50000000000000 : ℝ)^4511 := by
    have hnat : (1187022593 : ℕ)^5535*50000000000000^4511 ≤ 20047423887191^4511*2500000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187022593 2500000000 20047423887191 50000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342660859/1000000000 : ℝ)^5535 ≤ (26870666033053/100000000000000 : ℝ)^4511 := by
    have hnat : (342660859 : ℕ)^5535*100000000000000^4511 ≤ 26870666033053^4511*1000000000^5535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342660859 1000000000 26870666033053 100000000000000 5535 4511 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5535/1024 : ℝ)) 5535 4511 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1013679677/2500000000 : ℝ), (1187022593/2500000000 : ℝ), (342660859/1000000000 : ℝ)] ![(33034486170471/100000000000000 : ℝ), (20047423887191/50000000000000 : ℝ), (26870666033053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1013679677/2500000000 : ℝ)|^5535 ≤ (33034486170471/100000000000000 : ℝ)^4511
        have hw : |(1013679677/2500000000 : ℝ)|=(1013679677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1187022593/2500000000 : ℝ)|^5535 ≤ (20047423887191/50000000000000 : ℝ)^4511
        have hw : |(1187022593/2500000000 : ℝ)|=(1187022593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(342660859/1000000000 : ℝ)|^5535 ≤ (26870666033053/100000000000000 : ℝ)^4511
        have hw : |(342660859/1000000000 : ℝ)|=(342660859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1735_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18407/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1763/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (731/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18407/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18407/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4353/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18407/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18407/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4353/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18407/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18407/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4353/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4353/50000 : ℝ) ^ (5519/1024 : ℝ) ≤ (193194746516823/100000000000000000000 : ℝ) := by
    have hpowers : (4353/50000 : ℝ)^5519 ≤ (193194746516823/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4353 : ℕ)^5519*100000000000000000000^1024 ≤ 193194746516823^1024*50000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4353 50000 193194746516823 100000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4353/50000 : ℝ)) (X := (193194746516823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18407/100000 : ℝ) ^ (5519/1024 : ℝ) ≤ (2731849999861767/25000000000000000000 : ℝ) := by
    have hpowers : (18407/100000 : ℝ)^5519 ≤ (2731849999861767/25000000000000000000 : ℝ)^1024 := by
      have hnat : (18407 : ℕ)^5519*25000000000000000000^1024 ≤ 2731849999861767^1024*100000^5519 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18407 100000 2731849999861767 25000000000000000000 5519 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18407/100000 : ℝ)) (X := (2731849999861767/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000193194746516823/50000000000000000000 : ℝ) ≤ (10000007169092559/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (50000193194746516823/50000000000000000000 : ℝ)^1024 ≤ (10000007169092559/10000000000000000 : ℝ)^5519 := by
      have hnat : (50000193194746516823 : ℕ)^1024*10000000000000000^5519 ≤ 10000007169092559^5519*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000193194746516823 50000000000000000000 10000007169092559 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007169092559/10000000000000000 : ℝ)) (X := (50000193194746516823/50000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011120594745963891/100000000000000000000 : ℝ) ≤ (2000041264625319/2000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (100011120594745963891/100000000000000000000 : ℝ)^1024 ≤ (2000041264625319/2000000000000000 : ℝ)^5519 := by
      have hnat : (100011120594745963891 : ℕ)^1024*2000000000000000^5519 ≤ 2000041264625319^5519*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011120594745963891 100000000000000000000 2000041264625319 2000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000041264625319/2000000000000000 : ℝ)) (X := (100011120594745963891/100000000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502731849999861767/12500000000000000000 : ℝ) ≤ (10000405477160631/10000000000000000 : ℝ) ^ (5519/1024 : ℝ) := by
    have hpowers : (12502731849999861767/12500000000000000000 : ℝ)^1024 ≤ (10000405477160631/10000000000000000 : ℝ)^5519 := by
      have hnat : (12502731849999861767 : ℕ)^1024*10000000000000000^5519 ≤ 10000405477160631^5519*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502731849999861767 12500000000000000000 10000405477160631 10000000000000000 1024 5519 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000405477160631/10000000000000000 : ℝ)) (X := (12502731849999861767/12500000000000000000 : ℝ)) (by norm_num) 5519 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(193194746516823/100000000000000000000 : ℝ) ≤ ((97006601877326280027/97010000000000000000 : ℝ)+2*(49788508509/242525000000000 : ℝ)*(4353/50000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (97006601877326280027/97010000000000000000 : ℝ)+2*(49788508509/242525000000000 : ℝ)*(4353/50000 : ℝ)=(10000007169092559/10000000000000000 : ℝ) by norm_num, show 1+2*(193194746516823/100000000000000000000 : ℝ)=(50000193194746516823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2731849999861767/25000000000000000000 : ℝ)+(193194746516823/100000000000000000000 : ℝ) ≤ ((97006601877326280027/97010000000000000000 : ℝ)+(49788508509/242525000000000 : ℝ)*((18407/100000 : ℝ)+(4353/50000 : ℝ)))^(5519/1024 : ℝ) := by
    rw [show (97006601877326280027/97010000000000000000 : ℝ)+(49788508509/242525000000000 : ℝ)*((18407/100000 : ℝ)+(4353/50000 : ℝ))=(2000041264625319/2000000000000000 : ℝ) by norm_num, show 1+(2731849999861767/25000000000000000000 : ℝ)+(193194746516823/100000000000000000000 : ℝ)=(100011120594745963891/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2731849999861767/25000000000000000000 : ℝ) ≤ ((97006601877326280027/97010000000000000000 : ℝ)+2*(49788508509/242525000000000 : ℝ)*(18407/100000 : ℝ))^(5519/1024 : ℝ) := by
    rw [show (97006601877326280027/97010000000000000000 : ℝ)+2*(49788508509/242525000000000 : ℝ)*(18407/100000 : ℝ)=(10000405477160631/10000000000000000 : ℝ) by norm_num, show 1+2*(2731849999861767/25000000000000000000 : ℝ)=(12502731849999861767/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (97006601877326280027/97010000000000000000 : ℝ)*(X 1 0+X 2 0)+(49788508509/242525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (4353/50000 : ℝ)) (hi := (18407/100000 : ℝ)) (c := (97006601877326280027/97010000000000000000 : ℝ)) (alpha := (49788508509/242525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (97006601877326280027/97010000000000000000 : ℝ)*(X 0 1+X 2 1)+(49788508509/242525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (4353/50000 : ℝ)) (hi := (18407/100000 : ℝ)) (c := (97006601877326280027/97010000000000000000 : ℝ)) (alpha := (49788508509/242525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (97006601877326280027/97010000000000000000 : ℝ)*(X 0 2+X 1 2)+(49788508509/242525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5519/1024 : ℝ)) (lo := (4353/50000 : ℝ)) (hi := (18407/100000 : ℝ)) (c := (97006601877326280027/97010000000000000000 : ℝ)) (alpha := (49788508509/242525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1311194093/10000000000 : ℝ)*X 0 0+(275915071/500000000 : ℝ)*X 0 1+(2537877697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346931453/10000000000 : ℝ)*X 1 0+(-308671089/2000000000 : ℝ)*X 1 1+(1015151079/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346931443/10000000000 : ℝ)*X 2 0+(1015151079/2000000000 : ℝ)*X 2 1+(-771677729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1013382249/2500000000 : ℝ)*X 0 0+(851118699/2500000000 : ℝ)*X 0 1+(2384883019/5000000000 : ℝ)*X 0 2+(1013382249/2500000000 : ℝ)*X 1 0+(851118699/2500000000 : ℝ)*X 1 1+(2384883019/5000000000 : ℝ)*X 1 2+(1013382249/2500000000 : ℝ)*X 2 0+(851118699/2500000000 : ℝ)*X 2 1+(2384883019/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-655789879/5000000000 : ℝ)*X 0 0+(5082781323/10000000000 : ℝ)*X 0 1+(5511127097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((261462769/500000000 : ℝ)*X 1 0+(-17312249/156250000 : ℝ)*X 1 1+(5511126871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5229255341/10000000000 : ℝ)*X 2 0+(8817803/16000000 : ℝ)*X 2 1+(-1107983987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1013679677/2500000000 : ℝ)*X 0 0+(1187022593/2500000000 : ℝ)*X 0 1+(342660859/1000000000 : ℝ)*X 0 2+(1013679677/2500000000 : ℝ)*X 1 0+(1187022593/2500000000 : ℝ)*X 1 1+(342660859/1000000000 : ℝ)*X 1 2+(1013679677/2500000000 : ℝ)*X 2 0+(1187022593/2500000000 : ℝ)*X 2 1+(342660859/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1735_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (543071127907941666207231/48505000000000000000000000000 : ℝ) := by norm_num
    linear_combination (806505273/50000000000000 : ℝ)*(base19) + (4728237/312500000000 : ℝ)*(base23) + (12799029/25000000000000 : ℝ)*(lower2) + (278290419/100000000000000 : ℝ)*(upper3) + (100453113/50000000000000 : ℝ)*(upper5) + (1496064335480421/100000000000000 : ℝ)*(major0) + (1496064335480421/100000000000000 : ℝ)*(major1) + (1496064335480421/100000000000000 : ℝ)*(major2) + (2259664083955321/100000000000000 : ℝ)*(sp0) + (225967432797161/10000000000000 : ℝ)*(sp1) + (451934885589263/20000000000000 : ℝ)*(sp2) + (732448121932621/100000000000000 : ℝ)*(sp3) + (5928513417/50000000000000 : ℝ)*(sp4) + (4234839773/100000000000000 : ℝ)*(sp7) + (366226178386197/50000000000000 : ℝ)*(f.failure) + (564918985245539/25000000000000 : ℝ)*(f.sum) + (139108221987781/48505000000000000000000000000 : ℝ)*base65 + (15343636385863451367/9701000000000000000000000000000000 : ℝ)*base67 + (13395821430697451367/9701000000000000000000000000000000 : ℝ)*base69 + (73968989295392548633/9701000000000000000000000000000000 : ℝ)*base72 + (98396089897523/24252500000000000000000000000 : ℝ)*base73 + (32490525339480548633/9701000000000000000000000000000000 : ℝ)*base76 + (19263119085892451367/9701000000000000000000000000000000 : ℝ)*base77 + (2852938919459548633/9701000000000000000000000000000000 : ℝ)*base80 + (26376618307083/24252500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (200649/100000000000000000000 : ℝ)*base90 + (200649/100000000000000000000 : ℝ)*base92 + (200649/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15522906078358029395628191463/1212625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17036993/1000000000000 : ℝ)*(base19) + (893929507/50000000000000 : ℝ)*(base23) + (249897843/100000000000000 : ℝ)*(upper3) + (1592149/3125000000000 : ℝ)*(lower4) + (134553449/50000000000000 : ℝ)*(upper5) + (386411095316623/25000000000000 : ℝ)*(major0) + (386411095316623/25000000000000 : ℝ)*(major1) + (386411095316623/25000000000000 : ℝ)*(major2) + (10614155407/100000000000000 : ℝ)*(sp1) + (10798156277/100000000000000 : ℝ)*(sp2) + (2334562276033589/100000000000000 : ℝ)*(sp4) + (1167274979089441/50000000000000 : ℝ)*(sp5) + (1167274845009149/50000000000000 : ℝ)*(sp6) + (756726059796823/100000000000000 : ℝ)*(sp7) + (756726059796823/100000000000000 : ℝ)*(f.failure) + (2334562276033589/100000000000000 : ℝ)*(f.sum) + (119485214905699/24252500000000000000000000000 : ℝ)*base66 + (1686820147493038821/2425250000000000000000000000000000 : ℝ)*base67 + (10431000411081961179/2425250000000000000000000000000000 : ℝ)*base70 + (4798346401559961179/2425250000000000000000000000000000 : ℝ)*base72 + (44263320932233/48505000000000000000000000000 : ℝ)*base74 + (3745914843995461179/2425250000000000000000000000000000 : ℝ)*base76 + (3194924001840538821/2425250000000000000000000000000000 : ℝ)*base77 + (7275848669886461179/2425250000000000000000000000000000 : ℝ)*base80 + (166632859619589/24252500000000000000000000000 : ℝ)*base82 + (1091309/200000000000000000000 : ℝ)*base89 + (1091309/200000000000000000000 : ℝ)*base91 + (1091309/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1735_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18407/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4353/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (731/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1735_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1735_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (731/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1735_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1735_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1735_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5519/1024 : ℝ) ≤ p) (hpb : p ≤ (5535/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4085083/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1763/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (731/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1735_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

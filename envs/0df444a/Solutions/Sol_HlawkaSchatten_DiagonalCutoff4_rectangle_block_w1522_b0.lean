-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1522_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:48.656538+00:00
-- url     : https://prove2.me/submissions/c60d105a-2f61-46ab-9d42-921a26b1fc5c

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
theorem support_rectangle_w1522_s0_0 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418819839/2500000000 : ℝ)*x 0 + (147629261/250000000 : ℝ)*x 1 + (2429785657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418819839/2500000000 : ℝ)^4541 ≤ (4979028652117/50000000000000 : ℝ)^3517 := by
    have hnat : (418819839 : ℕ)^4541*50000000000000^3517 ≤ 4979028652117^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418819839 2500000000 4979028652117 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147629261/250000000 : ℝ)^4541 ≤ (25327662479317/50000000000000 : ℝ)^3517 := by
    have hnat : (147629261 : ℕ)^4541*50000000000000^3517 ≤ 25327662479317^3517*250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147629261 250000000 25327662479317 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2429785657/5000000000 : ℝ)^4541 ≤ (39386617720331/100000000000000 : ℝ)^3517 := by
    have hnat : (2429785657 : ℕ)^4541*100000000000000^3517 ≤ 39386617720331^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429785657 5000000000 39386617720331 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418819839/2500000000 : ℝ), (147629261/250000000 : ℝ), (2429785657/5000000000 : ℝ)] ![(4979028652117/50000000000000 : ℝ), (25327662479317/50000000000000 : ℝ), (39386617720331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418819839/2500000000 : ℝ)|^4541 ≤ (4979028652117/50000000000000 : ℝ)^3517
        have hw : |(-418819839/2500000000 : ℝ)|=(418819839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147629261/250000000 : ℝ)|^4541 ≤ (25327662479317/50000000000000 : ℝ)^3517
        have hw : |(147629261/250000000 : ℝ)|=(147629261/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2429785657/5000000000 : ℝ)|^4541 ≤ (39386617720331/100000000000000 : ℝ)^3517
        have hw : |(2429785657/5000000000 : ℝ)|=(2429785657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_1 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2737903651/5000000000 : ℝ)*x 0 + (-2260607179/10000000000 : ℝ)*x 1 + (4859571227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737903651/5000000000 : ℝ)^4541 ≤ (45951050533827/100000000000000 : ℝ)^3517 := by
    have hnat : (2737903651 : ℕ)^4541*100000000000000^3517 ≤ 45951050533827^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737903651 5000000000 45951050533827 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260607179/10000000000 : ℝ)^4541 ≤ (14662332641109/100000000000000 : ℝ)^3517 := by
    have hnat : (2260607179 : ℕ)^4541*100000000000000^3517 ≤ 14662332641109^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260607179 10000000000 14662332641109 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4859571227/10000000000 : ℝ)^4541 ≤ (4923327101237/12500000000000 : ℝ)^3517 := by
    have hnat : (4859571227 : ℕ)^4541*12500000000000^3517 ≤ 4923327101237^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859571227 10000000000 4923327101237 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737903651/5000000000 : ℝ), (-2260607179/10000000000 : ℝ), (4859571227/10000000000 : ℝ)] ![(45951050533827/100000000000000 : ℝ), (14662332641109/100000000000000 : ℝ), (4923327101237/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737903651/5000000000 : ℝ)|^4541 ≤ (45951050533827/100000000000000 : ℝ)^3517
        have hw : |(2737903651/5000000000 : ℝ)|=(2737903651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260607179/10000000000 : ℝ)|^4541 ≤ (14662332641109/100000000000000 : ℝ)^3517
        have hw : |(-2260607179/10000000000 : ℝ)|=(2260607179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4859571227/10000000000 : ℝ)|^4541 ≤ (4923327101237/12500000000000 : ℝ)^3517
        have hw : |(4859571227/10000000000 : ℝ)|=(4859571227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_2 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547580741/1000000000 : ℝ)*x 0 + (4859571283/10000000000 : ℝ)*x 1 + (-2260606969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547580741/1000000000 : ℝ)^4541 ≤ (5743881463/12500000000 : ℝ)^3517 := by
    have hnat : (547580741 : ℕ)^4541*12500000000^3517 ≤ 5743881463^3517*1000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547580741 1000000000 5743881463 12500000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4859571283/10000000000 : ℝ)^4541 ≤ (39386617395923/100000000000000 : ℝ)^3517 := by
    have hnat : (4859571283 : ℕ)^4541*100000000000000^3517 ≤ 39386617395923^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4859571283 10000000000 39386617395923 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260606969/10000000000 : ℝ)^4541 ≤ (14662330882471/100000000000000 : ℝ)^3517 := by
    have hnat : (2260606969 : ℕ)^4541*100000000000000^3517 ≤ 14662330882471^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260606969 10000000000 14662330882471 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547580741/1000000000 : ℝ), (4859571283/10000000000 : ℝ), (-2260606969/10000000000 : ℝ)] ![(5743881463/12500000000 : ℝ), (39386617395923/100000000000000 : ℝ), (14662330882471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547580741/1000000000 : ℝ)|^4541 ≤ (5743881463/12500000000 : ℝ)^3517
        have hw : |(547580741/1000000000 : ℝ)|=(547580741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4859571283/10000000000 : ℝ)|^4541 ≤ (39386617395923/100000000000000 : ℝ)^3517
        have hw : |(4859571283/10000000000 : ℝ)|=(4859571283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2260606969/10000000000 : ℝ)|^4541 ≤ (14662330882471/100000000000000 : ℝ)^3517
        have hw : |(-2260606969/10000000000 : ℝ)|=(2260606969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_3 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2071229059/5000000000 : ℝ)*x 0 + (193212179/625000000 : ℝ)*x 1 + (5479097061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071229059/5000000000 : ℝ)^4541 ≤ (32049411554423/100000000000000 : ℝ)^3517 := by
    have hnat : (2071229059 : ℕ)^4541*100000000000000^3517 ≤ 32049411554423^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071229059 5000000000 32049411554423 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193212179/625000000 : ℝ)^4541 ≤ (21963890446771/100000000000000 : ℝ)^3517 := by
    have hnat : (193212179 : ℕ)^4541*100000000000000^3517 ≤ 21963890446771^3517*625000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193212179 625000000 21963890446771 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5479097061/10000000000 : ℝ)^4541 ≤ (45986697984943/100000000000000 : ℝ)^3517 := by
    have hnat : (5479097061 : ℕ)^4541*100000000000000^3517 ≤ 45986697984943^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479097061 10000000000 45986697984943 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2071229059/5000000000 : ℝ), (193212179/625000000 : ℝ), (5479097061/10000000000 : ℝ)] ![(32049411554423/100000000000000 : ℝ), (21963890446771/100000000000000 : ℝ), (45986697984943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2071229059/5000000000 : ℝ)|^4541 ≤ (32049411554423/100000000000000 : ℝ)^3517
        have hw : |(2071229059/5000000000 : ℝ)|=(2071229059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193212179/625000000 : ℝ)|^4541 ≤ (21963890446771/100000000000000 : ℝ)^3517
        have hw : |(193212179/625000000 : ℝ)|=(193212179/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5479097061/10000000000 : ℝ)|^4541 ≤ (45986697984943/100000000000000 : ℝ)^3517
        have hw : |(5479097061/10000000000 : ℝ)|=(5479097061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_4 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-335743027/2000000000 : ℝ)*x 0 + (977238053/2000000000 : ℝ)*x 1 + (2938799759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335743027/2000000000 : ℝ)^4541 ≤ (4992217028261/50000000000000 : ℝ)^3517 := by
    have hnat : (335743027 : ℕ)^4541*50000000000000^3517 ≤ 4992217028261^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335743027 2000000000 4992217028261 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977238053/2000000000 : ℝ)^4541 ≤ (39665400877133/100000000000000 : ℝ)^3517 := by
    have hnat : (977238053 : ℕ)^4541*100000000000000^3517 ≤ 39665400877133^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977238053 2000000000 39665400877133 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2938799759/5000000000 : ℝ)^4541 ≤ (50350165050461/100000000000000 : ℝ)^3517 := by
    have hnat : (2938799759 : ℕ)^4541*100000000000000^3517 ≤ 50350165050461^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938799759 5000000000 50350165050461 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-335743027/2000000000 : ℝ), (977238053/2000000000 : ℝ), (2938799759/5000000000 : ℝ)] ![(4992217028261/50000000000000 : ℝ), (39665400877133/100000000000000 : ℝ), (50350165050461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-335743027/2000000000 : ℝ)|^4541 ≤ (4992217028261/50000000000000 : ℝ)^3517
        have hw : |(-335743027/2000000000 : ℝ)|=(335743027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977238053/2000000000 : ℝ)|^4541 ≤ (39665400877133/100000000000000 : ℝ)^3517
        have hw : |(977238053/2000000000 : ℝ)|=(977238053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2938799759/5000000000 : ℝ)|^4541 ≤ (50350165050461/100000000000000 : ℝ)^3517
        have hw : |(2938799759/5000000000 : ℝ)|=(2938799759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_5 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1297523873/2500000000 : ℝ)*x 0 + (-310644753/2500000000 : ℝ)*x 1 + (1175519913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297523873/2500000000 : ℝ)^4541 ≤ (2679949481597/6250000000000 : ℝ)^3517 := by
    have hnat : (1297523873 : ℕ)^4541*6250000000000^3517 ≤ 2679949481597^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297523873 2500000000 2679949481597 6250000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310644753/2500000000 : ℝ)^4541 ≤ (211582584799/3125000000000 : ℝ)^3517 := by
    have hnat : (310644753 : ℕ)^4541*3125000000000^3517 ≤ 211582584799^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310644753 2500000000 211582584799 3125000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1175519913/2000000000 : ℝ)^4541 ≤ (50350165570311/100000000000000 : ℝ)^3517 := by
    have hnat : (1175519913 : ℕ)^4541*100000000000000^3517 ≤ 50350165570311^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175519913 2000000000 50350165570311 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1297523873/2500000000 : ℝ), (-310644753/2500000000 : ℝ), (1175519913/2000000000 : ℝ)] ![(2679949481597/6250000000000 : ℝ), (211582584799/3125000000000 : ℝ), (50350165570311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1297523873/2500000000 : ℝ)|^4541 ≤ (2679949481597/6250000000000 : ℝ)^3517
        have hw : |(1297523873/2500000000 : ℝ)|=(1297523873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310644753/2500000000 : ℝ)|^4541 ≤ (211582584799/3125000000000 : ℝ)^3517
        have hw : |(-310644753/2500000000 : ℝ)|=(310644753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1175519913/2000000000 : ℝ)|^4541 ≤ (50350165570311/100000000000000 : ℝ)^3517
        have hw : |(1175519913/2000000000 : ℝ)|=(1175519913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_6 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648761931/1250000000 : ℝ)*x 0 + (2938799871/5000000000 : ℝ)*x 1 + (-3106447/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648761931/1250000000 : ℝ)^4541 ≤ (8575838247239/20000000000000 : ℝ)^3517 := by
    have hnat : (648761931 : ℕ)^4541*20000000000000^3517 ≤ 8575838247239^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648761931 1250000000 8575838247239 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2938799871/5000000000 : ℝ)^4541 ≤ (50350167528043/100000000000000 : ℝ)^3517 := by
    have hnat : (2938799871 : ℕ)^4541*100000000000000^3517 ≤ 50350167528043^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938799871 5000000000 50350167528043 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3106447/25000000 : ℝ)^4541 ≤ (1692660305519/25000000000000 : ℝ)^3517 := by
    have hnat : (3106447 : ℕ)^4541*25000000000000^3517 ≤ 1692660305519^3517*25000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106447 25000000 1692660305519 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648761931/1250000000 : ℝ), (2938799871/5000000000 : ℝ), (-3106447/25000000 : ℝ)] ![(8575838247239/20000000000000 : ℝ), (50350167528043/100000000000000 : ℝ), (1692660305519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648761931/1250000000 : ℝ)|^4541 ≤ (8575838247239/20000000000000 : ℝ)^3517
        have hw : |(648761931/1250000000 : ℝ)|=(648761931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2938799871/5000000000 : ℝ)|^4541 ≤ (50350167528043/100000000000000 : ℝ)^3517
        have hw : |(2938799871/5000000000 : ℝ)|=(2938799871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3106447/25000000 : ℝ)|^4541 ≤ (1692660305519/25000000000000 : ℝ)^3517
        have hw : |(-3106447/25000000 : ℝ)|=(3106447/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s0_7 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037575941/2500000000 : ℝ)*x 0 + (5418310701/10000000000 : ℝ)*x 1 + (630871047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037575941/2500000000 : ℝ)^4541 ≤ (4015975843789/12500000000000 : ℝ)^3517 := by
    have hnat : (1037575941 : ℕ)^4541*12500000000000^3517 ≤ 4015975843789^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037575941 2500000000 4015975843789 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418310701/10000000000 : ℝ)^4541 ≤ (22664516541437/50000000000000 : ℝ)^3517 := by
    have hnat : (5418310701 : ℕ)^4541*50000000000000^3517 ≤ 22664516541437^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418310701 10000000000 22664516541437 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630871047/2000000000 : ℝ)^4541 ≤ (22543160144369/100000000000000 : ℝ)^3517 := by
    have hnat : (630871047 : ℕ)^4541*100000000000000^3517 ≤ 22543160144369^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630871047 2000000000 22543160144369 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037575941/2500000000 : ℝ), (5418310701/10000000000 : ℝ), (630871047/2000000000 : ℝ)] ![(4015975843789/12500000000000 : ℝ), (22664516541437/50000000000000 : ℝ), (22543160144369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037575941/2500000000 : ℝ)|^4541 ≤ (4015975843789/12500000000000 : ℝ)^3517
        have hw : |(1037575941/2500000000 : ℝ)|=(1037575941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418310701/10000000000 : ℝ)|^4541 ≤ (22664516541437/50000000000000 : ℝ)^3517
        have hw : |(5418310701/10000000000 : ℝ)|=(5418310701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(630871047/2000000000 : ℝ)|^4541 ≤ (22543160144369/100000000000000 : ℝ)^3517
        have hw : |(630871047/2000000000 : ℝ)|=(630871047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1522_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (591/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5071/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4539/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4539 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4539*1^1024 ≤ 0^1024*1^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4539/1024 : ℝ) ≤ (344440549677020609/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4539 ≤ (344440549677020609/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4539*20000000000000000000^1024 ≤ 344440549677020609^1024*5^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 344440549677020609 20000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (344440549677020609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4539 := by
      have hnat : (1 : ℕ)^1024*1^4539 ≤ 1^4539*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20344440549677020609/20000000000000000000 : ℝ) ≤ (10038596476981207/10000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (20344440549677020609/20000000000000000000 : ℝ)^1024 ≤ (10038596476981207/10000000000000000 : ℝ)^4539 := by
      have hnat : (20344440549677020609 : ℕ)^1024*10000000000000000^4539 ≤ 10038596476981207^4539*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20344440549677020609 20000000000000000000 10038596476981207 10000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10038596476981207/10000000000000000 : ℝ)) (X := (20344440549677020609/20000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10344440549677020609/10000000000000000000 : ℝ) ≤ (5038596476981207/5000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (10344440549677020609/10000000000000000000 : ℝ)^1024 ≤ (5038596476981207/5000000000000000 : ℝ)^4539 := by
      have hnat : (10344440549677020609 : ℕ)^1024*5000000000000000^4539 ≤ 5038596476981207^4539*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10344440549677020609 10000000000000000000 5038596476981207 5000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038596476981207/5000000000000000 : ℝ)) (X := (10344440549677020609/10000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(38596476981207/4000000000000000 : ℝ)*(0 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(38596476981207/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(344440549677020609/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(38596476981207/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4539/1024 : ℝ) := by
    rw [show (1 : ℝ)+(38596476981207/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10038596476981207/10000000000000000 : ℝ) by norm_num, show 1+(344440549677020609/20000000000000000000 : ℝ)+(0 : ℝ)=(20344440549677020609/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(344440549677020609/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(38596476981207/4000000000000000 : ℝ)*(2/5 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(38596476981207/4000000000000000 : ℝ)*(2/5 : ℝ)=(5038596476981207/5000000000000000 : ℝ) by norm_num, show 1+2*(344440549677020609/20000000000000000000 : ℝ)=(10344440549677020609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(38596476981207/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (38596476981207/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(38596476981207/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (38596476981207/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(38596476981207/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (38596476981207/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-418819839/2500000000 : ℝ)*X 0 0+(147629261/250000000 : ℝ)*X 0 1+(2429785657/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2737903651/5000000000 : ℝ)*X 1 0+(-2260607179/10000000000 : ℝ)*X 1 1+(4859571227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((547580741/1000000000 : ℝ)*X 2 0+(4859571283/10000000000 : ℝ)*X 2 1+(-2260606969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2071229059/5000000000 : ℝ)*X 0 0+(193212179/625000000 : ℝ)*X 0 1+(5479097061/10000000000 : ℝ)*X 0 2+(2071229059/5000000000 : ℝ)*X 1 0+(193212179/625000000 : ℝ)*X 1 1+(5479097061/10000000000 : ℝ)*X 1 2+(2071229059/5000000000 : ℝ)*X 2 0+(193212179/625000000 : ℝ)*X 2 1+(5479097061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-335743027/2000000000 : ℝ)*X 0 0+(977238053/2000000000 : ℝ)*X 0 1+(2938799759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1297523873/2500000000 : ℝ)*X 1 0+(-310644753/2500000000 : ℝ)*X 1 1+(1175519913/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((648761931/1250000000 : ℝ)*X 2 0+(2938799871/5000000000 : ℝ)*X 2 1+(-3106447/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037575941/2500000000 : ℝ)*X 0 0+(5418310701/10000000000 : ℝ)*X 0 1+(630871047/2000000000 : ℝ)*X 0 2+(1037575941/2500000000 : ℝ)*X 1 0+(5418310701/10000000000 : ℝ)*X 1 1+(630871047/2000000000 : ℝ)*X 1 2+(1037575941/2500000000 : ℝ)*X 2 0+(5418310701/10000000000 : ℝ)*X 2 1+(630871047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177153073489971255306459/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5284853/12500000000000 : ℝ)*(base1) + (829770999/50000000000000 : ℝ)*(base19) + (1678405179/100000000000000 : ℝ)*(base23) + (184193707/100000000000000 : ℝ)*(upper3) + (62465483/25000000000000 : ℝ)*(upper5) + (343804856372479/50000000000000 : ℝ)*(major0) + (343804856372479/50000000000000 : ℝ)*(major1) + (343804856372479/50000000000000 : ℝ)*(major2) + (478197476347641/50000000000000 : ℝ)*(sp0) + (956399537690953/100000000000000 : ℝ)*(sp1) + (239099879706943/25000000000000 : ℝ)*(sp2) + (209407671521287/50000000000000 : ℝ)*(sp3) + (6286816493/100000000000000 : ℝ)*(sp4) + (521346293/20000000000000 : ℝ)*(sp7) + (418817992052863/100000000000000 : ℝ)*(f.failure) + (956401197232951/100000000000000 : ℝ)*(f.sum) + (50782329497847/100000000000000000000000000000 : ℝ)*base66 + (109859650197847/200000000000000000000000000000 : ℝ)*base68 + (1888476367197847/200000000000000000000000000000 : ℝ)*base70 + (649387084597847/200000000000000000000000000000 : ℝ)*base72 + (224021143602153/100000000000000000000000000000 : ℝ)*base73 + (1651560048997847/200000000000000000000000000000 : ℝ)*base76 + (1404317427397847/200000000000000000000000000000 : ℝ)*base78 + (1130293000397847/200000000000000000000000000000 : ℝ)*base80 + (312439447097847/100000000000000000000000000000 : ℝ)*base82 + (183639/10000000000000000000000 : ℝ)*base90 + (183639/10000000000000000000000 : ℝ)*base92 + (183639/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10028261863234887556869/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70000459/10000000000000 : ℝ)*(base19) + (184342583/25000000000000 : ℝ)*(base23) + (38369159/100000000000000 : ℝ)*(base39) + (100885977/100000000000000 : ℝ)*(upper3) + (14230403/12500000000000 : ℝ)*(upper5) + (362592456887603/50000000000000 : ℝ)*(major0) + (362592456887603/50000000000000 : ℝ)*(major1) + (22662027356439/3125000000000 : ℝ)*(major2) + (945085039/50000000000000 : ℝ)*(sp1) + (510058799/25000000000000 : ℝ)*(sp2) + (504332456516253/50000000000000 : ℝ)*(sp4) + (504331161428919/50000000000000 : ℝ)*(sp5) + (1008662173796137/100000000000000 : ℝ)*(sp6) + (88340953836123/20000000000000 : ℝ)*(sp7) + (88340953836123/20000000000000 : ℝ)*(f.failure) + (201732990280333/20000000000000 : ℝ)*(f.sum) + (52534272653211/200000000000000000000000000000 : ℝ)*base66 + (165089896620627/12500000000000000000000000000 : ℝ)*base68 + (1106792015676821/200000000000000000000000000000 : ℝ)*base69 + (47881090458127/12500000000000000000000000000 : ℝ)*base72 + (1048297982053211/200000000000000000000000000000 : ℝ)*base74 + (269421202076821/200000000000000000000000000000 : ℝ)*base75 + (1849991976923179/200000000000000000000000000000 : ℝ)*base78 + (1598374505123179/200000000000000000000000000000 : ℝ)*base80 + (485633042176821/100000000000000000000000000000 : ℝ)*base81 + (13865581/2000000000000000000000 : ℝ)*base89 + (13865581/2000000000000000000000 : ℝ)*base91 + (6134419/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1522_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (591/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5071/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1522_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1522_s1_0 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-45658137/250000000 : ℝ)*x 0 + (5563948237/10000000000 : ℝ)*x 1 + (79744833/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45658137/250000000 : ℝ)^4541 ≤ (11132208232211/100000000000000 : ℝ)^3517 := by
    have hnat : (45658137 : ℕ)^4541*100000000000000^3517 ≤ 11132208232211^3517*250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45658137 250000000 11132208232211 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5563948237/10000000000 : ℝ)^4541 ≤ (11727070369561/25000000000000 : ℝ)^3517 := by
    have hnat : (5563948237 : ℕ)^4541*25000000000000^3517 ≤ 11727070369561^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563948237 10000000000 11727070369561 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79744833/156250000 : ℝ)^4541 ≤ (167838041097/400000000000 : ℝ)^3517 := by
    have hnat : (79744833 : ℕ)^4541*400000000000^3517 ≤ 167838041097^3517*156250000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79744833 156250000 167838041097 400000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45658137/250000000 : ℝ), (5563948237/10000000000 : ℝ), (79744833/156250000 : ℝ)] ![(11132208232211/100000000000000 : ℝ), (11727070369561/25000000000000 : ℝ), (167838041097/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45658137/250000000 : ℝ)|^4541 ≤ (11132208232211/100000000000000 : ℝ)^3517
        have hw : |(-45658137/250000000 : ℝ)|=(45658137/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5563948237/10000000000 : ℝ)|^4541 ≤ (11727070369561/25000000000000 : ℝ)^3517
        have hw : |(5563948237/10000000000 : ℝ)|=(5563948237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79744833/156250000 : ℝ)|^4541 ≤ (167838041097/400000000000 : ℝ)^3517
        have hw : |(79744833/156250000 : ℝ)|=(79744833/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_1 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692404741/5000000000 : ℝ)*x 0 + (-2068394057/10000000000 : ℝ)*x 1 + (5103670187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692404741/5000000000 : ℝ)^4541 ≤ (11241872380151/25000000000000 : ℝ)^3517 := by
    have hnat : (2692404741 : ℕ)^4541*25000000000000^3517 ≤ 11241872380151^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692404741 5000000000 11241872380151 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068394057/10000000000 : ℝ)^4541 ≤ (6536495449523/50000000000000 : ℝ)^3517 := by
    have hnat : (2068394057 : ℕ)^4541*50000000000000^3517 ≤ 6536495449523^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068394057 10000000000 6536495449523 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5103670187/10000000000 : ℝ)^4541 ≤ (1678380782501/4000000000000 : ℝ)^3517 := by
    have hnat : (5103670187 : ℕ)^4541*4000000000000^3517 ≤ 1678380782501^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5103670187 10000000000 1678380782501 4000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692404741/5000000000 : ℝ), (-2068394057/10000000000 : ℝ), (5103670187/10000000000 : ℝ)] ![(11241872380151/25000000000000 : ℝ), (6536495449523/50000000000000 : ℝ), (1678380782501/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692404741/5000000000 : ℝ)|^4541 ≤ (11241872380151/25000000000000 : ℝ)^3517
        have hw : |(2692404741/5000000000 : ℝ)|=(2692404741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068394057/10000000000 : ℝ)|^4541 ≤ (6536495449523/50000000000000 : ℝ)^3517
        have hw : |(-2068394057/10000000000 : ℝ)|=(2068394057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5103670187/10000000000 : ℝ)|^4541 ≤ (1678380782501/4000000000000 : ℝ)^3517
        have hw : |(5103670187/10000000000 : ℝ)|=(5103670187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_2 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384811223/10000000000 : ℝ)*x 0 + (5103668617/10000000000 : ℝ)*x 1 + (-2068393799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384811223/10000000000 : ℝ)^4541 ≤ (44967508292417/100000000000000 : ℝ)^3517 := by
    have hnat : (5384811223 : ℕ)^4541*100000000000000^3517 ≤ 44967508292417^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384811223 10000000000 44967508292417 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5103668617/10000000000 : ℝ)^4541 ≤ (20979751448353/50000000000000 : ℝ)^3517 := by
    have hnat : (5103668617 : ℕ)^4541*50000000000000^3517 ≤ 20979751448353^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5103668617 10000000000 20979751448353 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068393799/10000000000 : ℝ)^4541 ≤ (13072988793617/100000000000000 : ℝ)^3517 := by
    have hnat : (2068393799 : ℕ)^4541*100000000000000^3517 ≤ 13072988793617^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068393799 10000000000 13072988793617 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384811223/10000000000 : ℝ), (5103668617/10000000000 : ℝ), (-2068393799/10000000000 : ℝ)] ![(44967508292417/100000000000000 : ℝ), (20979751448353/50000000000000 : ℝ), (13072988793617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384811223/10000000000 : ℝ)|^4541 ≤ (44967508292417/100000000000000 : ℝ)^3517
        have hw : |(5384811223/10000000000 : ℝ)|=(5384811223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5103668617/10000000000 : ℝ)|^4541 ≤ (20979751448353/50000000000000 : ℝ)^3517
        have hw : |(5103668617/10000000000 : ℝ)|=(5103668617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068393799/10000000000 : ℝ)|^4541 ≤ (13072988793617/100000000000000 : ℝ)^3517
        have hw : |(-2068393799/10000000000 : ℝ)|=(2068393799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_3 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061490751/2500000000 : ℝ)*x 0 + (3747664443/10000000000 : ℝ)*x 1 + (2399372497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061490751/2500000000 : ℝ)^4541 ≤ (33087106243779/100000000000000 : ℝ)^3517 := by
    have hnat : (1061490751 : ℕ)^4541*100000000000000^3517 ≤ 33087106243779^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061490751 2500000000 33087106243779 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3747664443/10000000000 : ℝ)^4541 ≤ (3520205800143/12500000000000 : ℝ)^3517 := by
    have hnat : (3747664443 : ℕ)^4541*12500000000000^3517 ≤ 3520205800143^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3747664443 10000000000 3520205800143 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2399372497/5000000000 : ℝ)^4541 ≤ (19375623671983/50000000000000 : ℝ)^3517 := by
    have hnat : (2399372497 : ℕ)^4541*50000000000000^3517 ≤ 19375623671983^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399372497 5000000000 19375623671983 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061490751/2500000000 : ℝ), (3747664443/10000000000 : ℝ), (2399372497/5000000000 : ℝ)] ![(33087106243779/100000000000000 : ℝ), (3520205800143/12500000000000 : ℝ), (19375623671983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061490751/2500000000 : ℝ)|^4541 ≤ (33087106243779/100000000000000 : ℝ)^3517
        have hw : |(1061490751/2500000000 : ℝ)|=(1061490751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3747664443/10000000000 : ℝ)|^4541 ≤ (3520205800143/12500000000000 : ℝ)^3517
        have hw : |(3747664443/10000000000 : ℝ)|=(3747664443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2399372497/5000000000 : ℝ)|^4541 ≤ (19375623671983/50000000000000 : ℝ)^3517
        have hw : |(2399372497/5000000000 : ℝ)|=(2399372497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_4 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1826609021/10000000000 : ℝ)*x 0 + (2554372483/5000000000 : ℝ)*x 1 + (5558792183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826609021/10000000000 : ℝ)^4541 ≤ (11134439789079/100000000000000 : ℝ)^3517 := by
    have hnat : (1826609021 : ℕ)^4541*100000000000000^3517 ≤ 11134439789079^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826609021 10000000000 11134439789079 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2554372483/5000000000 : ℝ)^4541 ≤ (42013397010961/100000000000000 : ℝ)^3517 := by
    have hnat : (2554372483 : ℕ)^4541*100000000000000^3517 ≤ 42013397010961^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2554372483 5000000000 42013397010961 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5558792183/10000000000 : ℝ)^4541 ≤ (46852163188577/100000000000000 : ℝ)^3517 := by
    have hnat : (5558792183 : ℕ)^4541*100000000000000^3517 ≤ 46852163188577^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558792183 10000000000 46852163188577 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1826609021/10000000000 : ℝ), (2554372483/5000000000 : ℝ), (5558792183/10000000000 : ℝ)] ![(11134439789079/100000000000000 : ℝ), (42013397010961/100000000000000 : ℝ), (46852163188577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1826609021/10000000000 : ℝ)|^4541 ≤ (11134439789079/100000000000000 : ℝ)^3517
        have hw : |(-1826609021/10000000000 : ℝ)|=(1826609021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2554372483/5000000000 : ℝ)|^4541 ≤ (42013397010961/100000000000000 : ℝ)^3517
        have hw : |(2554372483/5000000000 : ℝ)|=(2554372483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5558792183/10000000000 : ℝ)|^4541 ≤ (46852163188577/100000000000000 : ℝ)^3517
        have hw : |(5558792183/10000000000 : ℝ)|=(5558792183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_5 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631716269/5000000000 : ℝ)*x 0 + (-1613270407/10000000000 : ℝ)*x 1 + (5558792327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631716269/5000000000 : ℝ)^4541 ≤ (21831548212147/50000000000000 : ℝ)^3517 := by
    have hnat : (2631716269 : ℕ)^4541*50000000000000^3517 ≤ 21831548212147^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631716269 5000000000 21831548212147 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1613270407/10000000000 : ℝ)^4541 ≤ (9484738812609/100000000000000 : ℝ)^3517 := by
    have hnat : (1613270407 : ℕ)^4541*100000000000000^3517 ≤ 9484738812609^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613270407 10000000000 9484738812609 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5558792327/10000000000 : ℝ)^4541 ≤ (5856520594457/12500000000000 : ℝ)^3517 := by
    have hnat : (5558792327 : ℕ)^4541*12500000000000^3517 ≤ 5856520594457^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558792327 10000000000 5856520594457 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631716269/5000000000 : ℝ), (-1613270407/10000000000 : ℝ), (5558792327/10000000000 : ℝ)] ![(21831548212147/50000000000000 : ℝ), (9484738812609/100000000000000 : ℝ), (5856520594457/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631716269/5000000000 : ℝ)|^4541 ≤ (21831548212147/50000000000000 : ℝ)^3517
        have hw : |(2631716269/5000000000 : ℝ)|=(2631716269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1613270407/10000000000 : ℝ)|^4541 ≤ (9484738812609/100000000000000 : ℝ)^3517
        have hw : |(-1613270407/10000000000 : ℝ)|=(1613270407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5558792327/10000000000 : ℝ)|^4541 ≤ (5856520594457/12500000000000 : ℝ)^3517
        have hw : |(5558792327/10000000000 : ℝ)|=(5558792327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_6 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315858061/2500000000 : ℝ)*x 0 + (555879249/1000000000 : ℝ)*x 1 + (-1613270587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315858061/2500000000 : ℝ)^4541 ≤ (436630932753/1000000000000 : ℝ)^3517 := by
    have hnat : (1315858061 : ℕ)^4541*1000000000000^3517 ≤ 436630932753^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315858061 2500000000 436630932753 1000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555879249/1000000000 : ℝ)^4541 ≤ (23426083264751/50000000000000 : ℝ)^3517 := by
    have hnat : (555879249 : ℕ)^4541*50000000000000^3517 ≤ 23426083264751^3517*1000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555879249 1000000000 23426083264751 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1613270587/10000000000 : ℝ)^4541 ≤ (1185592522373/12500000000000 : ℝ)^3517 := by
    have hnat : (1613270587 : ℕ)^4541*12500000000000^3517 ≤ 1185592522373^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613270587 10000000000 1185592522373 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315858061/2500000000 : ℝ), (555879249/1000000000 : ℝ), (-1613270587/10000000000 : ℝ)] ![(436630932753/1000000000000 : ℝ), (23426083264751/50000000000000 : ℝ), (1185592522373/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315858061/2500000000 : ℝ)|^4541 ≤ (436630932753/1000000000000 : ℝ)^3517
        have hw : |(1315858061/2500000000 : ℝ)|=(1315858061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(555879249/1000000000 : ℝ)|^4541 ≤ (23426083264751/50000000000000 : ℝ)^3517
        have hw : |(555879249/1000000000 : ℝ)|=(555879249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1613270587/10000000000 : ℝ)|^4541 ≤ (1185592522373/12500000000000 : ℝ)^3517
        have hw : |(-1613270587/10000000000 : ℝ)|=(1613270587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s1_7 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123305733/5000000000 : ℝ)*x 0 + (2393577241/5000000000 : ℝ)*x 1 + (11748243/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123305733/5000000000 : ℝ)^4541 ≤ (33093630873959/100000000000000 : ℝ)^3517 := by
    have hnat : (2123305733 : ℕ)^4541*100000000000000^3517 ≤ 33093630873959^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123305733 5000000000 33093630873959 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2393577241/5000000000 : ℝ)^4541 ≤ (38630441776863/100000000000000 : ℝ)^3517 := by
    have hnat : (2393577241 : ℕ)^4541*100000000000000^3517 ≤ 38630441776863^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2393577241 5000000000 38630441776863 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11748243/31250000 : ℝ)^4541 ≤ (14137963662193/50000000000000 : ℝ)^3517 := by
    have hnat : (11748243 : ℕ)^4541*50000000000000^3517 ≤ 14137963662193^3517*31250000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11748243 31250000 14137963662193 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123305733/5000000000 : ℝ), (2393577241/5000000000 : ℝ), (11748243/31250000 : ℝ)] ![(33093630873959/100000000000000 : ℝ), (38630441776863/100000000000000 : ℝ), (14137963662193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123305733/5000000000 : ℝ)|^4541 ≤ (33093630873959/100000000000000 : ℝ)^3517
        have hw : |(2123305733/5000000000 : ℝ)|=(2123305733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2393577241/5000000000 : ℝ)|^4541 ≤ (38630441776863/100000000000000 : ℝ)^3517
        have hw : |(2393577241/5000000000 : ℝ)|=(2393577241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11748243/31250000 : ℝ)|^4541 ≤ (14137963662193/50000000000000 : ℝ)^3517
        have hw : |(11748243/31250000 : ℝ)|=(11748243/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1522_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5071/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (591/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1061/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9113/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5071/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (591/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5071/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (591/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5071/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (591/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5071/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (591/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5071/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (591/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5071/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (591/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (591/20000 : ℝ) ^ (4539/1024 : ℝ) ≤ (3323508679903/20000000000000000000 : ℝ) := by
    have hpowers : (591/20000 : ℝ)^4539 ≤ (3323508679903/20000000000000000000 : ℝ)^1024 := by
      have hnat : (591 : ℕ)^4539*20000000000000000000^1024 ≤ 3323508679903^1024*20000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        591 20000 3323508679903 20000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (591/20000 : ℝ)) (X := (3323508679903/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5071/20000 : ℝ) ^ (4539/1024 : ℝ) ≤ (228266477306698841/100000000000000000000 : ℝ) := by
    have hpowers : (5071/20000 : ℝ)^4539 ≤ (228266477306698841/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5071 : ℕ)^4539*100000000000000000000^1024 ≤ 228266477306698841^1024*20000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5071 20000 228266477306698841 100000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5071/20000 : ℝ)) (X := (228266477306698841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000003323508679903/10000000000000000000 : ℝ) ≤ (5000000374892317/5000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (10000003323508679903/10000000000000000000 : ℝ)^1024 ≤ (5000000374892317/5000000000000000 : ℝ)^4539 := by
      have hnat : (10000003323508679903 : ℕ)^1024*5000000000000000^4539 ≤ 5000000374892317^4539*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000003323508679903 10000000000000000000 5000000374892317 5000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000374892317/5000000000000000 : ℝ)) (X := (10000003323508679903/10000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25057070773712524589/25000000000000000000 : ℝ) ≤ (10005145528592109/10000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (25057070773712524589/25000000000000000000 : ℝ)^1024 ≤ (10005145528592109/10000000000000000 : ℝ)^4539 := by
      have hnat : (25057070773712524589 : ℕ)^1024*10000000000000000^4539 ≤ 10005145528592109^4539*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25057070773712524589 25000000000000000000 10005145528592109 10000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005145528592109/10000000000000000 : ℝ)) (X := (25057070773712524589/25000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50228266477306698841/50000000000000000000 : ℝ) ≤ (312821572106237/312500000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (50228266477306698841/50000000000000000000 : ℝ)^1024 ≤ (312821572106237/312500000000000 : ℝ)^4539 := by
      have hnat : (50228266477306698841 : ℕ)^1024*312500000000000^4539 ≤ 312821572106237^4539*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50228266477306698841 50000000000000000000 312821572106237 312500000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312821572106237/312500000000000 : ℝ)) (X := (50228266477306698841/50000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3323508679903/20000000000000000000 : ℝ) ≤ ((4479392223048472487/4480000000000000000 : ℝ)+2*(205791152299/89600000000000 : ℝ)*(591/20000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (4479392223048472487/4480000000000000000 : ℝ)+2*(205791152299/89600000000000 : ℝ)*(591/20000 : ℝ)=(5000000374892317/5000000000000000 : ℝ) by norm_num, show 1+2*(3323508679903/20000000000000000000 : ℝ)=(10000003323508679903/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(228266477306698841/100000000000000000000 : ℝ)+(3323508679903/20000000000000000000 : ℝ) ≤ ((4479392223048472487/4480000000000000000 : ℝ)+(205791152299/89600000000000 : ℝ)*((5071/20000 : ℝ)+(591/20000 : ℝ)))^(4539/1024 : ℝ) := by
    rw [show (4479392223048472487/4480000000000000000 : ℝ)+(205791152299/89600000000000 : ℝ)*((5071/20000 : ℝ)+(591/20000 : ℝ))=(10005145528592109/10000000000000000 : ℝ) by norm_num, show 1+(228266477306698841/100000000000000000000 : ℝ)+(3323508679903/20000000000000000000 : ℝ)=(25057070773712524589/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(228266477306698841/100000000000000000000 : ℝ) ≤ ((4479392223048472487/4480000000000000000 : ℝ)+2*(205791152299/89600000000000 : ℝ)*(5071/20000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (4479392223048472487/4480000000000000000 : ℝ)+2*(205791152299/89600000000000 : ℝ)*(5071/20000 : ℝ)=(312821572106237/312500000000000 : ℝ) by norm_num, show 1+2*(228266477306698841/100000000000000000000 : ℝ)=(50228266477306698841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4479392223048472487/4480000000000000000 : ℝ)*(X 1 0+X 2 0)+(205791152299/89600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (591/20000 : ℝ)) (hi := (5071/20000 : ℝ)) (c := (4479392223048472487/4480000000000000000 : ℝ)) (alpha := (205791152299/89600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4479392223048472487/4480000000000000000 : ℝ)*(X 0 1+X 2 1)+(205791152299/89600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (591/20000 : ℝ)) (hi := (5071/20000 : ℝ)) (c := (4479392223048472487/4480000000000000000 : ℝ)) (alpha := (205791152299/89600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4479392223048472487/4480000000000000000 : ℝ)*(X 0 2+X 1 2)+(205791152299/89600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (591/20000 : ℝ)) (hi := (5071/20000 : ℝ)) (c := (4479392223048472487/4480000000000000000 : ℝ)) (alpha := (205791152299/89600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-45658137/250000000 : ℝ)*X 0 0+(5563948237/10000000000 : ℝ)*X 0 1+(79744833/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2692404741/5000000000 : ℝ)*X 1 0+(-2068394057/10000000000 : ℝ)*X 1 1+(5103670187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5384811223/10000000000 : ℝ)*X 2 0+(5103668617/10000000000 : ℝ)*X 2 1+(-2068393799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061490751/2500000000 : ℝ)*X 0 0+(3747664443/10000000000 : ℝ)*X 0 1+(2399372497/5000000000 : ℝ)*X 0 2+(1061490751/2500000000 : ℝ)*X 1 0+(3747664443/10000000000 : ℝ)*X 1 1+(2399372497/5000000000 : ℝ)*X 1 2+(1061490751/2500000000 : ℝ)*X 2 0+(3747664443/10000000000 : ℝ)*X 2 1+(2399372497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1826609021/10000000000 : ℝ)*X 0 0+(2554372483/5000000000 : ℝ)*X 0 1+(5558792183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2631716269/5000000000 : ℝ)*X 1 0+(-1613270407/10000000000 : ℝ)*X 1 1+(5558792327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1315858061/2500000000 : ℝ)*X 2 0+(555879249/1000000000 : ℝ)*X 2 1+(-1613270587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123305733/5000000000 : ℝ)*X 0 0+(2393577241/5000000000 : ℝ)*X 0 1+(11748243/31250000 : ℝ)*X 0 2+(2123305733/5000000000 : ℝ)*X 1 0+(2393577241/5000000000 : ℝ)*X 1 1+(11748243/31250000 : ℝ)*X 1 2+(2123305733/5000000000 : ℝ)*X 2 0+(2393577241/5000000000 : ℝ)*X 2 1+(11748243/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2257569641319829580984482539/224000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1094189703/100000000000000 : ℝ)*(base19) + (110948823/6250000000000 : ℝ)*(base23) + (41590537/100000000000000 : ℝ)*(upper3) + (11551841/100000000000000 : ℝ)*(upper4) + (299040141/100000000000000 : ℝ)*(upper5) + (781008136260493/50000000000000 : ℝ)*(major0) + (781008136260493/50000000000000 : ℝ)*(major1) + (1562016272520987/100000000000000 : ℝ)*(major2) + (43452092236989/2000000000000 : ℝ)*(sp0) + (108630927619597/5000000000000 : ℝ)*(sp1) + (543154467850119/25000000000000 : ℝ)*(sp2) + (951407446558091/100000000000000 : ℝ)*(sp3) + (15034732193/100000000000000 : ℝ)*(sp4) + (5115954369/100000000000000 : ℝ)*(sp7) + (47570628125623/5000000000000 : ℝ)*(f.failure) + (2172619646581643/100000000000000 : ℝ)*(f.sum) + (29468105511527/8960000000000000000000000000 : ℝ)*base65 + (1103631768062618909/224000000000000000000000000000000 : ℝ)*base68 + (3056526010716284669/448000000000000000000000000000000 : ℝ)*base69 + (490657960801381091/224000000000000000000000000000000 : ℝ)*base71 + (5212724289433/8960000000000000000000000000 : ℝ)*base74 + (1156483167388284669/448000000000000000000000000000000 : ℝ)*base75 + (2112879441238093909/224000000000000000000000000000000 : ℝ)*base78 + (754016906166093909/224000000000000000000000000000000 : ℝ)*base80 + (9491043506607/2240000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (172081/500000000000000000000 : ℝ)*base89 + (172081/500000000000000000000 : ℝ)*base91 + (4827919/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135397100658567054640029927/16000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1638307261/100000000000000 : ℝ)*(base19) + (3343979/200000000000 : ℝ)*(base23) + (224511647/100000000000000 : ℝ)*(upper3) + (71971531/100000000000000 : ℝ)*(lower4) + (5303833/4000000000000 : ℝ)*(upper5) + (798754508099983/50000000000000 : ℝ)*(major0) + (798754508099983/50000000000000 : ℝ)*(major1) + (798754508099983/50000000000000 : ℝ)*(major2) + (11757090963/100000000000000 : ℝ)*(sp1) + (2534001031/20000000000000 : ℝ)*(sp2) + (2221986820058013/100000000000000 : ℝ)*(sp4) + (555493356164947/25000000000000 : ℝ)*(sp5) + (2221972478063357/100000000000000 : ℝ)*(sp6) + (48651546513231/5000000000000 : ℝ)*(sp7) + (48651546513231/5000000000000 : ℝ)*(f.failure) + (2221986820058013/100000000000000 : ℝ)*(f.sum) + (6743402418363/2240000000000000000000000000 : ℝ)*base66 + (1675225732785482279/224000000000000000000000000000000 : ℝ)*base68 + (949851949329482279/224000000000000000000000000000000 : ℝ)*base70 + (307075538353482279/224000000000000000000000000000000 : ℝ)*base72 + (2624330451003/2240000000000000000000000000 : ℝ)*base74 + (2195102530001482279/224000000000000000000000000000000 : ℝ)*base76 + (751098320465482279/224000000000000000000000000000000 : ℝ)*base78 + (263084262353482279/224000000000000000000000000000000 : ℝ)*base80 + (3711933887877/2240000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3178457/500000000000000000000 : ℝ)*base89 + (3178457/500000000000000000000 : ℝ)*base91 + (3178457/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1522_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5071/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (591/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1061/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9113/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1522_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1522_s2_0 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-462428881/2500000000 : ℝ)*x 0 + (545478959/1000000000 : ℝ)*x 1 + (1039532253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (462428881/2500000000 : ℝ)^4541 ≤ (11316633256357/100000000000000 : ℝ)^3517 := by
    have hnat : (462428881 : ℕ)^4541*100000000000000^3517 ≤ 11316633256357^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462428881 2500000000 11316633256357 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545478959/1000000000 : ℝ)^4541 ≤ (2857715768399/6250000000000 : ℝ)^3517 := by
    have hnat : (545478959 : ℕ)^4541*6250000000000^3517 ≤ 2857715768399^3517*1000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545478959 1000000000 2857715768399 6250000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039532253/2000000000 : ℝ)^4541 ≤ (21479957214347/50000000000000 : ℝ)^3517 := by
    have hnat : (1039532253 : ℕ)^4541*50000000000000^3517 ≤ 21479957214347^3517*2000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039532253 2000000000 21479957214347 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-462428881/2500000000 : ℝ), (545478959/1000000000 : ℝ), (1039532253/2000000000 : ℝ)] ![(11316633256357/100000000000000 : ℝ), (2857715768399/6250000000000 : ℝ), (21479957214347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-462428881/2500000000 : ℝ)|^4541 ≤ (11316633256357/100000000000000 : ℝ)^3517
        have hw : |(-462428881/2500000000 : ℝ)|=(462428881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545478959/1000000000 : ℝ)|^4541 ≤ (2857715768399/6250000000000 : ℝ)^3517
        have hw : |(545478959/1000000000 : ℝ)|=(545478959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039532253/2000000000 : ℝ)|^4541 ≤ (21479957214347/50000000000000 : ℝ)^3517
        have hw : |(1039532253/2000000000 : ℝ)|=(1039532253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_1 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669623689/1250000000 : ℝ)*x 0 + (-495500909/2500000000 : ℝ)*x 1 + (2598830897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669623689/1250000000 : ℝ)^4541 ≤ (8933550977223/20000000000000 : ℝ)^3517 := by
    have hnat : (669623689 : ℕ)^4541*20000000000000^3517 ≤ 8933550977223^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669623689 1250000000 8933550977223 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495500909/2500000000 : ℝ)^4541 ≤ (12372325015987/100000000000000 : ℝ)^3517 := by
    have hnat : (495500909 : ℕ)^4541*100000000000000^3517 ≤ 12372325015987^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495500909 2500000000 12372325015987 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598830897/5000000000 : ℝ)^4541 ≤ (10739980018509/25000000000000 : ℝ)^3517 := by
    have hnat : (2598830897 : ℕ)^4541*25000000000000^3517 ≤ 10739980018509^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598830897 5000000000 10739980018509 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669623689/1250000000 : ℝ), (-495500909/2500000000 : ℝ), (2598830897/5000000000 : ℝ)] ![(8933550977223/20000000000000 : ℝ), (12372325015987/100000000000000 : ℝ), (10739980018509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669623689/1250000000 : ℝ)|^4541 ≤ (8933550977223/20000000000000 : ℝ)^3517
        have hw : |(669623689/1250000000 : ℝ)|=(669623689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495500909/2500000000 : ℝ)|^4541 ≤ (12372325015987/100000000000000 : ℝ)^3517
        have hw : |(-495500909/2500000000 : ℝ)|=(495500909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598830897/5000000000 : ℝ)|^4541 ≤ (10739980018509/25000000000000 : ℝ)^3517
        have hw : |(2598830897/5000000000 : ℝ)|=(2598830897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_2 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669623787/1250000000 : ℝ)*x 0 + (5197661313/10000000000 : ℝ)*x 1 + (-1982003227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669623787/1250000000 : ℝ)^4541 ≤ (22333881663311/50000000000000 : ℝ)^3517 := by
    have hnat : (669623787 : ℕ)^4541*50000000000000^3517 ≤ 22333881663311^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669623787 1250000000 22333881663311 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5197661313/10000000000 : ℝ)^4541 ≤ (42959914940937/100000000000000 : ℝ)^3517 := by
    have hnat : (5197661313 : ℕ)^4541*100000000000000^3517 ≤ 42959914940937^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197661313 10000000000 42959914940937 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982003227/10000000000 : ℝ)^4541 ≤ (3093080429879/25000000000000 : ℝ)^3517 := by
    have hnat : (1982003227 : ℕ)^4541*25000000000000^3517 ≤ 3093080429879^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982003227 10000000000 3093080429879 25000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669623787/1250000000 : ℝ), (5197661313/10000000000 : ℝ), (-1982003227/10000000000 : ℝ)] ![(22333881663311/50000000000000 : ℝ), (42959914940937/100000000000000 : ℝ), (3093080429879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669623787/1250000000 : ℝ)|^4541 ≤ (22333881663311/50000000000000 : ℝ)^3517
        have hw : |(669623787/1250000000 : ℝ)|=(669623787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5197661313/10000000000 : ℝ)|^4541 ≤ (42959914940937/100000000000000 : ℝ)^3517
        have hw : |(5197661313/10000000000 : ℝ)|=(5197661313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1982003227/10000000000 : ℝ)|^4541 ≤ (3093080429879/25000000000000 : ℝ)^3517
        have hw : |(-1982003227/10000000000 : ℝ)|=(1982003227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_3 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4262784401/10000000000 : ℝ)*x 0 + (3977703423/10000000000 : ℝ)*x 1 + (4564875929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262784401/10000000000 : ℝ)^4541 ≤ (6651290370953/20000000000000 : ℝ)^3517 := by
    have hnat : (4262784401 : ℕ)^4541*20000000000000^3517 ≤ 6651290370953^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262784401 10000000000 6651290370953 20000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3977703423/10000000000 : ℝ)^4541 ≤ (30413224997523/100000000000000 : ℝ)^3517 := by
    have hnat : (3977703423 : ℕ)^4541*100000000000000^3517 ≤ 30413224997523^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977703423 10000000000 30413224997523 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564875929/10000000000 : ℝ)^4541 ≤ (227064519589/625000000000 : ℝ)^3517 := by
    have hnat : (4564875929 : ℕ)^4541*625000000000^3517 ≤ 227064519589^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564875929 10000000000 227064519589 625000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262784401/10000000000 : ℝ), (3977703423/10000000000 : ℝ), (4564875929/10000000000 : ℝ)] ![(6651290370953/20000000000000 : ℝ), (30413224997523/100000000000000 : ℝ), (227064519589/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262784401/10000000000 : ℝ)|^4541 ≤ (6651290370953/20000000000000 : ℝ)^3517
        have hw : |(4262784401/10000000000 : ℝ)|=(4262784401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3977703423/10000000000 : ℝ)|^4541 ≤ (30413224997523/100000000000000 : ℝ)^3517
        have hw : |(3977703423/10000000000 : ℝ)|=(3977703423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564875929/10000000000 : ℝ)|^4541 ≤ (227064519589/625000000000 : ℝ)^3517
        have hw : |(4564875929/10000000000 : ℝ)|=(4564875929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_4 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-924881961/5000000000 : ℝ)*x 0 + (2599627269/5000000000 : ℝ)*x 1 + (681647887/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924881961/5000000000 : ℝ)^4541 ≤ (5658507785311/50000000000000 : ℝ)^3517 := by
    have hnat : (924881961 : ℕ)^4541*50000000000000^3517 ≤ 5658507785311^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924881961 5000000000 5658507785311 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2599627269/5000000000 : ℝ)^4541 ≤ (21488459078237/50000000000000 : ℝ)^3517 := by
    have hnat : (2599627269 : ℕ)^4541*50000000000000^3517 ≤ 21488459078237^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599627269 5000000000 21488459078237 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681647887/1250000000 : ℝ)^4541 ≤ (22853033128073/50000000000000 : ℝ)^3517 := by
    have hnat : (681647887 : ℕ)^4541*50000000000000^3517 ≤ 22853033128073^3517*1250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681647887 1250000000 22853033128073 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-924881961/5000000000 : ℝ), (2599627269/5000000000 : ℝ), (681647887/1250000000 : ℝ)] ![(5658507785311/50000000000000 : ℝ), (21488459078237/50000000000000 : ℝ), (22853033128073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-924881961/5000000000 : ℝ)|^4541 ≤ (5658507785311/50000000000000 : ℝ)^3517
        have hw : |(-924881961/5000000000 : ℝ)|=(924881961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2599627269/5000000000 : ℝ)|^4541 ≤ (21488459078237/50000000000000 : ℝ)^3517
        have hw : |(2599627269/5000000000 : ℝ)|=(2599627269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681647887/1250000000 : ℝ)|^4541 ≤ (22853033128073/50000000000000 : ℝ)^3517
        have hw : |(681647887/1250000000 : ℝ)|=(681647887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_5 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322343679/2500000000 : ℝ)*x 0 + (-1726482619/10000000000 : ℝ)*x 1 + (545318377/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322343679/2500000000 : ℝ)^4541 ≤ (21970579384523/50000000000000 : ℝ)^3517 := by
    have hnat : (1322343679 : ℕ)^4541*50000000000000^3517 ≤ 21970579384523^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322343679 2500000000 21970579384523 50000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1726482619/10000000000 : ℝ)^4541 ≤ (414110706857/4000000000000 : ℝ)^3517 := by
    have hnat : (1726482619 : ℕ)^4541*4000000000000^3517 ≤ 414110706857^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726482619 10000000000 414110706857 4000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545318377/1000000000 : ℝ)^4541 ≤ (45706073550097/100000000000000 : ℝ)^3517 := by
    have hnat : (545318377 : ℕ)^4541*100000000000000^3517 ≤ 45706073550097^3517*1000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545318377 1000000000 45706073550097 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322343679/2500000000 : ℝ), (-1726482619/10000000000 : ℝ), (545318377/1000000000 : ℝ)] ![(21970579384523/50000000000000 : ℝ), (414110706857/4000000000000 : ℝ), (45706073550097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322343679/2500000000 : ℝ)|^4541 ≤ (21970579384523/50000000000000 : ℝ)^3517
        have hw : |(1322343679/2500000000 : ℝ)|=(1322343679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1726482619/10000000000 : ℝ)|^4541 ≤ (414110706857/4000000000000 : ℝ)^3517
        have hw : |(-1726482619/10000000000 : ℝ)|=(1726482619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545318377/1000000000 : ℝ)|^4541 ≤ (45706073550097/100000000000000 : ℝ)^3517
        have hw : |(545318377/1000000000 : ℝ)|=(545318377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_6 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644687741/5000000000 : ℝ)*x 0 + (136329587/250000000 : ℝ)*x 1 + (-1726481963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644687741/5000000000 : ℝ)^4541 ≤ (43941166985323/100000000000000 : ℝ)^3517 := by
    have hnat : (2644687741 : ℕ)^4541*100000000000000^3517 ≤ 43941166985323^3517*5000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644687741 5000000000 43941166985323 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136329587/250000000 : ℝ)^4541 ≤ (182824281647/400000000000 : ℝ)^3517 := by
    have hnat : (136329587 : ℕ)^4541*400000000000^3517 ≤ 182824281647^3517*250000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136329587 250000000 182824281647 400000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1726481963/10000000000 : ℝ)^4541 ≤ (10352762592437/100000000000000 : ℝ)^3517 := by
    have hnat : (1726481963 : ℕ)^4541*100000000000000^3517 ≤ 10352762592437^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726481963 10000000000 10352762592437 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644687741/5000000000 : ℝ), (136329587/250000000 : ℝ), (-1726481963/10000000000 : ℝ)] ![(43941166985323/100000000000000 : ℝ), (182824281647/400000000000 : ℝ), (10352762592437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644687741/5000000000 : ℝ)|^4541 ≤ (43941166985323/100000000000000 : ℝ)^3517
        have hw : |(2644687741/5000000000 : ℝ)|=(2644687741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136329587/250000000 : ℝ)|^4541 ≤ (182824281647/400000000000 : ℝ)^3517
        have hw : |(136329587/250000000 : ℝ)|=(136329587/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1726481963/10000000000 : ℝ)|^4541 ≤ (10352762592437/100000000000000 : ℝ)^3517
        have hw : |(-1726481963/10000000000 : ℝ)|=(1726481963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1522_s2_7 (p : ℝ) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4262898321/10000000000 : ℝ)*x 0 + (1140309793/2500000000 : ℝ)*x 1 + (3981371763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4262898321/10000000000 : ℝ)^4541 ≤ (4157199922863/12500000000000 : ℝ)^3517 := by
    have hnat : (4262898321 : ℕ)^4541*12500000000000^3517 ≤ 4157199922863^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262898321 10000000000 4157199922863 12500000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140309793/2500000000 : ℝ)^4541 ≤ (2268309784817/6250000000000 : ℝ)^3517 := by
    have hnat : (1140309793 : ℕ)^4541*6250000000000^3517 ≤ 2268309784817^3517*2500000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140309793 2500000000 2268309784817 6250000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3981371763/10000000000 : ℝ)^4541 ≤ (30449444049701/100000000000000 : ℝ)^3517 := by
    have hnat : (3981371763 : ℕ)^4541*100000000000000^3517 ≤ 30449444049701^3517*10000000000^4541 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3981371763 10000000000 30449444049701 100000000000000 4541 3517 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4541/1024 : ℝ)) 4541 3517 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4262898321/10000000000 : ℝ), (1140309793/2500000000 : ℝ), (3981371763/10000000000 : ℝ)] ![(4157199922863/12500000000000 : ℝ), (2268309784817/6250000000000 : ℝ), (30449444049701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4262898321/10000000000 : ℝ)|^4541 ≤ (4157199922863/12500000000000 : ℝ)^3517
        have hw : |(4262898321/10000000000 : ℝ)|=(4262898321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140309793/2500000000 : ℝ)|^4541 ≤ (2268309784817/6250000000000 : ℝ)^3517
        have hw : |(1140309793/2500000000 : ℝ)|=(1140309793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3981371763/10000000000 : ℝ)|^4541 ≤ (30449444049701/100000000000000 : ℝ)^3517
        have hw : |(3981371763/10000000000 : ℝ)|=(3981371763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1522_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1061/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2103/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (399/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9113/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1061/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9113/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1061/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9113/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1061/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9113/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1061/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9113/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1061/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9113/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1061/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1061/12500 : ℝ) ^ (4539/1024 : ℝ) ≤ (446420659312703/25000000000000000000 : ℝ) := by
    have hpowers : (1061/12500 : ℝ)^4539 ≤ (446420659312703/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1061 : ℕ)^4539*25000000000000000000^1024 ≤ 446420659312703^1024*12500^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1061 12500 446420659312703 25000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1061/12500 : ℝ)) (X := (446420659312703/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9113/50000 : ℝ) ^ (4539/1024 : ℝ) ≤ (26417872883289553/50000000000000000000 : ℝ) := by
    have hpowers : (9113/50000 : ℝ)^4539 ≤ (26417872883289553/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9113 : ℕ)^4539*50000000000000000000^1024 ≤ 26417872883289553^1024*50000^4539 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9113 50000 26417872883289553 50000000000000000000 4539 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9113/50000 : ℝ)) (X := (26417872883289553/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500446420659312703/12500000000000000000 : ℝ) ≤ (5000040284506179/5000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (12500446420659312703/12500000000000000000 : ℝ)^1024 ≤ (5000040284506179/5000000000000000 : ℝ)^4539 := by
      have hnat : (12500446420659312703 : ℕ)^1024*5000000000000000^4539 ≤ 5000040284506179^4539*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500446420659312703 12500000000000000000 5000040284506179 5000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000040284506179/5000000000000000 : ℝ)) (X := (12500446420659312703/12500000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50027310714201914959/50000000000000000000 : ℝ) ≤ (1000123200081839/1000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (50027310714201914959/50000000000000000000 : ℝ)^1024 ≤ (1000123200081839/1000000000000000 : ℝ)^4539 := by
      have hnat : (50027310714201914959 : ℕ)^1024*1000000000000000^4539 ≤ 1000123200081839^4539*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027310714201914959 50000000000000000000 1000123200081839 1000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000123200081839/1000000000000000 : ℝ)) (X := (50027310714201914959/50000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25026417872883289553/25000000000000000000 : ℝ) ≤ (5001191716312211/5000000000000000 : ℝ) ^ (4539/1024 : ℝ) := by
    have hpowers : (25026417872883289553/25000000000000000000 : ℝ)^1024 ≤ (5001191716312211/5000000000000000 : ℝ)^4539 := by
      have hnat : (25026417872883289553 : ℕ)^1024*5000000000000000^4539 ≤ 5001191716312211^4539*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026417872883289553 25000000000000000000 5001191716312211 5000000000000000 1024 4539 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001191716312211/5000000000000000 : ℝ)) (X := (25026417872883289553/25000000000000000000 : ℝ)) (by norm_num) 4539 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(446420659312703/25000000000000000000 : ℝ) ≤ ((24340309468675785743/24345000000000000000 : ℝ)+2*(71964487877/60862500000000 : ℝ)*(1061/12500 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (24340309468675785743/24345000000000000000 : ℝ)+2*(71964487877/60862500000000 : ℝ)*(1061/12500 : ℝ)=(5000040284506179/5000000000000000 : ℝ) by norm_num, show 1+2*(446420659312703/25000000000000000000 : ℝ)=(12500446420659312703/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26417872883289553/50000000000000000000 : ℝ)+(446420659312703/25000000000000000000 : ℝ) ≤ ((24340309468675785743/24345000000000000000 : ℝ)+(71964487877/60862500000000 : ℝ)*((9113/50000 : ℝ)+(1061/12500 : ℝ)))^(4539/1024 : ℝ) := by
    rw [show (24340309468675785743/24345000000000000000 : ℝ)+(71964487877/60862500000000 : ℝ)*((9113/50000 : ℝ)+(1061/12500 : ℝ))=(1000123200081839/1000000000000000 : ℝ) by norm_num, show 1+(26417872883289553/50000000000000000000 : ℝ)+(446420659312703/25000000000000000000 : ℝ)=(50027310714201914959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26417872883289553/50000000000000000000 : ℝ) ≤ ((24340309468675785743/24345000000000000000 : ℝ)+2*(71964487877/60862500000000 : ℝ)*(9113/50000 : ℝ))^(4539/1024 : ℝ) := by
    rw [show (24340309468675785743/24345000000000000000 : ℝ)+2*(71964487877/60862500000000 : ℝ)*(9113/50000 : ℝ)=(5001191716312211/5000000000000000 : ℝ) by norm_num, show 1+2*(26417872883289553/50000000000000000000 : ℝ)=(25026417872883289553/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24340309468675785743/24345000000000000000 : ℝ)*(X 1 0+X 2 0)+(71964487877/60862500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (1061/12500 : ℝ)) (hi := (9113/50000 : ℝ)) (c := (24340309468675785743/24345000000000000000 : ℝ)) (alpha := (71964487877/60862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24340309468675785743/24345000000000000000 : ℝ)*(X 0 1+X 2 1)+(71964487877/60862500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (1061/12500 : ℝ)) (hi := (9113/50000 : ℝ)) (c := (24340309468675785743/24345000000000000000 : ℝ)) (alpha := (71964487877/60862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24340309468675785743/24345000000000000000 : ℝ)*(X 0 2+X 1 2)+(71964487877/60862500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4539/1024 : ℝ)) (lo := (1061/12500 : ℝ)) (hi := (9113/50000 : ℝ)) (c := (24340309468675785743/24345000000000000000 : ℝ)) (alpha := (71964487877/60862500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-462428881/2500000000 : ℝ)*X 0 0+(545478959/1000000000 : ℝ)*X 0 1+(1039532253/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669623689/1250000000 : ℝ)*X 1 0+(-495500909/2500000000 : ℝ)*X 1 1+(2598830897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669623787/1250000000 : ℝ)*X 2 0+(5197661313/10000000000 : ℝ)*X 2 1+(-1982003227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4262784401/10000000000 : ℝ)*X 0 0+(3977703423/10000000000 : ℝ)*X 0 1+(4564875929/10000000000 : ℝ)*X 0 2+(4262784401/10000000000 : ℝ)*X 1 0+(3977703423/10000000000 : ℝ)*X 1 1+(4564875929/10000000000 : ℝ)*X 1 2+(4262784401/10000000000 : ℝ)*X 2 0+(3977703423/10000000000 : ℝ)*X 2 1+(4564875929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-924881961/5000000000 : ℝ)*X 0 0+(2599627269/5000000000 : ℝ)*X 0 1+(681647887/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322343679/2500000000 : ℝ)*X 1 0+(-1726482619/10000000000 : ℝ)*X 1 1+(545318377/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644687741/5000000000 : ℝ)*X 2 0+(136329587/250000000 : ℝ)*X 2 1+(-1726481963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4262898321/10000000000 : ℝ)*X 0 0+(1140309793/2500000000 : ℝ)*X 0 1+(3981371763/10000000000 : ℝ)*X 0 2+(4262898321/10000000000 : ℝ)*X 1 0+(1140309793/2500000000 : ℝ)*X 1 1+(3981371763/10000000000 : ℝ)*X 1 2+(4262898321/10000000000 : ℝ)*X 2 0+(1140309793/2500000000 : ℝ)*X 2 1+(3981371763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1522_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (343256565321563176339842603/33812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2028783379/100000000000000 : ℝ)*(base19) + (463920751/20000000000000 : ℝ)*(base23) + (80540417/50000000000000 : ℝ)*(upper3) + (29823821/20000000000000 : ℝ)*(upper4) + (40135143/10000000000000 : ℝ)*(upper5) + (2796143800371747/100000000000000 : ℝ)*(major0) + (2796143800371747/100000000000000 : ℝ)*(major1) + (699035950092937/25000000000000 : ℝ)*(major2) + (486142108786503/12500000000000 : ℝ)*(sp0) + (1944587359305279/50000000000000 : ℝ)*(sp1) + (3889174427790183/100000000000000 : ℝ)*(sp2) + (851546931527003/50000000000000 : ℝ)*(sp3) + (39877101913/100000000000000 : ℝ)*(sp4) + (16651903367/100000000000000 : ℝ)*(sp7) + (1703110514957373/100000000000000 : ℝ)*(f.failure) + (1944588373696969/50000000000000 : ℝ)*(f.sum) + (9138314122427/4869000000000000000000000000 : ℝ)*base66 + (3395476739369003021/2434500000000000000000000000000000 : ℝ)*base67 + (2223147241460622191/608625000000000000000000000000000 : ℝ)*base69 + (8910090335639496979/2434500000000000000000000000000000 : ℝ)*base72 + (65385432757/2434500000000000000000000000 : ℝ)*base74 + (4500921408181122191/608625000000000000000000000000000 : ℝ)*base75 + (5119223413958098993/811500000000000000000000000000000 : ℝ)*base78 + (1096806892101901007/811500000000000000000000000000000 : ℝ)*base79 + (11577845940113/4057500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (61814331/10000000000000000000000 : ℝ)*base89 + (61814331/10000000000000000000000 : ℝ)*base91 + (38185669/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7699028447999667733689937/541000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110814617/50000000000000 : ℝ)*(base19) + (581991531/50000000000000 : ℝ)*(base23) + (199542371/100000000000000 : ℝ)*(lower2) + (45774911/12500000000000 : ℝ)*(upper3) + (130051831/50000000000000 : ℝ)*(lower4) + (22650592022277/800000000000 : ℝ)*(major0) + (22650592022277/800000000000 : ℝ)*(major1) + (22650592022277/800000000000 : ℝ)*(major2) + (1259209059/6250000000000 : ℝ)*(sp2) + (409925109/50000000000000 : ℝ)*(sp3) + (3938109015063853/100000000000000 : ℝ)*(sp4) + (3938108793434619/100000000000000 : ℝ)*(sp5) + (492260962966981/12500000000000 : ℝ)*(sp6) + (215567212035621/12500000000000 : ℝ)*(sp7) + (862269258067593/50000000000000 : ℝ)*(f.failure) + (3938109015063853/100000000000000 : ℝ)*(f.sum) + (33399861731/10143750000000000000000000 : ℝ)*base65 + (31891133432809063/6492000000000000000000000000000 : ℝ)*base68 + (59856802138849063/6492000000000000000000000000000 : ℝ)*base70 + (1644929622001063/6492000000000000000000000000000 : ℝ)*base72 + (693580287427/1623000000000000000000000000 : ℝ)*base74 + (23155609323913063/6492000000000000000000000000000 : ℝ)*base76 + (5816657355646937/6492000000000000000000000000000 : ℝ)*base77 + (81375284199025063/6492000000000000000000000000000 : ℝ)*base80 + (1130408338631/811500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3286671/5000000000000000000000 : ℝ)*base89 + (3286671/5000000000000000000000 : ℝ)*base91 + (3286671/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1522_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9113/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1061/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2103/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (399/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1522_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1522_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2103/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (399/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1522_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1522_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1522_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4539/1024 : ℝ) ≤ p) (hpb : p ≤ (4541/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164178647/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2103/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (399/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1522_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

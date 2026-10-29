-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1750_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:19:03.780425+00:00
-- url     : https://prove2.me/submissions/6bd0e460-c703-439a-b7ec-af176de6e241

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
theorem support_rectangle_w1750_s3_0 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1222160163/10000000000 : ℝ)*x 0 + (5497008567/10000000000 : ℝ)*x 1 + (5081131411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1222160163/10000000000 : ℝ)^5775 ≤ (776915144597/10000000000000 : ℝ)^4751 := by
    have hnat : (1222160163 : ℕ)^5775*10000000000000^4751 ≤ 776915144597^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222160163 10000000000 776915144597 10000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497008567/10000000000 : ℝ)^5775 ≤ (24159332773349/50000000000000 : ℝ)^4751 := by
    have hnat : (5497008567 : ℕ)^5775*50000000000000^4751 ≤ 24159332773349^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497008567 10000000000 24159332773349 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081131411/10000000000 : ℝ)^5775 ≤ (43912182991731/100000000000000 : ℝ)^4751 := by
    have hnat : (5081131411 : ℕ)^5775*100000000000000^4751 ≤ 43912182991731^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081131411 10000000000 43912182991731 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1222160163/10000000000 : ℝ), (5497008567/10000000000 : ℝ), (5081131411/10000000000 : ℝ)] ![(776915144597/10000000000000 : ℝ), (24159332773349/50000000000000 : ℝ), (43912182991731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1222160163/10000000000 : ℝ)|^5775 ≤ (776915144597/10000000000000 : ℝ)^4751
        have hw : |(-1222160163/10000000000 : ℝ)|=(1222160163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497008567/10000000000 : ℝ)|^5775 ≤ (24159332773349/50000000000000 : ℝ)^4751
        have hw : |(5497008567/10000000000 : ℝ)|=(5497008567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081131411/10000000000 : ℝ)|^5775 ≤ (43912182991731/100000000000000 : ℝ)^4751
        have hw : |(5081131411/10000000000 : ℝ)|=(5081131411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_1 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067256163/2000000000 : ℝ)*x 0 + (-1439709567/10000000000 : ℝ)*x 1 + (508112981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067256163/2000000000 : ℝ)^5775 ≤ (46606817996827/100000000000000 : ℝ)^4751 := by
    have hnat : (1067256163 : ℕ)^5775*100000000000000^4751 ≤ 46606817996827^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067256163 2000000000 46606817996827 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1439709567/10000000000 : ℝ)^5775 ≤ (592563488717/6250000000000 : ℝ)^4751 := by
    have hnat : (1439709567 : ℕ)^5775*6250000000000^4751 ≤ 592563488717^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439709567 10000000000 592563488717 6250000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508112981/1000000000 : ℝ)^5775 ≤ (43912166173401/100000000000000 : ℝ)^4751 := by
    have hnat : (508112981 : ℕ)^5775*100000000000000^4751 ≤ 43912166173401^4751*1000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508112981 1000000000 43912166173401 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067256163/2000000000 : ℝ), (-1439709567/10000000000 : ℝ), (508112981/1000000000 : ℝ)] ![(46606817996827/100000000000000 : ℝ), (592563488717/6250000000000 : ℝ), (43912166173401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067256163/2000000000 : ℝ)|^5775 ≤ (46606817996827/100000000000000 : ℝ)^4751
        have hw : |(1067256163/2000000000 : ℝ)|=(1067256163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1439709567/10000000000 : ℝ)|^5775 ≤ (592563488717/6250000000000 : ℝ)^4751
        have hw : |(-1439709567/10000000000 : ℝ)|=(1439709567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508112981/1000000000 : ℝ)|^5775 ≤ (43912166173401/100000000000000 : ℝ)^4751
        have hw : |(508112981/1000000000 : ℝ)|=(508112981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_2 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (667034751/1250000000 : ℝ)*x 0 + (79392709/156250000 : ℝ)*x 1 + (-1439708611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (667034751/1250000000 : ℝ)^5775 ≤ (23303394098281/50000000000000 : ℝ)^4751 := by
    have hnat : (667034751 : ℕ)^5775*50000000000000^4751 ≤ 23303394098281^4751*1250000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667034751 1250000000 23303394098281 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79392709/156250000 : ℝ)^5775 ≤ (10978050908461/25000000000000 : ℝ)^4751 := by
    have hnat : (79392709 : ℕ)^5775*25000000000000^4751 ≤ 10978050908461^4751*156250000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79392709 156250000 10978050908461 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1439708611/10000000000 : ℝ)^5775 ≤ (4740504083473/50000000000000 : ℝ)^4751 := by
    have hnat : (1439708611 : ℕ)^5775*50000000000000^4751 ≤ 4740504083473^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439708611 10000000000 4740504083473 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(667034751/1250000000 : ℝ), (79392709/156250000 : ℝ), (-1439708611/10000000000 : ℝ)] ![(23303394098281/50000000000000 : ℝ), (10978050908461/25000000000000 : ℝ), (4740504083473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(667034751/1250000000 : ℝ)|^5775 ≤ (23303394098281/50000000000000 : ℝ)^4751
        have hw : |(667034751/1250000000 : ℝ)|=(667034751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79392709/156250000 : ℝ)|^5775 ≤ (10978050908461/25000000000000 : ℝ)^4751
        have hw : |(79392709/156250000 : ℝ)|=(79392709/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1439708611/10000000000 : ℝ)|^5775 ≤ (4740504083473/50000000000000 : ℝ)^4751
        have hw : |(-1439708611/10000000000 : ℝ)|=(1439708611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_3 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (502608691/1250000000 : ℝ)*x 0 + (1684623869/5000000000 : ℝ)*x 1 + (4735646607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502608691/1250000000 : ℝ)^5775 ≤ (33039818524119/100000000000000 : ℝ)^4751 := by
    have hnat : (502608691 : ℕ)^5775*100000000000000^4751 ≤ 33039818524119^4751*1250000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502608691 1250000000 33039818524119 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1684623869/5000000000 : ℝ)^5775 ≤ (26650197607703/100000000000000 : ℝ)^4751 := by
    have hnat : (1684623869 : ℕ)^5775*100000000000000^4751 ≤ 26650197607703^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1684623869 5000000000 26650197607703 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4735646607/10000000000 : ℝ)^5775 ≤ (20154991924981/50000000000000 : ℝ)^4751 := by
    have hnat : (4735646607 : ℕ)^5775*50000000000000^4751 ≤ 20154991924981^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4735646607 10000000000 20154991924981 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502608691/1250000000 : ℝ), (1684623869/5000000000 : ℝ), (4735646607/10000000000 : ℝ)] ![(33039818524119/100000000000000 : ℝ), (26650197607703/100000000000000 : ℝ), (20154991924981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502608691/1250000000 : ℝ)|^5775 ≤ (33039818524119/100000000000000 : ℝ)^4751
        have hw : |(502608691/1250000000 : ℝ)|=(502608691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1684623869/5000000000 : ℝ)|^5775 ≤ (26650197607703/100000000000000 : ℝ)^4751
        have hw : |(1684623869/5000000000 : ℝ)|=(1684623869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4735646607/10000000000 : ℝ)|^5775 ≤ (20154991924981/50000000000000 : ℝ)^4751
        have hw : |(4735646607/10000000000 : ℝ)|=(4735646607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_4 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1222509361/10000000000 : ℝ)*x 0 + (1271973847/2500000000 : ℝ)*x 1 + (2745051939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1222509361/10000000000 : ℝ)^5775 ≤ (1942962447843/25000000000000 : ℝ)^4751 := by
    have hnat : (1222509361 : ℕ)^5775*25000000000000^4751 ≤ 1942962447843^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222509361 10000000000 1942962447843 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1271973847/2500000000 : ℝ)^5775 ≤ (43983248024073/100000000000000 : ℝ)^4751 := by
    have hnat : (1271973847 : ℕ)^5775*100000000000000^4751 ≤ 43983248024073^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1271973847 2500000000 43983248024073 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745051939/5000000000 : ℝ)^5775 ≤ (48244902170451/100000000000000 : ℝ)^4751 := by
    have hnat : (2745051939 : ℕ)^5775*100000000000000^4751 ≤ 48244902170451^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745051939 5000000000 48244902170451 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1222509361/10000000000 : ℝ), (1271973847/2500000000 : ℝ), (2745051939/5000000000 : ℝ)] ![(1942962447843/25000000000000 : ℝ), (43983248024073/100000000000000 : ℝ), (48244902170451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1222509361/10000000000 : ℝ)|^5775 ≤ (1942962447843/25000000000000 : ℝ)^4751
        have hw : |(-1222509361/10000000000 : ℝ)|=(1222509361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1271973847/2500000000 : ℝ)|^5775 ≤ (43983248024073/100000000000000 : ℝ)^4751
        have hw : |(1271973847/2500000000 : ℝ)|=(1271973847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745051939/5000000000 : ℝ)|^5775 ≤ (48244902170451/100000000000000 : ℝ)^4751
        have hw : |(2745051939/5000000000 : ℝ)|=(2745051939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_5 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226034897/10000000000 : ℝ)*x 0 + (-206147141/2000000000 : ℝ)*x 1 + (2745051867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226034897/10000000000 : ℝ)^5775 ≤ (22719511021729/50000000000000 : ℝ)^4751 := by
    have hnat : (5226034897 : ℕ)^5775*50000000000000^4751 ≤ 22719511021729^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226034897 10000000000 22719511021729 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206147141/2000000000 : ℝ)^5775 ≤ (789509664169/12500000000000 : ℝ)^4751 := by
    have hnat : (206147141 : ℕ)^5775*12500000000000^4751 ≤ 789509664169^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206147141 2000000000 789509664169 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745051867/5000000000 : ℝ)^5775 ≤ (9648980126459/20000000000000 : ℝ)^4751 := by
    have hnat : (2745051867 : ℕ)^5775*20000000000000^4751 ≤ 9648980126459^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745051867 5000000000 9648980126459 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226034897/10000000000 : ℝ), (-206147141/2000000000 : ℝ), (2745051867/5000000000 : ℝ)] ![(22719511021729/50000000000000 : ℝ), (789509664169/12500000000000 : ℝ), (9648980126459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226034897/10000000000 : ℝ)|^5775 ≤ (22719511021729/50000000000000 : ℝ)^4751
        have hw : |(5226034897/10000000000 : ℝ)|=(5226034897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206147141/2000000000 : ℝ)|^5775 ≤ (789509664169/12500000000000 : ℝ)^4751
        have hw : |(-206147141/2000000000 : ℝ)|=(206147141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745051867/5000000000 : ℝ)|^5775 ≤ (9648980126459/20000000000000 : ℝ)^4751
        have hw : |(2745051867/5000000000 : ℝ)|=(2745051867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_6 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226034787/10000000000 : ℝ)*x 0 + (5490103359/10000000000 : ℝ)*x 1 + (-1030736399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226034787/10000000000 : ℝ)^5775 ≤ (9087804176179/20000000000000 : ℝ)^4751 := by
    have hnat : (5226034787 : ℕ)^5775*20000000000000^4751 ≤ 9087804176179^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226034787 10000000000 9087804176179 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490103359/10000000000 : ℝ)^5775 ≤ (48244896626681/100000000000000 : ℝ)^4751 := by
    have hnat : (5490103359 : ℕ)^5775*100000000000000^4751 ≤ 48244896626681^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490103359 10000000000 48244896626681 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030736399/10000000000 : ℝ)^5775 ≤ (631608248259/10000000000000 : ℝ)^4751 := by
    have hnat : (1030736399 : ℕ)^5775*10000000000000^4751 ≤ 631608248259^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030736399 10000000000 631608248259 10000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226034787/10000000000 : ℝ), (5490103359/10000000000 : ℝ), (-1030736399/10000000000 : ℝ)] ![(9087804176179/20000000000000 : ℝ), (48244896626681/100000000000000 : ℝ), (631608248259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226034787/10000000000 : ℝ)|^5775 ≤ (9087804176179/20000000000000 : ℝ)^4751
        have hw : |(5226034787/10000000000 : ℝ)|=(5226034787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490103359/10000000000 : ℝ)|^5775 ≤ (48244896626681/100000000000000 : ℝ)^4751
        have hw : |(5490103359/10000000000 : ℝ)|=(5490103359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030736399/10000000000 : ℝ)|^5775 ≤ (631608248259/10000000000000 : ℝ)^4751
        have hw : |(-1030736399/10000000000 : ℝ)|=(1030736399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_s3_7 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (804404801/2000000000 : ℝ)*x 0 + (2356710949/5000000000 : ℝ)*x 1 + (339193657/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804404801/2000000000 : ℝ)^5775 ≤ (33051349959037/100000000000000 : ℝ)^4751 := by
    have hnat : (804404801 : ℕ)^5775*100000000000000^4751 ≤ 33051349959037^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804404801 2000000000 33051349959037 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2356710949/5000000000 : ℝ)^5775 ≤ (40080148722377/100000000000000 : ℝ)^4751 := by
    have hnat : (2356710949 : ℕ)^5775*100000000000000^4751 ≤ 40080148722377^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356710949 5000000000 40080148722377 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339193657/1000000000 : ℝ)^5775 ≤ (26868501304917/100000000000000 : ℝ)^4751 := by
    have hnat : (339193657 : ℕ)^5775*100000000000000^4751 ≤ 26868501304917^4751*1000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339193657 1000000000 26868501304917 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804404801/2000000000 : ℝ), (2356710949/5000000000 : ℝ), (339193657/1000000000 : ℝ)] ![(33051349959037/100000000000000 : ℝ), (40080148722377/100000000000000 : ℝ), (26868501304917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804404801/2000000000 : ℝ)|^5775 ≤ (33051349959037/100000000000000 : ℝ)^4751
        have hw : |(804404801/2000000000 : ℝ)|=(804404801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2356710949/5000000000 : ℝ)|^5775 ≤ (40080148722377/100000000000000 : ℝ)^4751
        have hw : |(2356710949/5000000000 : ℝ)|=(2356710949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339193657/1000000000 : ℝ)|^5775 ≤ (26868501304917/100000000000000 : ℝ)^4751
        have hw : |(339193657/1000000000 : ℝ)|=(339193657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1750_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (719/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2247/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9039/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2247/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9039/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2247/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9039/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2247/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9039/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2247/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9039/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2247/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9039/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9039/100000 : ℝ) ^ (5759/1024 : ℝ) ≤ (67323485363313/50000000000000000000 : ℝ) := by
    have hpowers : (9039/100000 : ℝ)^5759 ≤ (67323485363313/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9039 : ℕ)^5759*50000000000000000000^1024 ≤ 67323485363313^1024*100000^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9039 100000 67323485363313 50000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9039/100000 : ℝ)) (X := (67323485363313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2247/12500 : ℝ) ^ (5759/1024 : ℝ) ≤ (6432448206507013/100000000000000000000 : ℝ) := by
    have hpowers : (2247/12500 : ℝ)^5759 ≤ (6432448206507013/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2247 : ℕ)^5759*100000000000000000000^1024 ≤ 6432448206507013^1024*12500^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 12500 6432448206507013 100000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/12500 : ℝ)) (X := (6432448206507013/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000067323485363313/25000000000000000000 : ℝ) ≤ (5000002394136923/5000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (25000067323485363313/25000000000000000000 : ℝ)^1024 ≤ (5000002394136923/5000000000000000 : ℝ)^5759 := by
      have hnat : (25000067323485363313 : ℕ)^1024*5000000000000000^5759 ≤ 5000002394136923^5759*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000067323485363313 25000000000000000000 5000002394136923 5000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002394136923/5000000000000000 : ℝ)) (X := (25000067323485363313/25000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100006567095177233639/100000000000000000000 : ℝ) ≤ (2500029191369689/2500000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (100006567095177233639/100000000000000000000 : ℝ)^1024 ≤ (2500029191369689/2500000000000000 : ℝ)^5759 := by
      have hnat : (100006567095177233639 : ℕ)^1024*2500000000000000^5759 ≤ 2500029191369689^5759*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100006567095177233639 100000000000000000000 2500029191369689 2500000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500029191369689/2500000000000000 : ℝ)) (X := (100006567095177233639/100000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50006432448206507013/50000000000000000000 : ℝ) ≤ (5000114371341833/5000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (50006432448206507013/50000000000000000000 : ℝ)^1024 ≤ (5000114371341833/5000000000000000 : ℝ)^5759 := by
      have hnat : (50006432448206507013 : ℕ)^1024*5000000000000000^5759 ≤ 5000114371341833^5759*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006432448206507013 50000000000000000000 5000114371341833 5000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000114371341833/5000000000000000 : ℝ)) (X := (50006432448206507013/50000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(67323485363313/50000000000000000000 : ℝ) ≤ ((4964889914938499929/4965000000000000000 : ℝ)+2*(3732573497/29790000000000 : ℝ)*(9039/100000 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (4964889914938499929/4965000000000000000 : ℝ)+2*(3732573497/29790000000000 : ℝ)*(9039/100000 : ℝ)=(5000002394136923/5000000000000000 : ℝ) by norm_num, show 1+2*(67323485363313/50000000000000000000 : ℝ)=(25000067323485363313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6432448206507013/100000000000000000000 : ℝ)+(67323485363313/50000000000000000000 : ℝ) ≤ ((4964889914938499929/4965000000000000000 : ℝ)+(3732573497/29790000000000 : ℝ)*((2247/12500 : ℝ)+(9039/100000 : ℝ)))^(5759/1024 : ℝ) := by
    rw [show (4964889914938499929/4965000000000000000 : ℝ)+(3732573497/29790000000000 : ℝ)*((2247/12500 : ℝ)+(9039/100000 : ℝ))=(2500029191369689/2500000000000000 : ℝ) by norm_num, show 1+(6432448206507013/100000000000000000000 : ℝ)+(67323485363313/50000000000000000000 : ℝ)=(100006567095177233639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6432448206507013/100000000000000000000 : ℝ) ≤ ((4964889914938499929/4965000000000000000 : ℝ)+2*(3732573497/29790000000000 : ℝ)*(2247/12500 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (4964889914938499929/4965000000000000000 : ℝ)+2*(3732573497/29790000000000 : ℝ)*(2247/12500 : ℝ)=(5000114371341833/5000000000000000 : ℝ) by norm_num, show 1+2*(6432448206507013/100000000000000000000 : ℝ)=(50006432448206507013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4964889914938499929/4965000000000000000 : ℝ)*(X 1 0+X 2 0)+(3732573497/29790000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (9039/100000 : ℝ)) (hi := (2247/12500 : ℝ)) (c := (4964889914938499929/4965000000000000000 : ℝ)) (alpha := (3732573497/29790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4964889914938499929/4965000000000000000 : ℝ)*(X 0 1+X 2 1)+(3732573497/29790000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (9039/100000 : ℝ)) (hi := (2247/12500 : ℝ)) (c := (4964889914938499929/4965000000000000000 : ℝ)) (alpha := (3732573497/29790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4964889914938499929/4965000000000000000 : ℝ)*(X 0 2+X 1 2)+(3732573497/29790000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (9039/100000 : ℝ)) (hi := (2247/12500 : ℝ)) (c := (4964889914938499929/4965000000000000000 : ℝ)) (alpha := (3732573497/29790000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1222160163/10000000000 : ℝ)*X 0 0+(5497008567/10000000000 : ℝ)*X 0 1+(5081131411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1067256163/2000000000 : ℝ)*X 1 0+(-1439709567/10000000000 : ℝ)*X 1 1+(508112981/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((667034751/1250000000 : ℝ)*X 2 0+(79392709/156250000 : ℝ)*X 2 1+(-1439708611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((502608691/1250000000 : ℝ)*X 0 0+(1684623869/5000000000 : ℝ)*X 0 1+(4735646607/10000000000 : ℝ)*X 0 2+(502608691/1250000000 : ℝ)*X 1 0+(1684623869/5000000000 : ℝ)*X 1 1+(4735646607/10000000000 : ℝ)*X 1 2+(502608691/1250000000 : ℝ)*X 2 0+(1684623869/5000000000 : ℝ)*X 2 1+(4735646607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1222509361/10000000000 : ℝ)*X 0 0+(1271973847/2500000000 : ℝ)*X 0 1+(2745051939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226034897/10000000000 : ℝ)*X 1 0+(-206147141/2000000000 : ℝ)*X 1 1+(2745051867/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5226034787/10000000000 : ℝ)*X 2 0+(5490103359/10000000000 : ℝ)*X 2 1+(-1030736399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((804404801/2000000000 : ℝ)*X 0 0+(2356710949/5000000000 : ℝ)*X 0 1+(339193657/1000000000 : ℝ)*X 0 2+(804404801/2000000000 : ℝ)*X 1 0+(2356710949/5000000000 : ℝ)*X 1 1+(339193657/1000000000 : ℝ)*X 1 2+(804404801/2000000000 : ℝ)*X 2 0+(2356710949/5000000000 : ℝ)*X 2 1+(339193657/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (565456908387191932036797647/41375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2276297937/100000000000000 : ℝ)*(base19) + (456069879/100000000000000 : ℝ)*(base23) + (42705281/12500000000000 : ℝ)*(upper3) + (18522551/6250000000000 : ℝ)*(upper4) + (160589829/50000000000000 : ℝ)*(upper5) + (1568216174168343/100000000000000 : ℝ)*(major0) + (1568216174168343/100000000000000 : ℝ)*(major1) + (1568216174168343/100000000000000 : ℝ)*(major2) + (2404565091164773/100000000000000 : ℝ)*(sp0) + (601143106486951/25000000000000 : ℝ)*(sp1) + (1202287123087931/50000000000000 : ℝ)*(sp2) + (731853946268133/100000000000000 : ℝ)*(sp3) + (1201385121/12500000000000 : ℝ)*(sp4) + (8110671/250000000000 : ℝ)*(sp7) + (731857190536533/100000000000000 : ℝ)*(f.failure) + (2404574702245741/100000000000000 : ℝ)*(f.sum) + (2331002989753/993000000000000000000000000 : ℝ)*base65 + (2254361505580452353/496500000000000000000000000000000 : ℝ)*base68 + (1675789613198952353/496500000000000000000000000000000 : ℝ)*base70 + (4373885873687952353/496500000000000000000000000000000 : ℝ)*base72 + (454131998179/248250000000000000000000000 : ℝ)*base73 + (1525315375516547647/496500000000000000000000000000000 : ℝ)*base75 + (2295766572461952353/496500000000000000000000000000000 : ℝ)*base78 + (1659745279250952353/496500000000000000000000000000000 : ℝ)*base80 + (1289178373343/993000000000000000000000000 : ℝ)*base82 + (22267929/10000000000000000000000 : ℝ)*base90 + (22267929/10000000000000000000000 : ℝ)*base92 + (22267929/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (293899528114756720354020689/41375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (553487513/100000000000000 : ℝ)*(base19) + (167381909/20000000000000 : ℝ)*(base23) + (131254343/100000000000000 : ℝ)*(lower1) + (206683893/100000000000000 : ℝ)*(lower4) + (12701407/10000000000000 : ℝ)*(upper5) + (1621496433288441/100000000000000 : ℝ)*(major0) + (1621496433288441/100000000000000 : ℝ)*(major1) + (1621496433288441/100000000000000 : ℝ)*(major2) + (162582419/20000000000000 : ℝ)*(sp0) + (353953969/12500000000000 : ℝ)*(sp1) + (2486269724819753/100000000000000 : ℝ)*(sp4) + (1243133576306291/50000000000000 : ℝ)*(sp5) + (77695928150697/3125000000000 : ℝ)*(sp6) + (189180523016991/25000000000000 : ℝ)*(sp7) + (189180523016991/25000000000000 : ℝ)*(f.failure) + (310783817216481/12500000000000 : ℝ)*(f.sum) + (86529646699/31031250000000000000000000 : ℝ)*base66 + (2681630038901979311/496500000000000000000000000000000 : ℝ)*base68 + (1328950026548979311/496500000000000000000000000000000 : ℝ)*base70 + (2213974232716479311/496500000000000000000000000000000 : ℝ)*base72 + (38246525491/248250000000000000000000000 : ℝ)*base73 + (3020047324402520689/496500000000000000000000000000000 : ℝ)*base75 + (3015214669117479311/496500000000000000000000000000000 : ℝ)*base78 + (5362532485027479311/496500000000000000000000000000000 : ℝ)*base80 + (1413897124703/496500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (9731883/2500000000000000000000 : ℝ)*base90 + (9731883/2500000000000000000000 : ℝ)*base92 + (9731883/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1750_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (719/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1750_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1750_box_0 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208863911/2500000000 : ℝ)*x 0 + (1356325109/2500000000 : ℝ)*x 1 + (339081249/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208863911/2500000000 : ℝ)^5775 ≤ (4892847685183/100000000000000 : ℝ)^4751 := by
    have hnat : (208863911 : ℕ)^5775*100000000000000^4751 ≤ 4892847685183^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208863911 2500000000 4892847685183 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356325109/2500000000 : ℝ)^5775 ≤ (9510715711761/20000000000000 : ℝ)^4751 := by
    have hnat : (1356325109 : ℕ)^5775*20000000000000^4751 ≤ 9510715711761^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356325109 2500000000 9510715711761 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339081249/625000000 : ℝ)^5775 ≤ (23776786871523/50000000000000 : ℝ)^4751 := by
    have hnat : (339081249 : ℕ)^5775*50000000000000^4751 ≤ 23776786871523^4751*625000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339081249 625000000 23776786871523 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208863911/2500000000 : ℝ), (1356325109/2500000000 : ℝ), (339081249/625000000 : ℝ)] ![(4892847685183/100000000000000 : ℝ), (9510715711761/20000000000000 : ℝ), (23776786871523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208863911/2500000000 : ℝ)|^5775 ≤ (4892847685183/100000000000000 : ℝ)^4751
        have hw : |(-208863911/2500000000 : ℝ)|=(208863911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356325109/2500000000 : ℝ)|^5775 ≤ (9510715711761/20000000000000 : ℝ)^4751
        have hw : |(1356325109/2500000000 : ℝ)|=(1356325109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339081249/625000000 : ℝ)|^5775 ≤ (23776786871523/50000000000000 : ℝ)^4751
        have hw : |(339081249/625000000 : ℝ)|=(339081249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_1 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597206113/5000000000 : ℝ)*x 0 + (-583262631/5000000000 : ℝ)*x 1 + (1356325099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597206113/5000000000 : ℝ)^5775 ≤ (45105028220573/100000000000000 : ℝ)^4751 := by
    have hnat : (2597206113 : ℕ)^5775*100000000000000^4751 ≤ 45105028220573^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597206113 5000000000 45105028220573 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583262631/5000000000 : ℝ)^5775 ≤ (3670696818271/50000000000000 : ℝ)^4751 := by
    have hnat : (583262631 : ℕ)^5775*50000000000000^4751 ≤ 3670696818271^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583262631 5000000000 3670696818271 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356325099/2500000000 : ℝ)^5775 ≤ (5944197266579/12500000000000 : ℝ)^4751 := by
    have hnat : (1356325099 : ℕ)^5775*12500000000000^4751 ≤ 5944197266579^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356325099 2500000000 5944197266579 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597206113/5000000000 : ℝ), (-583262631/5000000000 : ℝ), (1356325099/2500000000 : ℝ)] ![(45105028220573/100000000000000 : ℝ), (3670696818271/50000000000000 : ℝ), (5944197266579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597206113/5000000000 : ℝ)|^5775 ≤ (45105028220573/100000000000000 : ℝ)^4751
        have hw : |(2597206113/5000000000 : ℝ)|=(2597206113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-583262631/5000000000 : ℝ)|^5775 ≤ (3670696818271/50000000000000 : ℝ)^4751
        have hw : |(-583262631/5000000000 : ℝ)|=(583262631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356325099/2500000000 : ℝ)|^5775 ≤ (5944197266579/12500000000000 : ℝ)^4751
        have hw : |(1356325099/2500000000 : ℝ)|=(1356325099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_2 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207776509/400000000 : ℝ)*x 0 + (1356325003/2500000000 : ℝ)*x 1 + (-1166525107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207776509/400000000 : ℝ)^5775 ≤ (9021006697497/20000000000000 : ℝ)^4751 := by
    have hnat : (207776509 : ℕ)^5775*20000000000000^4751 ≤ 9021006697497^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207776509 400000000 9021006697497 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356325003/2500000000 : ℝ)^5775 ≤ (47553574041367/100000000000000 : ℝ)^4751 := by
    have hnat : (1356325003 : ℕ)^5775*100000000000000^4751 ≤ 47553574041367^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356325003 2500000000 47553574041367 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1166525107/10000000000 : ℝ)^5775 ≤ (367069622541/5000000000000 : ℝ)^4751 := by
    have hnat : (1166525107 : ℕ)^5775*5000000000000^4751 ≤ 367069622541^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166525107 10000000000 367069622541 5000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207776509/400000000 : ℝ), (1356325003/2500000000 : ℝ), (-1166525107/10000000000 : ℝ)] ![(9021006697497/20000000000000 : ℝ), (47553574041367/100000000000000 : ℝ), (367069622541/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207776509/400000000 : ℝ)|^5775 ≤ (9021006697497/20000000000000 : ℝ)^4751
        have hw : |(207776509/400000000 : ℝ)|=(207776509/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356325003/2500000000 : ℝ)|^5775 ≤ (47553574041367/100000000000000 : ℝ)^4751
        have hw : |(1356325003/2500000000 : ℝ)|=(1356325003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1166525107/10000000000 : ℝ)|^5775 ≤ (367069622541/5000000000000 : ℝ)^4751
        have hw : |(-1166525107/10000000000 : ℝ)|=(1166525107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_3 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2273618913/5000000000 : ℝ)*x 0 + (3796806441/10000000000 : ℝ)*x 1 + (3796806489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2273618913/5000000000 : ℝ)^5775 ≤ (38369028365407/100000000000000 : ℝ)^4751 := by
    have hnat : (2273618913 : ℕ)^5775*100000000000000^4751 ≤ 38369028365407^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273618913 5000000000 38369028365407 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3796806441/10000000000 : ℝ)^5775 ≤ (30815485575793/100000000000000 : ℝ)^4751 := by
    have hnat : (3796806441 : ℕ)^5775*100000000000000^4751 ≤ 30815485575793^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3796806441 10000000000 30815485575793 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3796806489/10000000000 : ℝ)^5775 ≤ (3851935756167/12500000000000 : ℝ)^4751 := by
    have hnat : (3796806489 : ℕ)^5775*12500000000000^4751 ≤ 3851935756167^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3796806489 10000000000 3851935756167 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2273618913/5000000000 : ℝ), (3796806441/10000000000 : ℝ), (3796806489/10000000000 : ℝ)] ![(38369028365407/100000000000000 : ℝ), (30815485575793/100000000000000 : ℝ), (3851935756167/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2273618913/5000000000 : ℝ)|^5775 ≤ (38369028365407/100000000000000 : ℝ)^4751
        have hw : |(2273618913/5000000000 : ℝ)|=(2273618913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3796806441/10000000000 : ℝ)|^5775 ≤ (30815485575793/100000000000000 : ℝ)^4751
        have hw : |(3796806441/10000000000 : ℝ)|=(3796806441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3796806489/10000000000 : ℝ)|^5775 ≤ (3851935756167/12500000000000 : ℝ)^4751
        have hw : |(3796806489/10000000000 : ℝ)|=(3796806489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_4 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-329721549/2000000000 : ℝ)*x 0 + (4006679/7812500 : ℝ)*x 1 + (5128548533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329721549/2000000000 : ℝ)^5775 ≤ (5589202480737/50000000000000 : ℝ)^4751 := by
    have hnat : (329721549 : ℕ)^5775*50000000000000^4751 ≤ 5589202480737^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329721549 2000000000 5589202480737 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006679/7812500 : ℝ)^5775 ≤ (888216012031/2000000000000 : ℝ)^4751 := by
    have hnat : (4006679 : ℕ)^5775*2000000000000^4751 ≤ 888216012031^4751*7812500^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006679 7812500 888216012031 2000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128548533/10000000000 : ℝ)^5775 ≤ (22205397211411/50000000000000 : ℝ)^4751 := by
    have hnat : (5128548533 : ℕ)^5775*50000000000000^4751 ≤ 22205397211411^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128548533 10000000000 22205397211411 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-329721549/2000000000 : ℝ), (4006679/7812500 : ℝ), (5128548533/10000000000 : ℝ)] ![(5589202480737/50000000000000 : ℝ), (888216012031/2000000000000 : ℝ), (22205397211411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-329721549/2000000000 : ℝ)|^5775 ≤ (5589202480737/50000000000000 : ℝ)^4751
        have hw : |(-329721549/2000000000 : ℝ)|=(329721549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006679/7812500 : ℝ)|^5775 ≤ (888216012031/2000000000000 : ℝ)^4751
        have hw : |(4006679/7812500 : ℝ)|=(4006679/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128548533/10000000000 : ℝ)|^5775 ≤ (22205397211411/50000000000000 : ℝ)^4751
        have hw : |(5128548533/10000000000 : ℝ)|=(5128548533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_5 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134826547/250000000 : ℝ)*x 0 + (-650267539/5000000000 : ℝ)*x 1 + (5128549821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134826547/250000000 : ℝ)^5775 ≤ (23605159233141/50000000000000 : ℝ)^4751 := by
    have hnat : (134826547 : ℕ)^5775*50000000000000^4751 ≤ 23605159233141^4751*250000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134826547 250000000 23605159233141 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650267539/5000000000 : ℝ)^5775 ≤ (1675774709097/20000000000000 : ℝ)^4751 := by
    have hnat : (650267539 : ℕ)^5775*20000000000000^4751 ≤ 1675774709097^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650267539 5000000000 1675774709097 20000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5128549821/10000000000 : ℝ)^5775 ≤ (44410807980237/100000000000000 : ℝ)^4751 := by
    have hnat : (5128549821 : ℕ)^5775*100000000000000^4751 ≤ 44410807980237^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128549821 10000000000 44410807980237 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134826547/250000000 : ℝ), (-650267539/5000000000 : ℝ), (5128549821/10000000000 : ℝ)] ![(23605159233141/50000000000000 : ℝ), (1675774709097/20000000000000 : ℝ), (44410807980237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134826547/250000000 : ℝ)|^5775 ≤ (23605159233141/50000000000000 : ℝ)^4751
        have hw : |(134826547/250000000 : ℝ)|=(134826547/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-650267539/5000000000 : ℝ)|^5775 ≤ (1675774709097/20000000000000 : ℝ)^4751
        have hw : |(-650267539/5000000000 : ℝ)|=(650267539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5128549821/10000000000 : ℝ)|^5775 ≤ (44410807980237/100000000000000 : ℝ)^4751
        have hw : |(5128549821/10000000000 : ℝ)|=(5128549821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_6 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696531243/5000000000 : ℝ)*x 0 + (160267157/312500000 : ℝ)*x 1 + (-52021413/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696531243/5000000000 : ℝ)^5775 ≤ (47210324914521/100000000000000 : ℝ)^4751 := by
    have hnat : (2696531243 : ℕ)^5775*100000000000000^4751 ≤ 47210324914521^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696531243 5000000000 47210324914521 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160267157/312500000 : ℝ)^5775 ≤ (2220539979553/5000000000000 : ℝ)^4751 := by
    have hnat : (160267157 : ℕ)^5775*5000000000000^4751 ≤ 2220539979553^4751*312500000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160267157 312500000 2220539979553 5000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52021413/400000000 : ℝ)^5775 ≤ (8378875479801/100000000000000 : ℝ)^4751 := by
    have hnat : (52021413 : ℕ)^5775*100000000000000^4751 ≤ 8378875479801^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52021413 400000000 8378875479801 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696531243/5000000000 : ℝ), (160267157/312500000 : ℝ), (-52021413/400000000 : ℝ)] ![(47210324914521/100000000000000 : ℝ), (2220539979553/5000000000000 : ℝ), (8378875479801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696531243/5000000000 : ℝ)|^5775 ≤ (47210324914521/100000000000000 : ℝ)^4751
        have hw : |(2696531243/5000000000 : ℝ)|=(2696531243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160267157/312500000 : ℝ)|^5775 ≤ (2220539979553/5000000000000 : ℝ)^4751
        have hw : |(160267157/312500000 : ℝ)|=(160267157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-52021413/400000000 : ℝ)|^5775 ≤ (8378875479801/100000000000000 : ℝ)^4751
        have hw : |(-52021413/400000000 : ℝ)|=(52021413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_7 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (138315219/400000000 : ℝ)*x 0 + (2169682791/5000000000 : ℝ)*x 1 + (2169682821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138315219/400000000 : ℝ)^5775 ≤ (6876192925077/25000000000000 : ℝ)^4751 := by
    have hnat : (138315219 : ℕ)^5775*25000000000000^4751 ≤ 6876192925077^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138315219 400000000 6876192925077 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169682791/5000000000 : ℝ)^5775 ≤ (36247613838387/100000000000000 : ℝ)^4751 := by
    have hnat : (2169682791 : ℕ)^5775*100000000000000^4751 ≤ 36247613838387^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169682791 5000000000 36247613838387 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2169682821/5000000000 : ℝ)^5775 ≤ (9061903611901/25000000000000 : ℝ)^4751 := by
    have hnat : (2169682821 : ℕ)^5775*25000000000000^4751 ≤ 9061903611901^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169682821 5000000000 9061903611901 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(138315219/400000000 : ℝ), (2169682791/5000000000 : ℝ), (2169682821/5000000000 : ℝ)] ![(6876192925077/25000000000000 : ℝ), (36247613838387/100000000000000 : ℝ), (9061903611901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(138315219/400000000 : ℝ)|^5775 ≤ (6876192925077/25000000000000 : ℝ)^4751
        have hw : |(138315219/400000000 : ℝ)|=(138315219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2169682791/5000000000 : ℝ)|^5775 ≤ (36247613838387/100000000000000 : ℝ)^4751
        have hw : |(2169682791/5000000000 : ℝ)|=(2169682791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2169682821/5000000000 : ℝ)|^5775 ≤ (9061903611901/25000000000000 : ℝ)^4751
        have hw : |(2169682821/5000000000 : ℝ)|=(2169682821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_8 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-294353397/2000000000 : ℝ)*x 0 + (4902596203/10000000000 : ℝ)*x 1 + (1097515221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (294353397/2000000000 : ℝ)^5775 ≤ (4869119578489/50000000000000 : ℝ)^4751 := by
    have hnat : (294353397 : ℕ)^5775*50000000000000^4751 ≤ 4869119578489^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294353397 2000000000 4869119578489 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4902596203/10000000000 : ℝ)^5775 ≤ (5255482259257/12500000000000 : ℝ)^4751 := by
    have hnat : (4902596203 : ℕ)^5775*12500000000000^4751 ≤ 5255482259257^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902596203 10000000000 5255482259257 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097515221/2000000000 : ℝ)^5775 ≤ (4821790275603/10000000000000 : ℝ)^4751 := by
    have hnat : (1097515221 : ℕ)^5775*10000000000000^4751 ≤ 4821790275603^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097515221 2000000000 4821790275603 10000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-294353397/2000000000 : ℝ), (4902596203/10000000000 : ℝ), (1097515221/2000000000 : ℝ)] ![(4869119578489/50000000000000 : ℝ), (5255482259257/12500000000000 : ℝ), (4821790275603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-294353397/2000000000 : ℝ)|^5775 ≤ (4869119578489/50000000000000 : ℝ)^4751
        have hw : |(-294353397/2000000000 : ℝ)|=(294353397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4902596203/10000000000 : ℝ)|^5775 ≤ (5255482259257/12500000000000 : ℝ)^4751
        have hw : |(4902596203/10000000000 : ℝ)|=(4902596203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097515221/2000000000 : ℝ)|^5775 ≤ (4821790275603/10000000000000 : ℝ)^4751
        have hw : |(1097515221/2000000000 : ℝ)|=(1097515221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_9 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152789007/10000000000 : ℝ)*x 0 + (-45479159/400000000 : ℝ)*x 1 + (5487578751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152789007/10000000000 : ℝ)^5775 ≤ (44666078086987/100000000000000 : ℝ)^4751 := by
    have hnat : (5152789007 : ℕ)^5775*100000000000000^4751 ≤ 44666078086987^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152789007 10000000000 44666078086987 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45479159/400000000 : ℝ)^5775 ≤ (444749430307/6250000000000 : ℝ)^4751 := by
    have hnat : (45479159 : ℕ)^5775*6250000000000^4751 ≤ 444749430307^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45479159 400000000 444749430307 6250000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5487578751/10000000000 : ℝ)^5775 ≤ (48217931016839/100000000000000 : ℝ)^4751 := by
    have hnat : (5487578751 : ℕ)^5775*100000000000000^4751 ≤ 48217931016839^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487578751 10000000000 48217931016839 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152789007/10000000000 : ℝ), (-45479159/400000000 : ℝ), (5487578751/10000000000 : ℝ)] ![(44666078086987/100000000000000 : ℝ), (444749430307/6250000000000 : ℝ), (48217931016839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152789007/10000000000 : ℝ)|^5775 ≤ (44666078086987/100000000000000 : ℝ)^4751
        have hw : |(5152789007/10000000000 : ℝ)|=(5152789007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45479159/400000000 : ℝ)|^5775 ≤ (444749430307/6250000000000 : ℝ)^4751
        have hw : |(-45479159/400000000 : ℝ)|=(45479159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5487578751/10000000000 : ℝ)|^5775 ≤ (48217931016839/100000000000000 : ℝ)^4751
        have hw : |(5487578751/10000000000 : ℝ)|=(5487578751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_10 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576394917/5000000000 : ℝ)*x 0 + (219503133/400000000 : ℝ)*x 1 + (-284244607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576394917/5000000000 : ℝ)^5775 ≤ (22333043400397/50000000000000 : ℝ)^4751 := by
    have hnat : (2576394917 : ℕ)^5775*50000000000000^4751 ≤ 22333043400397^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576394917 5000000000 22333043400397 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219503133/400000000 : ℝ)^5775 ≤ (1506810202091/3125000000000 : ℝ)^4751 := by
    have hnat : (219503133 : ℕ)^5775*3125000000000^4751 ≤ 1506810202091^4751*400000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219503133 400000000 1506810202091 3125000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284244607/2500000000 : ℝ)^5775 ≤ (3557993361767/50000000000000 : ℝ)^4751 := by
    have hnat : (284244607 : ℕ)^5775*50000000000000^4751 ≤ 3557993361767^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284244607 2500000000 3557993361767 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576394917/5000000000 : ℝ), (219503133/400000000 : ℝ), (-284244607/2500000000 : ℝ)] ![(22333043400397/50000000000000 : ℝ), (1506810202091/3125000000000 : ℝ), (3557993361767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576394917/5000000000 : ℝ)|^5775 ≤ (22333043400397/50000000000000 : ℝ)^4751
        have hw : |(2576394917/5000000000 : ℝ)|=(2576394917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219503133/400000000 : ℝ)|^5775 ≤ (1506810202091/3125000000000 : ℝ)^4751
        have hw : |(219503133/400000000 : ℝ)|=(219503133/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284244607/2500000000 : ℝ)|^5775 ≤ (3557993361767/50000000000000 : ℝ)^4751
        have hw : |(-284244607/2500000000 : ℝ)|=(284244607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_11 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2382634381/5000000000 : ℝ)*x 0 + (184125897/500000000 : ℝ)*x 1 + (1841258613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2382634381/5000000000 : ℝ)^5775 ≤ (1015417014171/2500000000000 : ℝ)^4751 := by
    have hnat : (2382634381 : ℕ)^5775*2500000000000^4751 ≤ 1015417014171^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382634381 5000000000 1015417014171 2500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184125897/500000000 : ℝ)^5775 ≤ (3711457900723/12500000000000 : ℝ)^4751 := by
    have hnat : (184125897 : ℕ)^5775*12500000000000^4751 ≤ 3711457900723^4751*500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184125897 500000000 3711457900723 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1841258613/5000000000 : ℝ)^5775 ≤ (7422914052023/25000000000000 : ℝ)^4751 := by
    have hnat : (1841258613 : ℕ)^5775*25000000000000^4751 ≤ 7422914052023^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841258613 5000000000 7422914052023 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2382634381/5000000000 : ℝ), (184125897/500000000 : ℝ), (1841258613/5000000000 : ℝ)] ![(1015417014171/2500000000000 : ℝ), (3711457900723/12500000000000 : ℝ), (7422914052023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2382634381/5000000000 : ℝ)|^5775 ≤ (1015417014171/2500000000000 : ℝ)^4751
        have hw : |(2382634381/5000000000 : ℝ)|=(2382634381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184125897/500000000 : ℝ)|^5775 ≤ (3711457900723/12500000000000 : ℝ)^4751
        have hw : |(184125897/500000000 : ℝ)|=(184125897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1841258613/5000000000 : ℝ)|^5775 ≤ (7422914052023/25000000000000 : ℝ)^4751
        have hw : |(1841258613/5000000000 : ℝ)|=(1841258613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_12 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-998581963/10000000000 : ℝ)*x 0 + (5637963227/10000000000 : ℝ)*x 1 + (1274602827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998581963/10000000000 : ℝ)^5775 ≤ (6077392923203/100000000000000 : ℝ)^4751 := by
    have hnat : (998581963 : ℕ)^5775*100000000000000^4751 ≤ 6077392923203^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998581963 10000000000 6077392923203 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5637963227/10000000000 : ℝ)^5775 ≤ (49828834154151/100000000000000 : ℝ)^4751 := by
    have hnat : (5637963227 : ℕ)^5775*100000000000000^4751 ≤ 49828834154151^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637963227 10000000000 49828834154151 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1274602827/2500000000 : ℝ)^5775 ≤ (22046886448821/50000000000000 : ℝ)^4751 := by
    have hnat : (1274602827 : ℕ)^5775*50000000000000^4751 ≤ 22046886448821^4751*2500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274602827 2500000000 22046886448821 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998581963/10000000000 : ℝ), (5637963227/10000000000 : ℝ), (1274602827/2500000000 : ℝ)] ![(6077392923203/100000000000000 : ℝ), (49828834154151/100000000000000 : ℝ), (22046886448821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998581963/10000000000 : ℝ)|^5775 ≤ (6077392923203/100000000000000 : ℝ)^4751
        have hw : |(-998581963/10000000000 : ℝ)|=(998581963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5637963227/10000000000 : ℝ)|^5775 ≤ (49828834154151/100000000000000 : ℝ)^4751
        have hw : |(5637963227/10000000000 : ℝ)|=(5637963227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1274602827/2500000000 : ℝ)|^5775 ≤ (22046886448821/50000000000000 : ℝ)^4751
        have hw : |(1274602827/2500000000 : ℝ)|=(1274602827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_13 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082662059/2000000000 : ℝ)*x 0 + (-1313481991/10000000000 : ℝ)*x 1 + (318650663/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082662059/2000000000 : ℝ)^5775 ≤ (23712931008257/50000000000000 : ℝ)^4751 := by
    have hnat : (1082662059 : ℕ)^5775*50000000000000^4751 ≤ 23712931008257^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082662059 2000000000 23712931008257 50000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313481991/10000000000 : ℝ)^5775 ≤ (2120093104597/25000000000000 : ℝ)^4751 := by
    have hnat : (1313481991 : ℕ)^5775*25000000000000^4751 ≤ 2120093104597^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313481991 10000000000 2120093104597 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318650663/625000000 : ℝ)^5775 ≤ (11023441384709/25000000000000 : ℝ)^4751 := by
    have hnat : (318650663 : ℕ)^5775*25000000000000^4751 ≤ 11023441384709^4751*625000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318650663 625000000 11023441384709 25000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082662059/2000000000 : ℝ), (-1313481991/10000000000 : ℝ), (318650663/625000000 : ℝ)] ![(23712931008257/50000000000000 : ℝ), (2120093104597/25000000000000 : ℝ), (11023441384709/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082662059/2000000000 : ℝ)|^5775 ≤ (23712931008257/50000000000000 : ℝ)^4751
        have hw : |(1082662059/2000000000 : ℝ)|=(1082662059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1313481991/10000000000 : ℝ)|^5775 ≤ (2120093104597/25000000000000 : ℝ)^4751
        have hw : |(-1313481991/10000000000 : ℝ)|=(1313481991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318650663/625000000 : ℝ)|^5775 ≤ (11023441384709/25000000000000 : ℝ)^4751
        have hw : |(318650663/625000000 : ℝ)|=(318650663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_14 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676663811/1250000000 : ℝ)*x 0 + (1019682163/2000000000 : ℝ)*x 1 + (-1313481453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676663811/1250000000 : ℝ)^5775 ≤ (2371293203591/5000000000000 : ℝ)^4751 := by
    have hnat : (676663811 : ℕ)^5775*5000000000000^4751 ≤ 2371293203591^4751*1250000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676663811 1250000000 2371293203591 5000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019682163/2000000000 : ℝ)^5775 ≤ (2204688385747/5000000000000 : ℝ)^4751 := by
    have hnat : (1019682163 : ℕ)^5775*5000000000000^4751 ≤ 2204688385747^4751*2000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019682163 2000000000 2204688385747 5000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313481453/10000000000 : ℝ)^5775 ≤ (8480368196177/100000000000000 : ℝ)^4751 := by
    have hnat : (1313481453 : ℕ)^5775*100000000000000^4751 ≤ 8480368196177^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313481453 10000000000 8480368196177 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676663811/1250000000 : ℝ), (1019682163/2000000000 : ℝ), (-1313481453/10000000000 : ℝ)] ![(2371293203591/5000000000000 : ℝ), (2204688385747/5000000000000 : ℝ), (8480368196177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676663811/1250000000 : ℝ)|^5775 ≤ (2371293203591/5000000000000 : ℝ)^4751
        have hw : |(676663811/1250000000 : ℝ)|=(676663811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1019682163/2000000000 : ℝ)|^5775 ≤ (2204688385747/5000000000000 : ℝ)^4751
        have hw : |(1019682163/2000000000 : ℝ)|=(1019682163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1313481453/10000000000 : ℝ)|^5775 ≤ (8480368196177/100000000000000 : ℝ)^4751
        have hw : |(-1313481453/10000000000 : ℝ)|=(1313481453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1750_box_15 (p : ℝ) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167101811/500000000 : ℝ)*x 0 + (4394243453/10000000000 : ℝ)*x 1 + (2197124003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167101811/500000000 : ℝ)^5775 ≤ (1055551840059/4000000000000 : ℝ)^4751 := by
    have hnat : (167101811 : ℕ)^5775*4000000000000^4751 ≤ 1055551840059^4751*500000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167101811 500000000 1055551840059 4000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394243453/10000000000 : ℝ)^5775 ≤ (36805578812639/100000000000000 : ℝ)^4751 := by
    have hnat : (4394243453 : ℕ)^5775*100000000000000^4751 ≤ 36805578812639^4751*10000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394243453 10000000000 36805578812639 100000000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197124003/5000000000 : ℝ)^5775 ≤ (4600703145923/12500000000000 : ℝ)^4751 := by
    have hnat : (2197124003 : ℕ)^5775*12500000000000^4751 ≤ 4600703145923^4751*5000000000^5775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197124003 5000000000 4600703145923 12500000000000 5775 4751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5775/1024 : ℝ)) 5775 4751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167101811/500000000 : ℝ), (4394243453/10000000000 : ℝ), (2197124003/5000000000 : ℝ)] ![(1055551840059/4000000000000 : ℝ), (36805578812639/100000000000000 : ℝ), (4600703145923/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167101811/500000000 : ℝ)|^5775 ≤ (1055551840059/4000000000000 : ℝ)^4751
        have hw : |(167101811/500000000 : ℝ)|=(167101811/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394243453/10000000000 : ℝ)|^5775 ≤ (36805578812639/100000000000000 : ℝ)^4751
        have hw : |(4394243453/10000000000 : ℝ)|=(4394243453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2197124003/5000000000 : ℝ)|^5775 ≤ (4600703145923/12500000000000 : ℝ)^4751
        have hw : |(2197124003/5000000000 : ℝ)|=(2197124003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1750_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (719/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h) :
    -(68913/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1816/3125 : ℝ) ∧ (40783/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (92899/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (719/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (719/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (719/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (719/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (719/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (719/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1250 : ℝ) ^ (5759/1024 : ℝ) ≤ (67365384436097/50000000000000000000 : ℝ) := by
    have hpowers : (113/1250 : ℝ)^5759 ≤ (67365384436097/50000000000000000000 : ℝ)^1024 := by
      have hnat : (113 : ℕ)^5759*50000000000000000000^1024 ≤ 67365384436097^1024*1250^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1250 67365384436097 50000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1250 : ℝ)) (X := (67365384436097/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (719/4000 : ℝ) ^ (5759/1024 : ℝ) ≤ (3215217995473071/50000000000000000000 : ℝ) := by
    have hpowers : (719/4000 : ℝ)^5759 ≤ (3215217995473071/50000000000000000000 : ℝ)^1024 := by
      have hnat : (719 : ℕ)^5759*50000000000000000000^1024 ≤ 3215217995473071^1024*4000^5759 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        719 4000 3215217995473071 50000000000000000000 5759 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (719/4000 : ℝ)) (X := (3215217995473071/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000067365384436097/25000000000000000000 : ℝ) ≤ (10000004791253847/10000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (25000067365384436097/25000000000000000000 : ℝ)^1024 ≤ (10000004791253847/10000000000000000 : ℝ)^5759 := by
      have hnat : (25000067365384436097 : ℕ)^1024*10000000000000000^5759 ≤ 10000004791253847^5759*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000067365384436097 25000000000000000000 10000004791253847 10000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000004791253847/10000000000000000 : ℝ)) (X := (25000067365384436097/25000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125205161461244323/3125000000000000000 : ℝ) ≤ (5000058365595839/5000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (3125205161461244323/3125000000000000000 : ℝ)^1024 ≤ (5000058365595839/5000000000000000 : ℝ)^5759 := by
      have hnat : (3125205161461244323 : ℕ)^1024*5000000000000000^5759 ≤ 5000058365595839^5759*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125205161461244323 3125000000000000000 5000058365595839 5000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000058365595839/5000000000000000 : ℝ)) (X := (3125205161461244323/3125000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25003215217995473071/25000000000000000000 : ℝ) ≤ (10000228671129509/10000000000000000 : ℝ) ^ (5759/1024 : ℝ) := by
    have hpowers : (25003215217995473071/25000000000000000000 : ℝ)^1024 ≤ (10000228671129509/10000000000000000 : ℝ)^5759 := by
      have hnat : (25003215217995473071 : ℕ)^1024*10000000000000000^5759 ≤ 10000228671129509^5759*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003215217995473071 25000000000000000000 10000228671129509 10000000000000000 1024 5759 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000228671129509/10000000000000000 : ℝ)) (X := (25003215217995473071/25000000000000000000 : ℝ)) (by norm_num) 5759 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(67365384436097/50000000000000000000 : ℝ) ≤ ((17869603787155427693/17870000000000000000 : ℝ)+2*(111939937831/893500000000000 : ℝ)*(113/1250 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (17869603787155427693/17870000000000000000 : ℝ)+2*(111939937831/893500000000000 : ℝ)*(113/1250 : ℝ)=(10000004791253847/10000000000000000 : ℝ) by norm_num, show 1+2*(67365384436097/50000000000000000000 : ℝ)=(25000067365384436097/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3215217995473071/50000000000000000000 : ℝ)+(67365384436097/50000000000000000000 : ℝ) ≤ ((17869603787155427693/17870000000000000000 : ℝ)+(111939937831/893500000000000 : ℝ)*((719/4000 : ℝ)+(113/1250 : ℝ)))^(5759/1024 : ℝ) := by
    rw [show (17869603787155427693/17870000000000000000 : ℝ)+(111939937831/893500000000000 : ℝ)*((719/4000 : ℝ)+(113/1250 : ℝ))=(5000058365595839/5000000000000000 : ℝ) by norm_num, show 1+(3215217995473071/50000000000000000000 : ℝ)+(67365384436097/50000000000000000000 : ℝ)=(3125205161461244323/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3215217995473071/50000000000000000000 : ℝ) ≤ ((17869603787155427693/17870000000000000000 : ℝ)+2*(111939937831/893500000000000 : ℝ)*(719/4000 : ℝ))^(5759/1024 : ℝ) := by
    rw [show (17869603787155427693/17870000000000000000 : ℝ)+2*(111939937831/893500000000000 : ℝ)*(719/4000 : ℝ)=(10000228671129509/10000000000000000 : ℝ) by norm_num, show 1+2*(3215217995473071/50000000000000000000 : ℝ)=(25003215217995473071/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17869603787155427693/17870000000000000000 : ℝ)*(X 1 0+X 2 0)+(111939937831/893500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (719/4000 : ℝ)) (c := (17869603787155427693/17870000000000000000 : ℝ)) (alpha := (111939937831/893500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17869603787155427693/17870000000000000000 : ℝ)*(X 0 1+X 2 1)+(111939937831/893500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (719/4000 : ℝ)) (c := (17869603787155427693/17870000000000000000 : ℝ)) (alpha := (111939937831/893500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17869603787155427693/17870000000000000000 : ℝ)*(X 0 2+X 1 2)+(111939937831/893500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5759/1024 : ℝ)) (lo := (113/1250 : ℝ)) (hi := (719/4000 : ℝ)) (c := (17869603787155427693/17870000000000000000 : ℝ)) (alpha := (111939937831/893500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208863911/2500000000 : ℝ)*X 0 0+(1356325109/2500000000 : ℝ)*X 0 1+(339081249/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2597206113/5000000000 : ℝ)*X 1 0+(-583262631/5000000000 : ℝ)*X 1 1+(1356325099/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((207776509/400000000 : ℝ)*X 2 0+(1356325003/2500000000 : ℝ)*X 2 1+(-1166525107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2273618913/5000000000 : ℝ)*X 0 0+(3796806441/10000000000 : ℝ)*X 0 1+(3796806489/10000000000 : ℝ)*X 0 2+(2273618913/5000000000 : ℝ)*X 1 0+(3796806441/10000000000 : ℝ)*X 1 1+(3796806489/10000000000 : ℝ)*X 1 2+(2273618913/5000000000 : ℝ)*X 2 0+(3796806441/10000000000 : ℝ)*X 2 1+(3796806489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-329721549/2000000000 : ℝ)*X 0 0+(4006679/7812500 : ℝ)*X 0 1+(5128548533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((134826547/250000000 : ℝ)*X 1 0+(-650267539/5000000000 : ℝ)*X 1 1+(5128549821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2696531243/5000000000 : ℝ)*X 2 0+(160267157/312500000 : ℝ)*X 2 1+(-52021413/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((138315219/400000000 : ℝ)*X 0 0+(2169682791/5000000000 : ℝ)*X 0 1+(2169682821/5000000000 : ℝ)*X 0 2+(138315219/400000000 : ℝ)*X 1 0+(2169682791/5000000000 : ℝ)*X 1 1+(2169682821/5000000000 : ℝ)*X 1 2+(138315219/400000000 : ℝ)*X 2 0+(2169682791/5000000000 : ℝ)*X 2 1+(2169682821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-294353397/2000000000 : ℝ)*X 0 0+(4902596203/10000000000 : ℝ)*X 0 1+(1097515221/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152789007/10000000000 : ℝ)*X 1 0+(-45479159/400000000 : ℝ)*X 1 1+(5487578751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2576394917/5000000000 : ℝ)*X 2 0+(219503133/400000000 : ℝ)*X 2 1+(-284244607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2382634381/5000000000 : ℝ)*X 0 0+(184125897/500000000 : ℝ)*X 0 1+(1841258613/5000000000 : ℝ)*X 0 2+(2382634381/5000000000 : ℝ)*X 1 0+(184125897/500000000 : ℝ)*X 1 1+(1841258613/5000000000 : ℝ)*X 1 2+(2382634381/5000000000 : ℝ)*X 2 0+(184125897/500000000 : ℝ)*X 2 1+(1841258613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-998581963/10000000000 : ℝ)*X 0 0+(5637963227/10000000000 : ℝ)*X 0 1+(1274602827/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1082662059/2000000000 : ℝ)*X 1 0+(-1313481991/10000000000 : ℝ)*X 1 1+(318650663/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((676663811/1250000000 : ℝ)*X 2 0+(1019682163/2000000000 : ℝ)*X 2 1+(-1313481453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((167101811/500000000 : ℝ)*X 0 0+(4394243453/10000000000 : ℝ)*X 0 1+(2197124003/5000000000 : ℝ)*X 0 2+(167101811/500000000 : ℝ)*X 1 0+(4394243453/10000000000 : ℝ)*X 1 1+(2197124003/5000000000 : ℝ)*X 1 2+(167101811/500000000 : ℝ)*X 2 0+(4394243453/10000000000 : ℝ)*X 2 1+(2197124003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1750_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-68913/100000 : ℝ) ≤ (-307856370954512198999436402032883/446750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36341437/100000000000000 : ℝ)*(upper3) + (1672577/12500000000000 : ℝ)*(upper4) + (3390313/6250000000000 : ℝ)*(upper5) + (524827180113241/50000000000000 : ℝ)*(major0) + (524827180113241/50000000000000 : ℝ)*(major1) + (524827180113241/50000000000000 : ℝ)*(major2) + (21020703/2500000000000 : ℝ)*(sp2) + (136708291/20000000000000 : ℝ)*(sp3) + (1632422721115519/100000000000000 : ℝ)*(sp4) + (163239071275469/10000000000000 : ℝ)*(sp5) + (816211935143641/50000000000000 : ℝ)*(sp6) + (97970679275311/20000000000000 : ℝ)*(sp7) + (1989999883/100000000000000 : ℝ)*(sp8) + (4249795089/12500000000000 : ℝ)*(sp13) + (48985407991801/10000000000000 : ℝ)*(f.failure) + (816212355557701/50000000000000 : ℝ)*(f.sum) + (209488757694833/44675000000000000000000000000 : ℝ)*base66 + (4427111747906196987/893500000000000000000000000000000 : ℝ)*base68 + (4161407143411696987/893500000000000000000000000000000 : ℝ)*base70 + (9665620493549696987/893500000000000000000000000000000 : ℝ)*base72 + (114659407137767/44675000000000000000000000000 : ℝ)*base73 + (1027959866725696987/893500000000000000000000000000000 : ℝ)*base76 + (3267787736071696987/893500000000000000000000000000000 : ℝ)*base78 + (5744678176592696987/893500000000000000000000000000000 : ℝ)*base80 + (74912458942917/44675000000000000000000000000 : ℝ)*base81 + (2585587/1000000000000000000000 : ℝ)*base89 + (2585587/1000000000000000000000 : ℝ)*base91 + (2585587/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1816/3125 : ℝ) ≤ (519252383441892236546777346952857/893500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43108479/100000000000000 : ℝ)*(upper0) + (1554987/25000000000000 : ℝ)*(upper3) + (78897217/100000000000000 : ℝ)*(upper4) + (1173186185321217/100000000000000 : ℝ)*(major0) + (1173186185321217/100000000000000 : ℝ)*(major1) + (1173186185321217/100000000000000 : ℝ)*(major2) + (444873843480623/25000000000000 : ℝ)*(sp0) + (1779494863638601/100000000000000 : ℝ)*(sp1) + (8897476809939/500000000000 : ℝ)*(sp2) + (109500658911517/20000000000000 : ℝ)*(sp3) + (4893311/250000000000 : ℝ)*(sp5) + (1823719/125000000000 : ℝ)*(sp6) + (31210743/4000000000000 : ℝ)*(sp7) + (361760127/25000000000000 : ℝ)*(sp8) + (6843800935327/1250000000000 : ℝ)*(f.failure) + (1779496820963/100000000000 : ℝ)*(f.sum) + (19802235634949/22337500000000000000000000000 : ℝ)*base66 + (3084213791151802381/1787000000000000000000000000000000 : ℝ)*base67 + (4023671120907802381/1787000000000000000000000000000000 : ℝ)*base69 + (3072235726721802381/1787000000000000000000000000000000 : ℝ)*base71 + (3627847853257/698046875000000000000000000 : ℝ)*base74 + (4433157929428197619/1787000000000000000000000000000000 : ℝ)*base76 + (5886234680383802381/1787000000000000000000000000000000 : ℝ)*base77 + (5311578194116197619/1787000000000000000000000000000000 : ℝ)*base80 + (148667820582399/22337500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (823749/125000000000000000000 : ℝ)*base89 + (823749/125000000000000000000 : ℝ)*base91 + (823749/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40783/50000 : ℝ) ≤ (72881790327782423717743165809663/89350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35141143/50000000000000 : ℝ)*(lower3) + (138014939/100000000000000 : ℝ)*(upper4) + (2426827/20000000000000 : ℝ)*(lower5) + (226522893519097/20000000000000 : ℝ)*(major0) + (226522893519097/20000000000000 : ℝ)*(major1) + (226522893519097/20000000000000 : ℝ)*(major2) + (3352954549/50000000000000 : ℝ)*(sp0) + (90620515347/100000000000000 : ℝ)*(sp1) + (44907210217/50000000000000 : ℝ)*(sp2) + (774553781/3125000000000 : ℝ)*(sp3) + (1709462591951443/100000000000000 : ℝ)*(sp8) + (854689338672597/50000000000000 : ℝ)*(sp9) + (1709379483440107/100000000000000 : ℝ)*(sp10) + (132136306604299/25000000000000 : ℝ)*(sp11) + (528570012138187/100000000000000 : ℝ)*(f.failure) + (1709469297860541/100000000000000 : ℝ)*(f.sum) + (14661279169097/2233750000000000000000000000 : ℝ)*base66 + (1136649638010306779/357400000000000000000000000000000 : ℝ)*base68 + (28397177170893221/357400000000000000000000000000000 : ℝ)*base69 + (3026239933807306779/357400000000000000000000000000000 : ℝ)*base72 + (15238863186273/8935000000000000000000000000 : ℝ)*base74 + (1214506412055706779/357400000000000000000000000000000 : ℝ)*base76 + (1275759104406506779/357400000000000000000000000000000 : ℝ)*base78 + (1134572545722706779/357400000000000000000000000000000 : ℝ)*base80 + (749630426643/8935000000000000000000000000 : ℝ)*base82 + (85623431/10000000000000000000000 : ℝ)*base90 + (85623431/10000000000000000000000 : ℝ)*base92 + (85623431/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-92899/100000 : ℝ) ≤ (-51877037091368113621995691705071/55843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25549997/100000000000000 : ℝ)*(lower1) + (1250423/800000000000 : ℝ)*(lower3) + (57178321/100000000000000 : ℝ)*(lower4) + (114912791/50000000000000 : ℝ)*(upper5) + (148568356907349/12500000000000 : ℝ)*(major0) + (148568356907349/12500000000000 : ℝ)*(major1) + (148568356907349/12500000000000 : ℝ)*(major2) + (168530707/50000000000000 : ℝ)*(sp4) + (45905114093/100000000000000 : ℝ)*(sp6) + (2465490819/20000000000000 : ℝ)*(sp7) + (1853386349209093/100000000000000 : ℝ)*(sp12) + (1853386686270507/100000000000000 : ℝ)*(sp13) + (926670390578207/50000000000000 : ℝ)*(sp14) + (34666267816167/6250000000000 : ℝ)*(sp15) + (554672612512767/100000000000000 : ℝ)*(f.failure) + (1853386686270507/100000000000000 : ℝ)*(f.sum) + (10483962357353/2792187500000000000000000000 : ℝ)*base66 + (1056563557627820857/223375000000000000000000000000000 : ℝ)*base67 + (1292686606628195857/223375000000000000000000000000000 : ℝ)*base69 + (168838863618554143/223375000000000000000000000000000 : ℝ)*base72 + (70527885632423/44675000000000000000000000000 : ℝ)*base74 + (413011519921945857/223375000000000000000000000000000 : ℝ)*base75 + (169593099712070857/223375000000000000000000000000000 : ℝ)*base77 + (479287983660695857/223375000000000000000000000000000 : ℝ)*base79 + (35106420543027/44675000000000000000000000000 : ℝ)*base81 + (37327029/10000000000000000000000 : ℝ)*base89 + (37327029/10000000000000000000000 : ℝ)*base91 + (37327029/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1750_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (719/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1816/3125 : ℝ) else (40783/50000 : ℝ) ≤ X j i ∧ X j i ≤ (92899/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1750_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1750_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1816/3125 : ℝ) else (40783/50000 : ℝ) ≤ X j i ∧ X j i ≤ (92899/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1750_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1750_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5759/1024 : ℝ) ≤ p) (hpb : p ≤ (5775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (214278987/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2247/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(68913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1816/3125 : ℝ) else (40783/50000 : ℝ) ≤ X j i ∧ X j i ≤ (92899/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1750_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

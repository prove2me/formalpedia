-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1179_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:49:12.927664+00:00
-- url     : https://prove2.me/submissions/ccfee8c5-d9d3-431e-b319-901fa46d068d

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
theorem support_rectangle_w1179_s6_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149293127/10000000000 : ℝ)*x 0 + (674080373/1250000000 : ℝ)*x 1 + (2633025741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149293127/10000000000 : ℝ)^2093 ≤ (13063588419463/100000000000000 : ℝ)^1581 := by
    have hnat : (2149293127 : ℕ)^2093*100000000000000^1581 ≤ 13063588419463^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149293127 10000000000 13063588419463 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674080373/1250000000 : ℝ)^2093 ≤ (4415163610539/10000000000000 : ℝ)^1581 := by
    have hnat : (674080373 : ℕ)^2093*10000000000000^1581 ≤ 4415163610539^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674080373 1250000000 4415163610539 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633025741/5000000000 : ℝ)^2093 ≤ (267404846611/625000000000 : ℝ)^1581 := by
    have hnat : (2633025741 : ℕ)^2093*625000000000^1581 ≤ 267404846611^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633025741 5000000000 267404846611 625000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149293127/10000000000 : ℝ), (674080373/1250000000 : ℝ), (2633025741/5000000000 : ℝ)] ![(13063588419463/100000000000000 : ℝ), (4415163610539/10000000000000 : ℝ), (267404846611/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149293127/10000000000 : ℝ)|^2093 ≤ (13063588419463/100000000000000 : ℝ)^1581
        have hw : |(-2149293127/10000000000 : ℝ)|=(2149293127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674080373/1250000000 : ℝ)|^2093 ≤ (4415163610539/10000000000000 : ℝ)^1581
        have hw : |(674080373/1250000000 : ℝ)|=(674080373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633025741/5000000000 : ℝ)|^2093 ≤ (267404846611/625000000000 : ℝ)^1581
        have hw : |(2633025741/5000000000 : ℝ)|=(2633025741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068936239/2000000000 : ℝ)*x 0 + (-1106748501/5000000000 : ℝ)*x 1 + (5266051879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068936239/2000000000 : ℝ)^2093 ≤ (21816268241229/50000000000000 : ℝ)^1581 := by
    have hnat : (1068936239 : ℕ)^2093*50000000000000^1581 ≤ 21816268241229^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068936239 2000000000 21816268241229 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106748501/5000000000 : ℝ)^2093 ≤ (13582683774637/100000000000000 : ℝ)^1581 := by
    have hnat : (1106748501 : ℕ)^2093*100000000000000^1581 ≤ 13582683774637^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106748501 5000000000 13582683774637 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266051879/10000000000 : ℝ)^2093 ≤ (42784779727801/100000000000000 : ℝ)^1581 := by
    have hnat : (5266051879 : ℕ)^2093*100000000000000^1581 ≤ 42784779727801^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266051879 10000000000 42784779727801 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068936239/2000000000 : ℝ), (-1106748501/5000000000 : ℝ), (5266051879/10000000000 : ℝ)] ![(21816268241229/50000000000000 : ℝ), (13582683774637/100000000000000 : ℝ), (42784779727801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068936239/2000000000 : ℝ)|^2093 ≤ (21816268241229/50000000000000 : ℝ)^1581
        have hw : |(1068936239/2000000000 : ℝ)|=(1068936239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1106748501/5000000000 : ℝ)|^2093 ≤ (13582683774637/100000000000000 : ℝ)^1581
        have hw : |(-1106748501/5000000000 : ℝ)|=(1106748501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266051879/10000000000 : ℝ)|^2093 ≤ (42784779727801/100000000000000 : ℝ)^1581
        have hw : |(5266051879/10000000000 : ℝ)|=(5266051879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068936243/2000000000 : ℝ)*x 0 + (5266051123/10000000000 : ℝ)*x 1 + (-276687247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068936243/2000000000 : ℝ)^2093 ≤ (43632536698609/100000000000000 : ℝ)^1581 := by
    have hnat : (1068936243 : ℕ)^2093*100000000000000^1581 ≤ 43632536698609^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068936243 2000000000 43632536698609 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266051123/10000000000 : ℝ)^2093 ≤ (42784771596439/100000000000000 : ℝ)^1581 := by
    have hnat : (5266051123 : ℕ)^2093*100000000000000^1581 ≤ 42784771596439^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266051123 10000000000 42784771596439 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276687247/1250000000 : ℝ)^2093 ≤ (6791345843471/50000000000000 : ℝ)^1581 := by
    have hnat : (276687247 : ℕ)^2093*50000000000000^1581 ≤ 6791345843471^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276687247 1250000000 6791345843471 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068936243/2000000000 : ℝ), (5266051123/10000000000 : ℝ), (-276687247/1250000000 : ℝ)] ![(43632536698609/100000000000000 : ℝ), (42784771596439/100000000000000 : ℝ), (6791345843471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068936243/2000000000 : ℝ)|^2093 ≤ (43632536698609/100000000000000 : ℝ)^1581
        have hw : |(1068936243/2000000000 : ℝ)|=(1068936243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266051123/10000000000 : ℝ)|^2093 ≤ (42784771596439/100000000000000 : ℝ)^1581
        have hw : |(5266051123/10000000000 : ℝ)|=(5266051123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276687247/1250000000 : ℝ)|^2093 ≤ (6791345843471/50000000000000 : ℝ)^1581
        have hw : |(-276687247/1250000000 : ℝ)|=(276687247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359472459/10000000000 : ℝ)*x 0 + (4234452731/10000000000 : ℝ)*x 1 + (897626703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359472459/10000000000 : ℝ)^2093 ≤ (33317022452931/100000000000000 : ℝ)^1581 := by
    have hnat : (4359472459 : ℕ)^2093*100000000000000^1581 ≤ 33317022452931^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359472459 10000000000 33317022452931 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234452731/10000000000 : ℝ)^2093 ≤ (16029028926543/50000000000000 : ℝ)^1581 := by
    have hnat : (4234452731 : ℕ)^2093*50000000000000^1581 ≤ 16029028926543^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234452731 10000000000 16029028926543 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897626703/2000000000 : ℝ)^2093 ≤ (17312459834547/50000000000000 : ℝ)^1581 := by
    have hnat : (897626703 : ℕ)^2093*50000000000000^1581 ≤ 17312459834547^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897626703 2000000000 17312459834547 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359472459/10000000000 : ℝ), (4234452731/10000000000 : ℝ), (897626703/2000000000 : ℝ)] ![(33317022452931/100000000000000 : ℝ), (16029028926543/50000000000000 : ℝ), (17312459834547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359472459/10000000000 : ℝ)|^2093 ≤ (33317022452931/100000000000000 : ℝ)^1581
        have hw : |(4359472459/10000000000 : ℝ)|=(4359472459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234452731/10000000000 : ℝ)|^2093 ≤ (16029028926543/50000000000000 : ℝ)^1581
        have hw : |(4234452731/10000000000 : ℝ)|=(4234452731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897626703/2000000000 : ℝ)|^2093 ≤ (17312459834547/50000000000000 : ℝ)^1581
        have hw : |(897626703/2000000000 : ℝ)|=(897626703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074648929/5000000000 : ℝ)*x 0 + (526637121/1000000000 : ℝ)*x 1 + (1348080547/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074648929/5000000000 : ℝ)^2093 ≤ (13063626487221/100000000000000 : ℝ)^1581 := by
    have hnat : (1074648929 : ℕ)^2093*100000000000000^1581 ≤ 13063626487221^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074648929 5000000000 13063626487221 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526637121/1000000000 : ℝ)^2093 ≤ (2674263400779/6250000000000 : ℝ)^1581 := by
    have hnat : (526637121 : ℕ)^2093*6250000000000^1581 ≤ 2674263400779^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526637121 1000000000 2674263400779 6250000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348080547/2500000000 : ℝ)^2093 ≤ (11037039771221/25000000000000 : ℝ)^1581 := by
    have hnat : (1348080547 : ℕ)^2093*25000000000000^1581 ≤ 11037039771221^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348080547 2500000000 11037039771221 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074648929/5000000000 : ℝ), (526637121/1000000000 : ℝ), (1348080547/2500000000 : ℝ)] ![(13063626487221/100000000000000 : ℝ), (2674263400779/6250000000000 : ℝ), (11037039771221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074648929/5000000000 : ℝ)|^2093 ≤ (13063626487221/100000000000000 : ℝ)^1581
        have hw : |(-1074648929/5000000000 : ℝ)|=(1074648929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526637121/1000000000 : ℝ)|^2093 ≤ (2674263400779/6250000000000 : ℝ)^1581
        have hw : |(526637121/1000000000 : ℝ)|=(526637121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348080547/2500000000 : ℝ)|^2093 ≤ (11037039771221/25000000000000 : ℝ)^1581
        have hw : |(1348080547/2500000000 : ℝ)|=(1348080547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312522287/10000000000 : ℝ)*x 0 + (-2087226481/10000000000 : ℝ)*x 1 + (5392322217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312522287/10000000000 : ℝ)^2093 ≤ (43285317550507/100000000000000 : ℝ)^1581 := by
    have hnat : (5312522287 : ℕ)^2093*100000000000000^1581 ≤ 43285317550507^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312522287 10000000000 43285317550507 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087226481/10000000000 : ℝ)^2093 ≤ (12566523028041/100000000000000 : ℝ)^1581 := by
    have hnat : (2087226481 : ℕ)^2093*100000000000000^1581 ≤ 12566523028041^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087226481 10000000000 12566523028041 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392322217/10000000000 : ℝ)^2093 ≤ (11037039849801/25000000000000 : ℝ)^1581 := by
    have hnat : (5392322217 : ℕ)^2093*25000000000000^1581 ≤ 11037039849801^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392322217 10000000000 11037039849801 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312522287/10000000000 : ℝ), (-2087226481/10000000000 : ℝ), (5392322217/10000000000 : ℝ)] ![(43285317550507/100000000000000 : ℝ), (12566523028041/100000000000000 : ℝ), (11037039849801/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312522287/10000000000 : ℝ)|^2093 ≤ (43285317550507/100000000000000 : ℝ)^1581
        have hw : |(5312522287/10000000000 : ℝ)|=(5312522287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087226481/10000000000 : ℝ)|^2093 ≤ (12566523028041/100000000000000 : ℝ)^1581
        have hw : |(-2087226481/10000000000 : ℝ)|=(2087226481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392322217/10000000000 : ℝ)|^2093 ≤ (11037039849801/25000000000000 : ℝ)^1581
        have hw : |(5392322217/10000000000 : ℝ)|=(5392322217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332032643/625000000 : ℝ)*x 0 + (1348080561/2500000000 : ℝ)*x 1 + (-521806611/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332032643/625000000 : ℝ)^2093 ≤ (43285317561293/100000000000000 : ℝ)^1581 := by
    have hnat : (332032643 : ℕ)^2093*100000000000000^1581 ≤ 43285317561293^1581*625000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332032643 625000000 43285317561293 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348080561/2500000000 : ℝ)^2093 ≤ (44148159691847/100000000000000 : ℝ)^1581 := by
    have hnat : (1348080561 : ℕ)^2093*100000000000000^1581 ≤ 44148159691847^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348080561 2500000000 44148159691847 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521806611/2500000000 : ℝ)^2093 ≤ (2513304546627/20000000000000 : ℝ)^1581 := by
    have hnat : (521806611 : ℕ)^2093*20000000000000^1581 ≤ 2513304546627^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521806611 2500000000 2513304546627 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332032643/625000000 : ℝ), (1348080561/2500000000 : ℝ), (-521806611/2500000000 : ℝ)] ![(43285317561293/100000000000000 : ℝ), (44148159691847/100000000000000 : ℝ), (2513304546627/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332032643/625000000 : ℝ)|^2093 ≤ (43285317561293/100000000000000 : ℝ)^1581
        have hw : |(332032643/625000000 : ℝ)|=(332032643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348080561/2500000000 : ℝ)|^2093 ≤ (44148159691847/100000000000000 : ℝ)^1581
        have hw : |(1348080561/2500000000 : ℝ)|=(1348080561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521806611/2500000000 : ℝ)|^2093 ≤ (2513304546627/20000000000000 : ℝ)^1581
        have hw : |(-521806611/2500000000 : ℝ)|=(521806611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s6_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1089870607/2500000000 : ℝ)*x 0 + (4487492241/10000000000 : ℝ)*x 1 + (423509611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089870607/2500000000 : ℝ)^2093 ≤ (33317123313487/100000000000000 : ℝ)^1581 := by
    have hnat : (1089870607 : ℕ)^2093*100000000000000^1581 ≤ 33317123313487^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089870607 2500000000 33317123313487 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487492241/10000000000 : ℝ)^2093 ≤ (34618370383203/100000000000000 : ℝ)^1581 := by
    have hnat : (4487492241 : ℕ)^2093*100000000000000^1581 ≤ 34618370383203^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487492241 10000000000 34618370383203 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423509611/1000000000 : ℝ)^2093 ≤ (6412901259151/20000000000000 : ℝ)^1581 := by
    have hnat : (423509611 : ℕ)^2093*20000000000000^1581 ≤ 6412901259151^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423509611 1000000000 6412901259151 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089870607/2500000000 : ℝ), (4487492241/10000000000 : ℝ), (423509611/1000000000 : ℝ)] ![(33317123313487/100000000000000 : ℝ), (34618370383203/100000000000000 : ℝ), (6412901259151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089870607/2500000000 : ℝ)|^2093 ≤ (33317123313487/100000000000000 : ℝ)^1581
        have hw : |(1089870607/2500000000 : ℝ)|=(1089870607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487492241/10000000000 : ℝ)|^2093 ≤ (34618370383203/100000000000000 : ℝ)^1581
        have hw : |(4487492241/10000000000 : ℝ)|=(4487492241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423509611/1000000000 : ℝ)|^2093 ≤ (6412901259151/20000000000000 : ℝ)^1581
        have hw : |(423509611/1000000000 : ℝ)|=(423509611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2279/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1421/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1421/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1421/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1421/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1421/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1421/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1421/12500 : ℝ) ^ (8371/2048 : ℝ) ≤ (55240910103149/400000000000000000 : ℝ) := by
    have hpowers : (1421/12500 : ℝ)^8371 ≤ (55240910103149/400000000000000000 : ℝ)^2048 := by
      have hnat : (1421 : ℕ)^8371*400000000000000000^2048 ≤ 55240910103149^2048*12500^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1421 12500 55240910103149 400000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1421/12500 : ℝ)) (X := (55240910103149/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (8371/2048 : ℝ) ≤ (33344155329537511/100000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^8371 ≤ (33344155329537511/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1763 : ℕ)^8371*100000000000000000000^2048 ≤ 33344155329537511^2048*12500^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 33344155329537511 100000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (33344155329537511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (200055240910103149/200000000000000000 : ℝ) ≤ (312521114857897/312500000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (200055240910103149/200000000000000000 : ℝ)^2048 ≤ (312521114857897/312500000000000 : ℝ)^8371 := by
      have hnat : (200055240910103149 : ℕ)^2048*312500000000000^8371 ≤ 312521114857897^8371*200000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200055240910103149 200000000000000000 312521114857897 312500000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312521114857897/312500000000000 : ℝ)) (X := (200055240910103149/200000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047154382855324761/100000000000000000000 : ℝ) ≤ (10001153446211407/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (100047154382855324761/100000000000000000000 : ℝ)^2048 ≤ (10001153446211407/10000000000000000 : ℝ)^8371 := by
      have hnat : (100047154382855324761 : ℕ)^2048*10000000000000000^8371 ≤ 10001153446211407^8371*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047154382855324761 100000000000000000000 10001153446211407 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001153446211407/10000000000000000 : ℝ)) (X := (100047154382855324761/100000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033344155329537511/50000000000000000000 : ℝ) ≤ (1000163121697011/1000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (50033344155329537511/50000000000000000000 : ℝ)^2048 ≤ (1000163121697011/1000000000000000 : ℝ)^8371 := by
      have hnat : (50033344155329537511 : ℕ)^2048*1000000000000000^8371 ≤ 1000163121697011^8371*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033344155329537511 50000000000000000000 1000163121697011 1000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000163121697011/1000000000000000 : ℝ)) (X := (50033344155329537511/50000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(55240910103149/400000000000000000 : ℝ) ≤ ((1709436628254295421/1710000000000000000 : ℝ)+2*(477770758703/273600000000000 : ℝ)*(1421/12500 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (1709436628254295421/1710000000000000000 : ℝ)+2*(477770758703/273600000000000 : ℝ)*(1421/12500 : ℝ)=(312521114857897/312500000000000 : ℝ) by norm_num, show 1+2*(55240910103149/400000000000000000 : ℝ)=(200055240910103149/200000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33344155329537511/100000000000000000000 : ℝ)+(55240910103149/400000000000000000 : ℝ) ≤ ((1709436628254295421/1710000000000000000 : ℝ)+(477770758703/273600000000000 : ℝ)*((1763/12500 : ℝ)+(1421/12500 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (1709436628254295421/1710000000000000000 : ℝ)+(477770758703/273600000000000 : ℝ)*((1763/12500 : ℝ)+(1421/12500 : ℝ))=(10001153446211407/10000000000000000 : ℝ) by norm_num, show 1+(33344155329537511/100000000000000000000 : ℝ)+(55240910103149/400000000000000000 : ℝ)=(100047154382855324761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33344155329537511/100000000000000000000 : ℝ) ≤ ((1709436628254295421/1710000000000000000 : ℝ)+2*(477770758703/273600000000000 : ℝ)*(1763/12500 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (1709436628254295421/1710000000000000000 : ℝ)+2*(477770758703/273600000000000 : ℝ)*(1763/12500 : ℝ)=(1000163121697011/1000000000000000 : ℝ) by norm_num, show 1+2*(33344155329537511/100000000000000000000 : ℝ)=(50033344155329537511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1709436628254295421/1710000000000000000 : ℝ)*(X 1 0+X 2 0)+(477770758703/273600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (1709436628254295421/1710000000000000000 : ℝ)) (alpha := (477770758703/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1709436628254295421/1710000000000000000 : ℝ)*(X 0 1+X 2 1)+(477770758703/273600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (1709436628254295421/1710000000000000000 : ℝ)) (alpha := (477770758703/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1709436628254295421/1710000000000000000 : ℝ)*(X 0 2+X 1 2)+(477770758703/273600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (1421/12500 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (1709436628254295421/1710000000000000000 : ℝ)) (alpha := (477770758703/273600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149293127/10000000000 : ℝ)*X 0 0+(674080373/1250000000 : ℝ)*X 0 1+(2633025741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068936239/2000000000 : ℝ)*X 1 0+(-1106748501/5000000000 : ℝ)*X 1 1+(5266051879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068936243/2000000000 : ℝ)*X 2 0+(5266051123/10000000000 : ℝ)*X 2 1+(-276687247/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359472459/10000000000 : ℝ)*X 0 0+(4234452731/10000000000 : ℝ)*X 0 1+(897626703/2000000000 : ℝ)*X 0 2+(4359472459/10000000000 : ℝ)*X 1 0+(4234452731/10000000000 : ℝ)*X 1 1+(897626703/2000000000 : ℝ)*X 1 2+(4359472459/10000000000 : ℝ)*X 2 0+(4234452731/10000000000 : ℝ)*X 2 1+(897626703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074648929/5000000000 : ℝ)*X 0 0+(526637121/1000000000 : ℝ)*X 0 1+(1348080547/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312522287/10000000000 : ℝ)*X 1 0+(-2087226481/10000000000 : ℝ)*X 1 1+(5392322217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332032643/625000000 : ℝ)*X 2 0+(1348080561/2500000000 : ℝ)*X 2 1+(-521806611/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089870607/2500000000 : ℝ)*X 0 0+(4487492241/10000000000 : ℝ)*X 0 1+(423509611/1000000000 : ℝ)*X 0 2+(1089870607/2500000000 : ℝ)*X 1 0+(4487492241/10000000000 : ℝ)*X 1 1+(423509611/1000000000 : ℝ)*X 1 2+(1089870607/2500000000 : ℝ)*X 2 0+(4487492241/10000000000 : ℝ)*X 2 1+(423509611/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4988204738055171543913/760000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395084379/100000000000000 : ℝ)*(base19) + (75508709/20000000000000 : ℝ)*(base23) + (121715611/100000000000000 : ℝ)*(upper2) + (28225463/10000000000000 : ℝ)*(upper3) + (2960371776455711/50000000000000 : ℝ)*(major0) + (2960371776455711/50000000000000 : ℝ)*(major1) + (2960371776455711/50000000000000 : ℝ)*(major2) + (315978465413081/4000000000000 : ℝ)*(sp0) + (315979141410951/4000000000000 : ℝ)*(sp1) + (987429109583519/12500000000000 : ℝ)*(sp2) + (3941983205089703/100000000000000 : ℝ)*(sp3) + (1729503113/10000000000000 : ℝ)*(sp4) + (45676146457/100000000000000 : ℝ)*(sp6) + (24751594071/100000000000000 : ℝ)*(sp7) + (1971003978341887/50000000000000 : ℝ)*(f.failure) + (3949739465179077/50000000000000 : ℝ)*(f.sum) + (7631846571167/6840000000000000000000000000 : ℝ)*base66 + (548713881232694419/85500000000000000000000000000000 : ℝ)*base68 + (374193969438194419/85500000000000000000000000000000 : ℝ)*base70 + (953299307185694419/85500000000000000000000000000000 : ℝ)*base72 + (10138105362527/6840000000000000000000000000 : ℝ)*base74 + (257432173219305581/85500000000000000000000000000000 : ℝ)*base75 + (147193664693805581/85500000000000000000000000000000 : ℝ)*base77 + (680501295775305581/85500000000000000000000000000000 : ℝ)*base79 + (38272264366967/6840000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (28832429/2500000000000000000000 : ℝ)*base89 + (28832429/2500000000000000000000 : ℝ)*base91 + (28832429/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96906408062846032499227/37500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (213365197/50000000000000 : ℝ)*(base19) + (109058883/20000000000000 : ℝ)*(base23) + (17879557/25000000000000 : ℝ)*(upper3) + (8484853/20000000000000 : ℝ)*(lower4) + (7346321/20000000000000 : ℝ)*(upper5) + (1190162070674663/20000000000000 : ℝ)*(major0) + (1190162070674663/20000000000000 : ℝ)*(major1) + (1190162070674663/20000000000000 : ℝ)*(major2) + (11731196279/100000000000000 : ℝ)*(sp1) + (1117407881/6250000000000 : ℝ)*(sp2) + (7939594305487313/100000000000000 : ℝ)*(sp4) + (24811194211127/312500000000 : ℝ)*(sp5) + (3969787940833401/50000000000000 : ℝ)*(sp6) + (1981013157560139/50000000000000 : ℝ)*(sp7) + (1981013157560139/50000000000000 : ℝ)*(f.failure) + (7939594305487313/100000000000000 : ℝ)*(f.sum) + (253388210611/144000000000000000000000000 : ℝ)*base65 + (33050839281424967/1800000000000000000000000000000 : ℝ)*base67 + (32324903428624967/1800000000000000000000000000000 : ℝ)*base69 + (7661039332375033/1800000000000000000000000000000 : ℝ)*base72 + (1040348186131/144000000000000000000000000 : ℝ)*base73 + (47930730130024967/1800000000000000000000000000000 : ℝ)*base75 + (4067918111824967/1800000000000000000000000000000 : ℝ)*base77 + (26853275902624967/1800000000000000000000000000000 : ℝ)*base79 + (386008557907/144000000000000000000000000 : ℝ)*base81 + (151313/2500000000000000000000 : ℝ)*base89 + (151313/2500000000000000000000 : ℝ)*base91 + (151313/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1179_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1179_s7_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-268664511/1250000000 : ℝ)*x 0 + (2696185573/5000000000 : ℝ)*x 1 + (2633154119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268664511/1250000000 : ℝ)^2093 ≤ (1306377317427/10000000000000 : ℝ)^1581 := by
    have hnat : (268664511 : ℕ)^2093*10000000000000^1581 ≤ 1306377317427^1581*1250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268664511 1250000000 1306377317427 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696185573/5000000000 : ℝ)^2093 ≤ (8829737944597/20000000000000 : ℝ)^1581 := by
    have hnat : (2696185573 : ℕ)^2093*20000000000000^1581 ≤ 8829737944597^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696185573 5000000000 8829737944597 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633154119/5000000000 : ℝ)^2093 ≤ (42787537088097/100000000000000 : ℝ)^1581 := by
    have hnat : (2633154119 : ℕ)^2093*100000000000000^1581 ≤ 42787537088097^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633154119 5000000000 42787537088097 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268664511/1250000000 : ℝ), (2696185573/5000000000 : ℝ), (2633154119/5000000000 : ℝ)] ![(1306377317427/10000000000000 : ℝ), (8829737944597/20000000000000 : ℝ), (42787537088097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268664511/1250000000 : ℝ)|^2093 ≤ (1306377317427/10000000000000 : ℝ)^1581
        have hw : |(-268664511/1250000000 : ℝ)|=(268664511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696185573/5000000000 : ℝ)|^2093 ≤ (8829737944597/20000000000000 : ℝ)^1581
        have hw : |(2696185573/5000000000 : ℝ)|=(2696185573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633154119/5000000000 : ℝ)|^2093 ≤ (42787537088097/100000000000000 : ℝ)^1581
        have hw : |(2633154119/5000000000 : ℝ)|=(2633154119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344612519/10000000000 : ℝ)*x 0 + (-34582009/156250000 : ℝ)*x 1 + (5266308509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344612519/10000000000 : ℝ)^2093 ≤ (43631794266817/100000000000000 : ℝ)^1581 := by
    have hnat : (5344612519 : ℕ)^2093*100000000000000^1581 ≤ 43631794266817^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344612519 10000000000 43631794266817 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34582009/156250000 : ℝ)^2093 ≤ (13580665718867/100000000000000 : ℝ)^1581 := by
    have hnat : (34582009 : ℕ)^2093*100000000000000^1581 ≤ 13580665718867^1581*156250000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34582009 156250000 13580665718867 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266308509/10000000000 : ℝ)^2093 ≤ (10696885000739/25000000000000 : ℝ)^1581 := by
    have hnat : (5266308509 : ℕ)^2093*25000000000000^1581 ≤ 10696885000739^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266308509 10000000000 10696885000739 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344612519/10000000000 : ℝ), (-34582009/156250000 : ℝ), (5266308509/10000000000 : ℝ)] ![(43631794266817/100000000000000 : ℝ), (13580665718867/100000000000000 : ℝ), (10696885000739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344612519/10000000000 : ℝ)|^2093 ≤ (43631794266817/100000000000000 : ℝ)^1581
        have hw : |(5344612519/10000000000 : ℝ)|=(5344612519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34582009/156250000 : ℝ)|^2093 ≤ (13580665718867/100000000000000 : ℝ)^1581
        have hw : |(-34582009/156250000 : ℝ)|=(34582009/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266308509/10000000000 : ℝ)|^2093 ≤ (10696885000739/25000000000000 : ℝ)^1581
        have hw : |(5266308509/10000000000 : ℝ)|=(5266308509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (534461267/1000000000 : ℝ)*x 0 + (2633154333/5000000000 : ℝ)*x 1 + (-2213248167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534461267/1000000000 : ℝ)^2093 ≤ (21815897949373/50000000000000 : ℝ)^1581 := by
    have hnat : (534461267 : ℕ)^2093*50000000000000^1581 ≤ 21815897949373^1581*1000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534461267 1000000000 21815897949373 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633154333/5000000000 : ℝ)^2093 ≤ (42787541691639/100000000000000 : ℝ)^1581 := by
    have hnat : (2633154333 : ℕ)^2093*100000000000000^1581 ≤ 42787541691639^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633154333 5000000000 42787541691639 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213248167/10000000000 : ℝ)^2093 ≤ (1358066239647/10000000000000 : ℝ)^1581 := by
    have hnat : (2213248167 : ℕ)^2093*10000000000000^1581 ≤ 1358066239647^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213248167 10000000000 1358066239647 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534461267/1000000000 : ℝ), (2633154333/5000000000 : ℝ), (-2213248167/10000000000 : ℝ)] ![(21815897949373/50000000000000 : ℝ), (42787541691639/100000000000000 : ℝ), (1358066239647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534461267/1000000000 : ℝ)|^2093 ≤ (21815897949373/50000000000000 : ℝ)^1581
        have hw : |(534461267/1000000000 : ℝ)|=(534461267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633154333/5000000000 : ℝ)|^2093 ≤ (42787541691639/100000000000000 : ℝ)^1581
        have hw : |(2633154333/5000000000 : ℝ)|=(2633154333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213248167/10000000000 : ℝ)|^2093 ≤ (1358066239647/10000000000000 : ℝ)^1581
        have hw : |(-2213248167/10000000000 : ℝ)|=(2213248167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (21797433/50000000 : ℝ)*x 0 + (4234980903/10000000000 : ℝ)*x 1 + (2243800587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21797433/50000000 : ℝ)^2093 ≤ (4164645690423/12500000000000 : ℝ)^1581 := by
    have hnat : (21797433 : ℕ)^2093*12500000000000^1581 ≤ 4164645690423^1581*50000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21797433 50000000 4164645690423 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234980903/10000000000 : ℝ)^2093 ≤ (4007918947331/12500000000000 : ℝ)^1581 := by
    have hnat : (4234980903 : ℕ)^2093*12500000000000^1581 ≤ 4007918947331^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234980903 10000000000 4007918947331 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243800587/5000000000 : ℝ)^2093 ≤ (34619482886839/100000000000000 : ℝ)^1581 := by
    have hnat : (2243800587 : ℕ)^2093*100000000000000^1581 ≤ 34619482886839^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243800587 5000000000 34619482886839 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21797433/50000000 : ℝ), (4234980903/10000000000 : ℝ), (2243800587/5000000000 : ℝ)] ![(4164645690423/12500000000000 : ℝ), (4007918947331/12500000000000 : ℝ), (34619482886839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21797433/50000000 : ℝ)|^2093 ≤ (4164645690423/12500000000000 : ℝ)^1581
        have hw : |(21797433/50000000 : ℝ)|=(21797433/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234980903/10000000000 : ℝ)|^2093 ≤ (4007918947331/12500000000000 : ℝ)^1581
        have hw : |(4234980903/10000000000 : ℝ)|=(4234980903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243800587/5000000000 : ℝ)|^2093 ≤ (34619482886839/100000000000000 : ℝ)^1581
        have hw : |(2243800587/5000000000 : ℝ)|=(2243800587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074660213/5000000000 : ℝ)*x 0 + (2633312771/5000000000 : ℝ)*x 1 + (5392053037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074660213/5000000000 : ℝ)^2093 ≤ (13063808079893/100000000000000 : ℝ)^1581 := by
    have hnat : (1074660213 : ℕ)^2093*100000000000000^1581 ≤ 13063808079893^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074660213 5000000000 13063808079893 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633312771/5000000000 : ℝ)^2093 ≤ (10697737506047/25000000000000 : ℝ)^1581 := by
    have hnat : (2633312771 : ℕ)^2093*25000000000000^1581 ≤ 10697737506047^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633312771 5000000000 10697737506047 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392053037/10000000000 : ℝ)^2093 ≤ (44145241882151/100000000000000 : ℝ)^1581 := by
    have hnat : (5392053037 : ℕ)^2093*100000000000000^1581 ≤ 44145241882151^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392053037 10000000000 44145241882151 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074660213/5000000000 : ℝ), (2633312771/5000000000 : ℝ), (5392053037/10000000000 : ℝ)] ![(13063808079893/100000000000000 : ℝ), (10697737506047/25000000000000 : ℝ), (44145241882151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074660213/5000000000 : ℝ)|^2093 ≤ (13063808079893/100000000000000 : ℝ)^1581
        have hw : |(-1074660213/5000000000 : ℝ)|=(1074660213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633312771/5000000000 : ℝ)|^2093 ≤ (10697737506047/25000000000000 : ℝ)^1581
        have hw : |(2633312771/5000000000 : ℝ)|=(2633312771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392053037/10000000000 : ℝ)|^2093 ≤ (44145241882151/100000000000000 : ℝ)^1581
        have hw : |(5392053037/10000000000 : ℝ)|=(5392053037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312588223/10000000000 : ℝ)*x 0 + (-1043751643/5000000000 : ℝ)*x 1 + (2696026519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312588223/10000000000 : ℝ)^2093 ≤ (135268839891/312500000000 : ℝ)^1581 := by
    have hnat : (5312588223 : ℕ)^2093*312500000000^1581 ≤ 135268839891^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312588223 10000000000 135268839891 312500000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043751643/5000000000 : ℝ)^2093 ≤ (2513745867239/20000000000000 : ℝ)^1581 := by
    have hnat : (1043751643 : ℕ)^2093*20000000000000^1581 ≤ 2513745867239^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043751643 5000000000 2513745867239 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696026519/5000000000 : ℝ)^2093 ≤ (4414524189299/10000000000000 : ℝ)^1581 := by
    have hnat : (2696026519 : ℕ)^2093*10000000000000^1581 ≤ 4414524189299^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696026519 5000000000 4414524189299 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312588223/10000000000 : ℝ), (-1043751643/5000000000 : ℝ), (2696026519/5000000000 : ℝ)] ![(135268839891/312500000000 : ℝ), (2513745867239/20000000000000 : ℝ), (4414524189299/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312588223/10000000000 : ℝ)|^2093 ≤ (135268839891/312500000000 : ℝ)^1581
        have hw : |(5312588223/10000000000 : ℝ)|=(5312588223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043751643/5000000000 : ℝ)|^2093 ≤ (2513745867239/20000000000000 : ℝ)^1581
        have hw : |(-1043751643/5000000000 : ℝ)|=(1043751643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696026519/5000000000 : ℝ)|^2093 ≤ (4414524189299/10000000000000 : ℝ)^1581
        have hw : |(2696026519/5000000000 : ℝ)|=(2696026519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656294109/5000000000 : ℝ)*x 0 + (5392053041/10000000000 : ℝ)*x 1 + (-2087503287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656294109/5000000000 : ℝ)^2093 ≤ (10821507177797/25000000000000 : ℝ)^1581 := by
    have hnat : (2656294109 : ℕ)^2093*25000000000000^1581 ≤ 10821507177797^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656294109 5000000000 10821507177797 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392053041/10000000000 : ℝ)^2093 ≤ (8829048385101/20000000000000 : ℝ)^1581 := by
    have hnat : (5392053041 : ℕ)^2093*20000000000000^1581 ≤ 8829048385101^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392053041 10000000000 8829048385101 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087503287/10000000000 : ℝ)^2093 ≤ (6284364672083/50000000000000 : ℝ)^1581 := by
    have hnat : (2087503287 : ℕ)^2093*50000000000000^1581 ≤ 6284364672083^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087503287 10000000000 6284364672083 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656294109/5000000000 : ℝ), (5392053041/10000000000 : ℝ), (-2087503287/10000000000 : ℝ)] ![(10821507177797/25000000000000 : ℝ), (8829048385101/20000000000000 : ℝ), (6284364672083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656294109/5000000000 : ℝ)|^2093 ≤ (10821507177797/25000000000000 : ℝ)^1581
        have hw : |(2656294109/5000000000 : ℝ)|=(2656294109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392053041/10000000000 : ℝ)|^2093 ≤ (8829048385101/20000000000000 : ℝ)^1581
        have hw : |(5392053041/10000000000 : ℝ)|=(5392053041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087503287/10000000000 : ℝ)|^2093 ≤ (6284364672083/50000000000000 : ℝ)^1581
        have hw : |(-2087503287/10000000000 : ℝ)|=(2087503287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s7_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2179747853/5000000000 : ℝ)*x 0 + (4486965947/10000000000 : ℝ)*x 1 + (211780947/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179747853/5000000000 : ℝ)^2093 ≤ (33317257652701/100000000000000 : ℝ)^1581 := by
    have hnat : (2179747853 : ℕ)^2093*100000000000000^1581 ≤ 33317257652701^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179747853 5000000000 33317257652701 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4486965947/10000000000 : ℝ)^2093 ≤ (34612995606339/100000000000000 : ℝ)^1581 := by
    have hnat : (4486965947 : ℕ)^2093*100000000000000^1581 ≤ 34612995606339^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486965947 10000000000 34612995606339 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211780947/500000000 : ℝ)^2093 ≤ (16034873368317/50000000000000 : ℝ)^1581 := by
    have hnat : (211780947 : ℕ)^2093*50000000000000^1581 ≤ 16034873368317^1581*500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211780947 500000000 16034873368317 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179747853/5000000000 : ℝ), (4486965947/10000000000 : ℝ), (211780947/500000000 : ℝ)] ![(33317257652701/100000000000000 : ℝ), (34612995606339/100000000000000 : ℝ), (16034873368317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179747853/5000000000 : ℝ)|^2093 ≤ (33317257652701/100000000000000 : ℝ)^1581
        have hw : |(2179747853/5000000000 : ℝ)|=(2179747853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4486965947/10000000000 : ℝ)|^2093 ≤ (34612995606339/100000000000000 : ℝ)^1581
        have hw : |(4486965947/10000000000 : ℝ)|=(4486965947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211780947/500000000 : ℝ)|^2093 ≤ (16034873368317/50000000000000 : ℝ)^1581
        have hw : |(211780947/500000000 : ℝ)|=(211780947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14071/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2279/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2279/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2279/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2279/20000 : ℝ) ^ (8371/2048 : ℝ) ≤ (6972394377039463/50000000000000000000 : ℝ) := by
    have hpowers : (2279/20000 : ℝ)^8371 ≤ (6972394377039463/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2279 : ℕ)^8371*50000000000000000000^2048 ≤ 6972394377039463^2048*20000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2279 20000 6972394377039463 50000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2279/20000 : ℝ)) (X := (6972394377039463/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (8371/2048 : ℝ) ≤ (33074411395637461/100000000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^8371 ≤ (33074411395637461/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3519 : ℕ)^8371*100000000000000000000^2048 ≤ 33074411395637461^2048*25000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 33074411395637461 100000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (33074411395637461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006972394377039463/25000000000000000000 : ℝ) ≤ (10000682258265629/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (25006972394377039463/25000000000000000000 : ℝ)^2048 ≤ (10000682258265629/10000000000000000 : ℝ)^8371 := by
      have hnat : (25006972394377039463 : ℕ)^2048*10000000000000000^8371 ≤ 10000682258265629^8371*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006972394377039463 25000000000000000000 10000682258265629 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682258265629/10000000000000000 : ℝ)) (X := (25006972394377039463/25000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047019200149716387/100000000000000000000 : ℝ) ≤ (10001150140086051/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (100047019200149716387/100000000000000000000 : ℝ)^2048 ≤ (10001150140086051/10000000000000000 : ℝ)^8371 := by
      have hnat : (100047019200149716387 : ℕ)^2048*10000000000000000^8371 ≤ 10001150140086051^8371*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047019200149716387 100000000000000000000 10001150140086051 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001150140086051/10000000000000000 : ℝ)) (X := (100047019200149716387/100000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033074411395637461/50000000000000000000 : ℝ) ≤ (10001618021906473/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (50033074411395637461/50000000000000000000 : ℝ)^2048 ≤ (10001618021906473/10000000000000000 : ℝ)^8371 := by
      have hnat : (50033074411395637461 : ℕ)^2048*10000000000000000^8371 ≤ 10001618021906473^8371*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033074411395637461 50000000000000000000 10001618021906473 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001618021906473/10000000000000000 : ℝ)) (X := (50033074411395637461/50000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6972394377039463/50000000000000000000 : ℝ) ≤ ((26801166107722733969/26810000000000000000 : ℝ)+2*(233940910211/134050000000000 : ℝ)*(2279/20000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (26801166107722733969/26810000000000000000 : ℝ)+2*(233940910211/134050000000000 : ℝ)*(2279/20000 : ℝ)=(10000682258265629/10000000000000000 : ℝ) by norm_num, show 1+2*(6972394377039463/50000000000000000000 : ℝ)=(25006972394377039463/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33074411395637461/100000000000000000000 : ℝ)+(6972394377039463/50000000000000000000 : ℝ) ≤ ((26801166107722733969/26810000000000000000 : ℝ)+(233940910211/134050000000000 : ℝ)*((3519/25000 : ℝ)+(2279/20000 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (26801166107722733969/26810000000000000000 : ℝ)+(233940910211/134050000000000 : ℝ)*((3519/25000 : ℝ)+(2279/20000 : ℝ))=(10001150140086051/10000000000000000 : ℝ) by norm_num, show 1+(33074411395637461/100000000000000000000 : ℝ)+(6972394377039463/50000000000000000000 : ℝ)=(100047019200149716387/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33074411395637461/100000000000000000000 : ℝ) ≤ ((26801166107722733969/26810000000000000000 : ℝ)+2*(233940910211/134050000000000 : ℝ)*(3519/25000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (26801166107722733969/26810000000000000000 : ℝ)+2*(233940910211/134050000000000 : ℝ)*(3519/25000 : ℝ)=(10001618021906473/10000000000000000 : ℝ) by norm_num, show 1+2*(33074411395637461/100000000000000000000 : ℝ)=(50033074411395637461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26801166107722733969/26810000000000000000 : ℝ)*(X 1 0+X 2 0)+(233940910211/134050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (26801166107722733969/26810000000000000000 : ℝ)) (alpha := (233940910211/134050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26801166107722733969/26810000000000000000 : ℝ)*(X 0 1+X 2 1)+(233940910211/134050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (26801166107722733969/26810000000000000000 : ℝ)) (alpha := (233940910211/134050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26801166107722733969/26810000000000000000 : ℝ)*(X 0 2+X 1 2)+(233940910211/134050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (2279/20000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (26801166107722733969/26810000000000000000 : ℝ)) (alpha := (233940910211/134050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268664511/1250000000 : ℝ)*X 0 0+(2696185573/5000000000 : ℝ)*X 0 1+(2633154119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344612519/10000000000 : ℝ)*X 1 0+(-34582009/156250000 : ℝ)*X 1 1+(5266308509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534461267/1000000000 : ℝ)*X 2 0+(2633154333/5000000000 : ℝ)*X 2 1+(-2213248167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((21797433/50000000 : ℝ)*X 0 0+(4234980903/10000000000 : ℝ)*X 0 1+(2243800587/5000000000 : ℝ)*X 0 2+(21797433/50000000 : ℝ)*X 1 0+(4234980903/10000000000 : ℝ)*X 1 1+(2243800587/5000000000 : ℝ)*X 1 2+(21797433/50000000 : ℝ)*X 2 0+(4234980903/10000000000 : ℝ)*X 2 1+(2243800587/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074660213/5000000000 : ℝ)*X 0 0+(2633312771/5000000000 : ℝ)*X 0 1+(5392053037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312588223/10000000000 : ℝ)*X 1 0+(-1043751643/5000000000 : ℝ)*X 1 1+(2696026519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656294109/5000000000 : ℝ)*X 2 0+(5392053041/10000000000 : ℝ)*X 2 1+(-2087503287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179747853/5000000000 : ℝ)*X 0 0+(4486965947/10000000000 : ℝ)*X 0 1+(211780947/500000000 : ℝ)*X 0 2+(2179747853/5000000000 : ℝ)*X 1 0+(4486965947/10000000000 : ℝ)*X 1 1+(211780947/500000000 : ℝ)*X 1 2+(2179747853/5000000000 : ℝ)*X 2 0+(4486965947/10000000000 : ℝ)*X 2 1+(211780947/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142128730851371545729149/13405000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1327496739/100000000000000 : ℝ)*(base19) + (347881289/25000000000000 : ℝ)*(base23) + (405897/195312500000 : ℝ)*(upper3) + (4278087/5000000000000 : ℝ)*(upper4) + (796141153/100000000000000 : ℝ)*(upper5) + (743197333254589/12500000000000 : ℝ)*(major0) + (743197333254589/12500000000000 : ℝ)*(major1) + (743197333254589/12500000000000 : ℝ)*(major2) + (793256335765597/10000000000000 : ℝ)*(sp0) + (3966306286525277/50000000000000 : ℝ)*(sp1) + (7932612509022137/100000000000000 : ℝ)*(sp2) + (3958531712115561/100000000000000 : ℝ)*(sp3) + (50542891323/100000000000000 : ℝ)*(sp4) + (5682994187/50000000000000 : ℝ)*(sp7) + (30926117797687/781250000000 : ℝ)*(f.failure) + (1983153475136823/25000000000000 : ℝ)*(f.sum) + (54287286580817/6702500000000000000000000000 : ℝ)*base65 + (255874733710663037/47875000000000000000000000000000 : ℝ)*base68 + (965875851157586963/47875000000000000000000000000000 : ℝ)*base69 + (36165412675711963/47875000000000000000000000000000 : ℝ)*base71 + (37984848925379/13405000000000000000000000000 : ℝ)*base73 + (685494964095538037/47875000000000000000000000000000 : ℝ)*base76 + (432645271213288037/47875000000000000000000000000000 : ℝ)*base78 + (979093180295836963/47875000000000000000000000000000 : ℝ)*base79 + (84362413782989/13405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (146029/39062500000000000000 : ℝ)*base89 + (146029/39062500000000000000 : ℝ)*base91 + (146029/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6232339460404379422530429423/670250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1689895439/100000000000000 : ℝ)*(base19) + (916289739/50000000000000 : ℝ)*(base23) + (186928919/100000000000000 : ℝ)*(upper3) + (68597859/100000000000000 : ℝ)*(lower4) + (188603593/100000000000000 : ℝ)*(upper5) + (2987823702910937/50000000000000 : ℝ)*(major0) + (2987823702910937/50000000000000 : ℝ)*(major1) + (2987823702910937/50000000000000 : ℝ)*(major2) + (23562186503/50000000000000 : ℝ)*(sp1) + (12654638727/25000000000000 : ℝ)*(sp2) + (3986365886979221/50000000000000 : ℝ)*(sp4) + (3986341479844999/50000000000000 : ℝ)*(sp5) + (1594535864564811/20000000000000 : ℝ)*(sp6) + (1989281363867153/50000000000000 : ℝ)*(sp7) + (1989281363867153/50000000000000 : ℝ)*(f.failure) + (3986365886979221/50000000000000 : ℝ)*(f.sum) + (12283280856873/3351250000000000000000000000 : ℝ)*base66 + (1830843106797131279/191500000000000000000000000000000 : ℝ)*base67 + (3914757472705131279/191500000000000000000000000000000 : ℝ)*base69 + (1652778295240131279/191500000000000000000000000000000 : ℝ)*base71 + (3432581573431/6702500000000000000000000000 : ℝ)*base74 + (1359394183709131279/191500000000000000000000000000000 : ℝ)*base75 + (2329058116637131279/191500000000000000000000000000000 : ℝ)*base77 + (4170167194558631279/191500000000000000000000000000000 : ℝ)*base79 + (22232690710133/13405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (14906749/2500000000000000000000 : ℝ)*base90 + (14906749/2500000000000000000000 : ℝ)*base92 + (14906749/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1179_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1179_s8_0 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074659569/5000000000 : ℝ)*x 0 + (1078464537/2000000000 : ℝ)*x 1 + (5266354789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074659569/5000000000 : ℝ)^2093 ≤ (13063797716027/100000000000000 : ℝ)^1581 := by
    have hnat : (1074659569 : ℕ)^2093*100000000000000^1581 ≤ 13063797716027^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074659569 5000000000 13063797716027 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078464537/2000000000 : ℝ)^2093 ≤ (68981506987/156250000000 : ℝ)^1581 := by
    have hnat : (1078464537 : ℕ)^2093*156250000000^1581 ≤ 68981506987^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078464537 2000000000 68981506987 156250000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266354789/10000000000 : ℝ)^2093 ≤ (21394018894289/50000000000000 : ℝ)^1581 := by
    have hnat : (5266354789 : ℕ)^2093*50000000000000^1581 ≤ 21394018894289^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266354789 10000000000 21394018894289 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074659569/5000000000 : ℝ), (1078464537/2000000000 : ℝ), (5266354789/10000000000 : ℝ)] ![(13063797716027/100000000000000 : ℝ), (68981506987/156250000000 : ℝ), (21394018894289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074659569/5000000000 : ℝ)|^2093 ≤ (13063797716027/100000000000000 : ℝ)^1581
        have hw : |(-1074659569/5000000000 : ℝ)|=(1074659569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078464537/2000000000 : ℝ)|^2093 ≤ (68981506987/156250000000 : ℝ)^1581
        have hw : |(1078464537/2000000000 : ℝ)|=(1078464537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266354789/10000000000 : ℝ)|^2093 ≤ (21394018894289/50000000000000 : ℝ)^1581
        have hw : |(5266354789/10000000000 : ℝ)|=(5266354789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_1 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672300517/5000000000 : ℝ)*x 0 + (-553300649/2500000000 : ℝ)*x 1 + (2633177387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672300517/5000000000 : ℝ)^2093 ≤ (2181583507151/5000000000000 : ℝ)^1581 := by
    have hnat : (2672300517 : ℕ)^2093*5000000000000^1581 ≤ 2181583507151^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672300517 5000000000 2181583507151 5000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553300649/2500000000 : ℝ)^2093 ≤ (679014610723/5000000000000 : ℝ)^1581 := by
    have hnat : (553300649 : ℕ)^2093*5000000000000^1581 ≤ 679014610723^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553300649 2500000000 679014610723 5000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633177387/5000000000 : ℝ)^2093 ≤ (21394018813619/50000000000000 : ℝ)^1581 := by
    have hnat : (2633177387 : ℕ)^2093*50000000000000^1581 ≤ 21394018813619^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633177387 5000000000 21394018813619 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672300517/5000000000 : ℝ), (-553300649/2500000000 : ℝ), (2633177387/5000000000 : ℝ)] ![(2181583507151/5000000000000 : ℝ), (679014610723/5000000000000 : ℝ), (21394018813619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672300517/5000000000 : ℝ)|^2093 ≤ (2181583507151/5000000000000 : ℝ)^1581
        have hw : |(2672300517/5000000000 : ℝ)|=(2672300517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553300649/2500000000 : ℝ)|^2093 ≤ (679014610723/5000000000000 : ℝ)^1581
        have hw : |(-553300649/2500000000 : ℝ)|=(553300649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633177387/5000000000 : ℝ)|^2093 ≤ (21394018813619/50000000000000 : ℝ)^1581
        have hw : |(2633177387/5000000000 : ℝ)|=(2633177387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_2 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1068920211/2000000000 : ℝ)*x 0 + (2633177393/5000000000 : ℝ)*x 1 + (-2213202551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068920211/2000000000 : ℝ)^2093 ≤ (5453958796247/12500000000000 : ℝ)^1581 := by
    have hnat : (1068920211 : ℕ)^2093*12500000000000^1581 ≤ 5453958796247^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068920211 2000000000 5453958796247 12500000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633177393/5000000000 : ℝ)^2093 ≤ (4278803775631/10000000000000 : ℝ)^1581 := by
    have hnat : (2633177393 : ℕ)^2093*10000000000000^1581 ≤ 4278803775631^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633177393 5000000000 4278803775631 10000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2213202551/10000000000 : ℝ)^2093 ≤ (6790145924459/50000000000000 : ℝ)^1581 := by
    have hnat : (2213202551 : ℕ)^2093*50000000000000^1581 ≤ 6790145924459^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213202551 10000000000 6790145924459 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068920211/2000000000 : ℝ), (2633177393/5000000000 : ℝ), (-2213202551/10000000000 : ℝ)] ![(5453958796247/12500000000000 : ℝ), (4278803775631/10000000000000 : ℝ), (6790145924459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068920211/2000000000 : ℝ)|^2093 ≤ (5453958796247/12500000000000 : ℝ)^1581
        have hw : |(1068920211/2000000000 : ℝ)|=(1068920211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633177393/5000000000 : ℝ)|^2093 ≤ (4278803775631/10000000000000 : ℝ)^1581
        have hw : |(2633177393/5000000000 : ℝ)|=(2633177393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2213202551/10000000000 : ℝ)|^2093 ≤ (6790145924459/50000000000000 : ℝ)^1581
        have hw : |(-2213202551/10000000000 : ℝ)|=(2213202551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_3 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4359488461/10000000000 : ℝ)*x 0 + (4235075943/10000000000 : ℝ)*x 1 + (4487506057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359488461/10000000000 : ℝ)^2093 ≤ (8329296087979/25000000000000 : ℝ)^1581 := by
    have hnat : (4359488461 : ℕ)^2093*25000000000000^1581 ≤ 8329296087979^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359488461 10000000000 8329296087979 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235075943/10000000000 : ℝ)^2093 ≤ (8016076040411/25000000000000 : ℝ)^1581 := by
    have hnat : (4235075943 : ℕ)^2093*25000000000000^1581 ≤ 8016076040411^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235075943 10000000000 8016076040411 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487506057/10000000000 : ℝ)^2093 ≤ (34618511481837/100000000000000 : ℝ)^1581 := by
    have hnat : (4487506057 : ℕ)^2093*100000000000000^1581 ≤ 34618511481837^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487506057 10000000000 34618511481837 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359488461/10000000000 : ℝ), (4235075943/10000000000 : ℝ), (4487506057/10000000000 : ℝ)] ![(8329296087979/25000000000000 : ℝ), (8016076040411/25000000000000 : ℝ), (34618511481837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359488461/10000000000 : ℝ)|^2093 ≤ (8329296087979/25000000000000 : ℝ)^1581
        have hw : |(4359488461/10000000000 : ℝ)|=(4359488461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235075943/10000000000 : ℝ)|^2093 ≤ (8016076040411/25000000000000 : ℝ)^1581
        have hw : |(4235075943/10000000000 : ℝ)|=(4235075943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487506057/10000000000 : ℝ)|^2093 ≤ (34618511481837/100000000000000 : ℝ)^1581
        have hw : |(4487506057/10000000000 : ℝ)|=(4487506057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_4 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149323713/10000000000 : ℝ)*x 0 + (2633335681/5000000000 : ℝ)*x 1 + (43136041/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149323713/10000000000 : ℝ)^2093 ≤ (6531917264341/50000000000000 : ℝ)^1581 := by
    have hnat : (2149323713 : ℕ)^2093*50000000000000^1581 ≤ 6531917264341^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149323713 10000000000 6531917264341 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633335681/5000000000 : ℝ)^2093 ≤ (42791442871671/100000000000000 : ℝ)^1581 := by
    have hnat : (2633335681 : ℕ)^2093*100000000000000^1581 ≤ 42791442871671^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633335681 5000000000 42791442871671 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43136041/80000000 : ℝ)^2093 ≤ (44144722591171/100000000000000 : ℝ)^1581 := by
    have hnat : (43136041 : ℕ)^2093*100000000000000^1581 ≤ 44144722591171^1581*80000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43136041 80000000 44144722591171 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149323713/10000000000 : ℝ), (2633335681/5000000000 : ℝ), (43136041/80000000 : ℝ)] ![(6531917264341/50000000000000 : ℝ), (42791442871671/100000000000000 : ℝ), (44144722591171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149323713/10000000000 : ℝ)|^2093 ≤ (6531917264341/50000000000000 : ℝ)^1581
        have hw : |(-2149323713/10000000000 : ℝ)|=(2149323713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633335681/5000000000 : ℝ)|^2093 ≤ (42791442871671/100000000000000 : ℝ)^1581
        have hw : |(2633335681/5000000000 : ℝ)|=(2633335681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43136041/80000000 : ℝ)|^2093 ≤ (44144722591171/100000000000000 : ℝ)^1581
        have hw : |(43136041/80000000 : ℝ)|=(43136041/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_5 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312600271/10000000000 : ℝ)*x 0 + (-417510527/2000000000 : ℝ)*x 1 + (2696002377/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312600271/10000000000 : ℝ)^2093 ≤ (43286158720441/100000000000000 : ℝ)^1581 := by
    have hnat : (5312600271 : ℕ)^2093*100000000000000^1581 ≤ 43286158720441^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312600271 10000000000 43286158720441 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417510527/2000000000 : ℝ)^2093 ≤ (2513824537679/20000000000000 : ℝ)^1581 := by
    have hnat : (417510527 : ℕ)^2093*20000000000000^1581 ≤ 2513824537679^1581*2000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417510527 2000000000 2513824537679 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696002377/5000000000 : ℝ)^2093 ≤ (22072359285059/50000000000000 : ℝ)^1581 := by
    have hnat : (2696002377 : ℕ)^2093*50000000000000^1581 ≤ 22072359285059^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696002377 5000000000 22072359285059 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312600271/10000000000 : ℝ), (-417510527/2000000000 : ℝ), (2696002377/5000000000 : ℝ)] ![(43286158720441/100000000000000 : ℝ), (2513824537679/20000000000000 : ℝ), (22072359285059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312600271/10000000000 : ℝ)|^2093 ≤ (43286158720441/100000000000000 : ℝ)^1581
        have hw : |(5312600271/10000000000 : ℝ)|=(5312600271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417510527/2000000000 : ℝ)|^2093 ≤ (2513824537679/20000000000000 : ℝ)^1581
        have hw : |(-417510527/2000000000 : ℝ)|=(417510527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696002377/5000000000 : ℝ)|^2093 ≤ (22072359285059/50000000000000 : ℝ)^1581
        have hw : |(2696002377/5000000000 : ℝ)|=(2696002377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_6 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212504003/400000000 : ℝ)*x 0 + (2696002519/5000000000 : ℝ)*x 1 + (-1043776257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212504003/400000000 : ℝ)^2093 ≤ (43286156606293/100000000000000 : ℝ)^1581 := by
    have hnat : (212504003 : ℕ)^2093*100000000000000^1581 ≤ 43286156606293^1581*400000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212504003 400000000 43286156606293 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696002519/5000000000 : ℝ)^2093 ≤ (44144721648229/100000000000000 : ℝ)^1581 := by
    have hnat : (2696002519 : ℕ)^2093*100000000000000^1581 ≤ 44144721648229^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696002519 5000000000 44144721648229 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043776257/5000000000 : ℝ)^2093 ≤ (6284560861961/50000000000000 : ℝ)^1581 := by
    have hnat : (1043776257 : ℕ)^2093*50000000000000^1581 ≤ 6284560861961^1581*5000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043776257 5000000000 6284560861961 50000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212504003/400000000 : ℝ), (2696002519/5000000000 : ℝ), (-1043776257/5000000000 : ℝ)] ![(43286156606293/100000000000000 : ℝ), (44144721648229/100000000000000 : ℝ), (6284560861961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212504003/400000000 : ℝ)|^2093 ≤ (43286156606293/100000000000000 : ℝ)^1581
        have hw : |(212504003/400000000 : ℝ)|=(212504003/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696002519/5000000000 : ℝ)|^2093 ≤ (44144721648229/100000000000000 : ℝ)^1581
        have hw : |(2696002519/5000000000 : ℝ)|=(2696002519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043776257/5000000000 : ℝ)|^2093 ≤ (6284560861961/50000000000000 : ℝ)^1581
        have hw : |(-1043776257/5000000000 : ℝ)|=(1043776257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1179_s8_7 (p : ℝ) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1089874547/2500000000 : ℝ)*x 0 + (112171779/250000000 : ℝ)*x 1 + (4235713007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089874547/2500000000 : ℝ)^2093 ≤ (8329320691043/25000000000000 : ℝ)^1581 := by
    have hnat : (1089874547 : ℕ)^2093*25000000000000^1581 ≤ 8329320691043^1581*2500000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089874547 2500000000 8329320691043 25000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112171779/250000000 : ℝ)^2093 ≤ (34612027615907/100000000000000 : ℝ)^1581 := by
    have hnat : (112171779 : ℕ)^2093*100000000000000^1581 ≤ 34612027615907^1581*250000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112171779 250000000 34612027615907 100000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235713007/10000000000 : ℝ)^2093 ≤ (6414137922649/20000000000000 : ℝ)^1581 := by
    have hnat : (4235713007 : ℕ)^2093*20000000000000^1581 ≤ 6414137922649^1581*10000000000^2093 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235713007 10000000000 6414137922649 20000000000000 2093 1581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2093/512 : ℝ)) 2093 1581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089874547/2500000000 : ℝ), (112171779/250000000 : ℝ), (4235713007/10000000000 : ℝ)] ![(8329320691043/25000000000000 : ℝ), (34612027615907/100000000000000 : ℝ), (6414137922649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089874547/2500000000 : ℝ)|^2093 ≤ (8329320691043/25000000000000 : ℝ)^1581
        have hw : |(1089874547/2500000000 : ℝ)|=(1089874547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112171779/250000000 : ℝ)|^2093 ≤ (34612027615907/100000000000000 : ℝ)^1581
        have hw : |(112171779/250000000 : ℝ)|=(112171779/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235713007/10000000000 : ℝ)|^2093 ≤ (6414137922649/20000000000000 : ℝ)^1581
        have hw : |(4235713007/10000000000 : ℝ)|=(4235713007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1179_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    (11401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14071/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14071/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/500 : ℝ) ^ (8371/2048 : ℝ) ≤ (2793963155125423/20000000000000000000 : ℝ) := by
    have hpowers : (57/500 : ℝ)^8371 ≤ (2793963155125423/20000000000000000000 : ℝ)^2048 := by
      have hnat : (57 : ℕ)^8371*20000000000000000000^2048 ≤ 2793963155125423^2048*500^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 500 2793963155125423 20000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/500 : ℝ)) (X := (2793963155125423/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14071/100000 : ℝ) ^ (8371/2048 : ℝ) ≤ (8256604206267351/25000000000000000000 : ℝ) := by
    have hpowers : (14071/100000 : ℝ)^8371 ≤ (8256604206267351/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14071 : ℕ)^8371*25000000000000000000^2048 ≤ 8256604206267351^2048*100000^8371 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14071 100000 8256604206267351 25000000000000000000 8371 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14071/100000 : ℝ)) (X := (8256604206267351/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002793963155125423/10000000000000000000 : ℝ) ≤ (10000683482600487/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (10002793963155125423/10000000000000000000 : ℝ)^2048 ≤ (10000683482600487/10000000000000000 : ℝ)^8371 := by
      have hnat : (10002793963155125423 : ℕ)^2048*10000000000000000^8371 ≤ 10000683482600487^8371*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002793963155125423 10000000000000000000 10000683482600487 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000683482600487/10000000000000000 : ℝ)) (X := (10002793963155125423/10000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046996232600696519/100000000000000000000 : ℝ) ≤ (5000574789187419/5000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (100046996232600696519/100000000000000000000 : ℝ)^2048 ≤ (5000574789187419/5000000000000000 : ℝ)^8371 := by
      have hnat : (100046996232600696519 : ℕ)^2048*5000000000000000^8371 ≤ 5000574789187419^8371*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046996232600696519 100000000000000000000 5000574789187419 5000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000574789187419/5000000000000000 : ℝ)) (X := (100046996232600696519/100000000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508256604206267351/12500000000000000000 : ℝ) ≤ (10001615674149189/10000000000000000 : ℝ) ^ (8371/2048 : ℝ) := by
    have hpowers : (12508256604206267351/12500000000000000000 : ℝ)^2048 ≤ (10001615674149189/10000000000000000 : ℝ)^8371 := by
      have hnat : (12508256604206267351 : ℕ)^2048*10000000000000000^8371 ≤ 10001615674149189^8371*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508256604206267351 12500000000000000000 10001615674149189 10000000000000000 2048 8371 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001615674149189/10000000000000000 : ℝ)) (X := (12508256604206267351/12500000000000000000 : ℝ)) (by norm_num) 8371 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2793963155125423/20000000000000000000 : ℝ) ≤ ((26701198598370697977/26710000000000000000 : ℝ)+2*(466095774351/267100000000000 : ℝ)*(57/500 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (26701198598370697977/26710000000000000000 : ℝ)+2*(466095774351/267100000000000 : ℝ)*(57/500 : ℝ)=(10000683482600487/10000000000000000 : ℝ) by norm_num, show 1+2*(2793963155125423/20000000000000000000 : ℝ)=(10002793963155125423/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8256604206267351/25000000000000000000 : ℝ)+(2793963155125423/20000000000000000000 : ℝ) ≤ ((26701198598370697977/26710000000000000000 : ℝ)+(466095774351/267100000000000 : ℝ)*((14071/100000 : ℝ)+(57/500 : ℝ)))^(8371/2048 : ℝ) := by
    rw [show (26701198598370697977/26710000000000000000 : ℝ)+(466095774351/267100000000000 : ℝ)*((14071/100000 : ℝ)+(57/500 : ℝ))=(5000574789187419/5000000000000000 : ℝ) by norm_num, show 1+(8256604206267351/25000000000000000000 : ℝ)+(2793963155125423/20000000000000000000 : ℝ)=(100046996232600696519/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8256604206267351/25000000000000000000 : ℝ) ≤ ((26701198598370697977/26710000000000000000 : ℝ)+2*(466095774351/267100000000000 : ℝ)*(14071/100000 : ℝ))^(8371/2048 : ℝ) := by
    rw [show (26701198598370697977/26710000000000000000 : ℝ)+2*(466095774351/267100000000000 : ℝ)*(14071/100000 : ℝ)=(10001615674149189/10000000000000000 : ℝ) by norm_num, show 1+2*(8256604206267351/25000000000000000000 : ℝ)=(12508256604206267351/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26701198598370697977/26710000000000000000 : ℝ)*(X 1 0+X 2 0)+(466095774351/267100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (26701198598370697977/26710000000000000000 : ℝ)) (alpha := (466095774351/267100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26701198598370697977/26710000000000000000 : ℝ)*(X 0 1+X 2 1)+(466095774351/267100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (26701198598370697977/26710000000000000000 : ℝ)) (alpha := (466095774351/267100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26701198598370697977/26710000000000000000 : ℝ)*(X 0 2+X 1 2)+(466095774351/267100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8371/2048 : ℝ)) (lo := (57/500 : ℝ)) (hi := (14071/100000 : ℝ)) (c := (26701198598370697977/26710000000000000000 : ℝ)) (alpha := (466095774351/267100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1074659569/5000000000 : ℝ)*X 0 0+(1078464537/2000000000 : ℝ)*X 0 1+(5266354789/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672300517/5000000000 : ℝ)*X 1 0+(-553300649/2500000000 : ℝ)*X 1 1+(2633177387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068920211/2000000000 : ℝ)*X 2 0+(2633177393/5000000000 : ℝ)*X 2 1+(-2213202551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359488461/10000000000 : ℝ)*X 0 0+(4235075943/10000000000 : ℝ)*X 0 1+(4487506057/10000000000 : ℝ)*X 0 2+(4359488461/10000000000 : ℝ)*X 1 0+(4235075943/10000000000 : ℝ)*X 1 1+(4487506057/10000000000 : ℝ)*X 1 2+(4359488461/10000000000 : ℝ)*X 2 0+(4235075943/10000000000 : ℝ)*X 2 1+(4487506057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2149323713/10000000000 : ℝ)*X 0 0+(2633335681/5000000000 : ℝ)*X 0 1+(43136041/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312600271/10000000000 : ℝ)*X 1 0+(-417510527/2000000000 : ℝ)*X 1 1+(2696002377/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212504003/400000000 : ℝ)*X 2 0+(2696002519/5000000000 : ℝ)*X 2 1+(-1043776257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089874547/2500000000 : ℝ)*X 0 0+(112171779/250000000 : ℝ)*X 0 1+(4235713007/10000000000 : ℝ)*X 0 2+(1089874547/2500000000 : ℝ)*X 1 0+(112171779/250000000 : ℝ)*X 1 1+(4235713007/10000000000 : ℝ)*X 1 2+(1089874547/2500000000 : ℝ)*X 2 0+(112171779/250000000 : ℝ)*X 2 1+(4235713007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1179_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (766181792814701094875484351/83468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1733207323/100000000000000 : ℝ)*(base19) + (337550161/20000000000000 : ℝ)*(base23) + (10241453/25000000000000 : ℝ)*(lower2) + (173766003/100000000000000 : ℝ)*(upper3) + (195111913/100000000000000 : ℝ)*(upper5) + (371880426954679/6250000000000 : ℝ)*(major0) + (371880426954679/6250000000000 : ℝ)*(major1) + (371880426954679/6250000000000 : ℝ)*(major2) + (7938578241282693/100000000000000 : ℝ)*(sp0) + (7938627026436809/100000000000000 : ℝ)*(sp1) + (496164191993333/6250000000000 : ℝ)*(sp2) + (3961518390215897/100000000000000 : ℝ)*(sp3) + (50518361439/100000000000000 : ℝ)*(sp4) + (26206714183/100000000000000 : ℝ)*(sp7) + (3961544596930081/100000000000000 : ℝ)*(f.failure) + (1984657189911033/25000000000000 : ℝ)*(f.sum) + (696225937777/417343750000000000000000000 : ℝ)*base65 + (61963714350740617/166937500000000000000000000000000 : ℝ)*base68 + (1960036824508759383/166937500000000000000000000000000 : ℝ)*base69 + (3040353263139071883/166937500000000000000000000000000 : ℝ)*base71 + (53920242673121/13355000000000000000000000000 : ℝ)*base74 + (1347451543422115617/166937500000000000000000000000000 : ℝ)*base76 + (1878601723994446883/166937500000000000000000000000000 : ℝ)*base77 + (90605944953321883/166937500000000000000000000000000 : ℝ)*base79 + (9214095462423/6677500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (17253427/5000000000000000000000 : ℝ)*base89 + (17253427/5000000000000000000000 : ℝ)*base91 + (17253427/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14768452083241997566868793069/1335500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (621300883/50000000000000 : ℝ)*(base19) + (378918433/25000000000000 : ℝ)*(base23) + (152853537/50000000000000 : ℝ)*(lower1) + (276891221/100000000000000 : ℝ)*(lower4) + (327614553/100000000000000 : ℝ)*(upper5) + (5980107225092333/100000000000000 : ℝ)*(major0) + (5980107225092333/100000000000000 : ℝ)*(major1) + (5980107225092333/100000000000000 : ℝ)*(major2) + (1159005073/50000000000000 : ℝ)*(sp0) + (7675745027/100000000000000 : ℝ)*(sp2) + (797867970555841/10000000000000 : ℝ)*(sp4) + (7978680780966791/100000000000000 : ℝ)*(sp5) + (3989336416074899/50000000000000 : ℝ)*(sp6) + (248845753625237/6250000000000 : ℝ)*(sp7) + (248845753625237/6250000000000 : ℝ)*(f.failure) + (7978682023568557/100000000000000 : ℝ)*(f.sum) + (3647008378493/13355000000000000000000000000 : ℝ)*base65 + (6415621145080389659/2671000000000000000000000000000000 : ℝ)*base68 + (32301104380378389659/2671000000000000000000000000000000 : ℝ)*base70 + (22423122084877389659/2671000000000000000000000000000000 : ℝ)*base72 + (39415718985729/6677500000000000000000000000 : ℝ)*base73 + (82365217164248389659/2671000000000000000000000000000000 : ℝ)*base76 + (3653038113431389659/2671000000000000000000000000000000 : ℝ)*base78 + (69832146119916389659/2671000000000000000000000000000000 : ℝ)*base80 + (1271354555079/6677500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (491879/312500000000000000000 : ℝ)*base89 + (491879/312500000000000000000 : ℝ)*base91 + (491879/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1179_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14071/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1179_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1179_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1179_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1179_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1179_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8371/2048 : ℝ) ≤ p) (hpb : p ≤ (2093/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75098067/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1421/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1179_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

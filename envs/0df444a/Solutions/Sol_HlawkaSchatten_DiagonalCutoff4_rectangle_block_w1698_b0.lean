-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1698_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:17.626705+00:00
-- url     : https://prove2.me/submissions/3e0448cc-ddc6-4fb3-837c-e9eac34438a0

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
theorem support_rectangle_w1698_s0_0 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1372680089/10000000000 : ℝ)*x 0 + (572251313/1000000000 : ℝ)*x 1 + (4947089237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372680089/10000000000 : ℝ)^5207 ≤ (422100611837/5000000000000 : ℝ)^4183 := by
    have hnat : (1372680089 : ℕ)^5207*5000000000000^4183 ≤ 422100611837^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372680089 10000000000 422100611837 5000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572251313/1000000000 : ℝ)^5207 ≤ (24958240053379/50000000000000 : ℝ)^4183 := by
    have hnat : (572251313 : ℕ)^5207*50000000000000^4183 ≤ 24958240053379^4183*1000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572251313 1000000000 24958240053379 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4947089237/10000000000 : ℝ)^5207 ≤ (20820753820931/50000000000000 : ℝ)^4183 := by
    have hnat : (4947089237 : ℕ)^5207*50000000000000^4183 ≤ 20820753820931^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4947089237 10000000000 20820753820931 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1372680089/10000000000 : ℝ), (572251313/1000000000 : ℝ), (4947089237/10000000000 : ℝ)] ![(422100611837/5000000000000 : ℝ), (24958240053379/50000000000000 : ℝ), (20820753820931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1372680089/10000000000 : ℝ)|^5207 ≤ (422100611837/5000000000000 : ℝ)^4183
        have hw : |(-1372680089/10000000000 : ℝ)|=(1372680089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572251313/1000000000 : ℝ)|^5207 ≤ (24958240053379/50000000000000 : ℝ)^4183
        have hw : |(572251313/1000000000 : ℝ)|=(572251313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4947089237/10000000000 : ℝ)|^5207 ≤ (20820753820931/50000000000000 : ℝ)^4183
        have hw : |(4947089237/10000000000 : ℝ)|=(4947089237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_1 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676598317/1250000000 : ℝ)*x 0 + (-1794263159/10000000000 : ℝ)*x 1 + (4947088721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676598317/1250000000 : ℝ)^5207 ≤ (46576004982683/100000000000000 : ℝ)^4183 := by
    have hnat : (676598317 : ℕ)^5207*100000000000000^4183 ≤ 46576004982683^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676598317 1250000000 46576004982683 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794263159/10000000000 : ℝ)^5207 ≤ (5891246381549/50000000000000 : ℝ)^4183 := by
    have hnat : (1794263159 : ℕ)^5207*50000000000000^4183 ≤ 5891246381549^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794263159 10000000000 5891246381549 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4947088721/10000000000 : ℝ)^5207 ≤ (41641502235239/100000000000000 : ℝ)^4183 := by
    have hnat : (4947088721 : ℕ)^5207*100000000000000^4183 ≤ 41641502235239^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4947088721 10000000000 41641502235239 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676598317/1250000000 : ℝ), (-1794263159/10000000000 : ℝ), (4947088721/10000000000 : ℝ)] ![(46576004982683/100000000000000 : ℝ), (5891246381549/50000000000000 : ℝ), (41641502235239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676598317/1250000000 : ℝ)|^5207 ≤ (46576004982683/100000000000000 : ℝ)^4183
        have hw : |(676598317/1250000000 : ℝ)|=(676598317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794263159/10000000000 : ℝ)|^5207 ≤ (5891246381549/50000000000000 : ℝ)^4183
        have hw : |(-1794263159/10000000000 : ℝ)|=(1794263159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4947088721/10000000000 : ℝ)|^5207 ≤ (41641502235239/100000000000000 : ℝ)^4183
        have hw : |(4947088721/10000000000 : ℝ)|=(4947088721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_2 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (676598251/1250000000 : ℝ)*x 0 + (4947089219/10000000000 : ℝ)*x 1 + (-1794263213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676598251/1250000000 : ℝ)^5207 ≤ (46575999327131/100000000000000 : ℝ)^4183 := by
    have hnat : (676598251 : ℕ)^5207*100000000000000^4183 ≤ 46575999327131^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676598251 1250000000 46575999327131 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4947089219/10000000000 : ℝ)^5207 ≤ (41641507453259/100000000000000 : ℝ)^4183 := by
    have hnat : (4947089219 : ℕ)^5207*100000000000000^4183 ≤ 41641507453259^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4947089219 10000000000 41641507453259 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794263213/10000000000 : ℝ)^5207 ≤ (11782493204511/100000000000000 : ℝ)^4183 := by
    have hnat : (1794263213 : ℕ)^5207*100000000000000^4183 ≤ 11782493204511^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794263213 10000000000 11782493204511 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(676598251/1250000000 : ℝ), (4947089219/10000000000 : ℝ), (-1794263213/10000000000 : ℝ)] ![(46575999327131/100000000000000 : ℝ), (41641507453259/100000000000000 : ℝ), (11782493204511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(676598251/1250000000 : ℝ)|^5207 ≤ (46575999327131/100000000000000 : ℝ)^4183
        have hw : |(676598251/1250000000 : ℝ)|=(676598251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4947089219/10000000000 : ℝ)|^5207 ≤ (41641507453259/100000000000000 : ℝ)^4183
        have hw : |(4947089219/10000000000 : ℝ)|=(4947089219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794263213/10000000000 : ℝ)|^5207 ≤ (11782493204511/100000000000000 : ℝ)^4183
        have hw : |(-1794263213/10000000000 : ℝ)|=(1794263213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_3 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4049737683/10000000000 : ℝ)*x 0 + (610381309/2000000000 : ℝ)*x 1 + (654824911/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4049737683/10000000000 : ℝ)^5207 ≤ (32458230983331/100000000000000 : ℝ)^4183 := by
    have hnat : (4049737683 : ℕ)^5207*100000000000000^4183 ≤ 32458230983331^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049737683 10000000000 32458230983331 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610381309/2000000000 : ℝ)^5207 ≤ (1141206075379/5000000000000 : ℝ)^4183 := by
    have hnat : (610381309 : ℕ)^5207*5000000000000^4183 ≤ 1141206075379^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610381309 2000000000 1141206075379 5000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654824911/1250000000 : ℝ)^5207 ≤ (44717647496223/100000000000000 : ℝ)^4183 := by
    have hnat : (654824911 : ℕ)^5207*100000000000000^4183 ≤ 44717647496223^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654824911 1250000000 44717647496223 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4049737683/10000000000 : ℝ), (610381309/2000000000 : ℝ), (654824911/1250000000 : ℝ)] ![(32458230983331/100000000000000 : ℝ), (1141206075379/5000000000000 : ℝ), (44717647496223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4049737683/10000000000 : ℝ)|^5207 ≤ (32458230983331/100000000000000 : ℝ)^4183
        have hw : |(4049737683/10000000000 : ℝ)|=(4049737683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(610381309/2000000000 : ℝ)|^5207 ≤ (1141206075379/5000000000000 : ℝ)^4183
        have hw : |(610381309/2000000000 : ℝ)|=(610381309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654824911/1250000000 : ℝ)|^5207 ≤ (44717647496223/100000000000000 : ℝ)^4183
        have hw : |(654824911/1250000000 : ℝ)|=(654824911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_4 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-687273227/5000000000 : ℝ)*x 0 + (2483195933/5000000000 : ℝ)*x 1 + (356409557/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687273227/5000000000 : ℝ)^5207 ≤ (8456302662989/100000000000000 : ℝ)^4183 := by
    have hnat : (687273227 : ℕ)^5207*100000000000000^4183 ≤ 8456302662989^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687273227 5000000000 8456302662989 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2483195933/5000000000 : ℝ)^5207 ≤ (41843856163601/100000000000000 : ℝ)^4183 := by
    have hnat : (2483195933 : ℕ)^5207*100000000000000^4183 ≤ 41843856163601^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483195933 5000000000 41843856163601 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356409557/625000000 : ℝ)^5207 ≤ (49699841162299/100000000000000 : ℝ)^4183 := by
    have hnat : (356409557 : ℕ)^5207*100000000000000^4183 ≤ 49699841162299^4183*625000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356409557 625000000 49699841162299 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-687273227/5000000000 : ℝ), (2483195933/5000000000 : ℝ), (356409557/625000000 : ℝ)] ![(8456302662989/100000000000000 : ℝ), (41843856163601/100000000000000 : ℝ), (49699841162299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-687273227/5000000000 : ℝ)|^5207 ≤ (8456302662989/100000000000000 : ℝ)^4183
        have hw : |(-687273227/5000000000 : ℝ)|=(687273227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2483195933/5000000000 : ℝ)|^5207 ≤ (41843856163601/100000000000000 : ℝ)^4183
        have hw : |(2483195933/5000000000 : ℝ)|=(2483195933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356409557/625000000 : ℝ)|^5207 ≤ (49699841162299/100000000000000 : ℝ)^4183
        have hw : |(356409557/625000000 : ℝ)|=(356409557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_5 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202355581/10000000000 : ℝ)*x 0 + (-207759827/2000000000 : ℝ)*x 1 + (5702553009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202355581/10000000000 : ℝ)^5207 ≤ (44332854182269/100000000000000 : ℝ)^4183 := by
    have hnat : (5202355581 : ℕ)^5207*100000000000000^4183 ≤ 44332854182269^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202355581 10000000000 44332854182269 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207759827/2000000000 : ℝ)^5207 ≤ (2983651797593/50000000000000 : ℝ)^4183 := by
    have hnat : (207759827 : ℕ)^5207*50000000000000^4183 ≤ 2983651797593^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207759827 2000000000 2983651797593 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5702553009/10000000000 : ℝ)^5207 ≤ (24849921107321/50000000000000 : ℝ)^4183 := by
    have hnat : (5702553009 : ℕ)^5207*50000000000000^4183 ≤ 24849921107321^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5702553009 10000000000 24849921107321 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202355581/10000000000 : ℝ), (-207759827/2000000000 : ℝ), (5702553009/10000000000 : ℝ)] ![(44332854182269/100000000000000 : ℝ), (2983651797593/50000000000000 : ℝ), (24849921107321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202355581/10000000000 : ℝ)|^5207 ≤ (44332854182269/100000000000000 : ℝ)^4183
        have hw : |(5202355581/10000000000 : ℝ)|=(5202355581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207759827/2000000000 : ℝ)|^5207 ≤ (2983651797593/50000000000000 : ℝ)^4183
        have hw : |(-207759827/2000000000 : ℝ)|=(207759827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5702553009/10000000000 : ℝ)|^5207 ≤ (24849921107321/50000000000000 : ℝ)^4183
        have hw : |(5702553009/10000000000 : ℝ)|=(5702553009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_6 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5202355589/10000000000 : ℝ)*x 0 + (1425638363/2500000000 : ℝ)*x 1 + (-20775969/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202355589/10000000000 : ℝ)^5207 ≤ (44332854267131/100000000000000 : ℝ)^4183 := by
    have hnat : (5202355589 : ℕ)^5207*100000000000000^4183 ≤ 44332854267131^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202355589 10000000000 44332854267131 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1425638363/2500000000 : ℝ)^5207 ≤ (49699847020701/100000000000000 : ℝ)^4183 := by
    have hnat : (1425638363 : ℕ)^5207*100000000000000^4183 ≤ 49699847020701^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425638363 2500000000 49699847020701 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20775969/200000000 : ℝ)^5207 ≤ (5967298696983/100000000000000 : ℝ)^4183 := by
    have hnat : (20775969 : ℕ)^5207*100000000000000^4183 ≤ 5967298696983^4183*200000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20775969 200000000 5967298696983 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202355589/10000000000 : ℝ), (1425638363/2500000000 : ℝ), (-20775969/200000000 : ℝ)] ![(44332854267131/100000000000000 : ℝ), (49699847020701/100000000000000 : ℝ), (5967298696983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202355589/10000000000 : ℝ)|^5207 ≤ (44332854267131/100000000000000 : ℝ)^4183
        have hw : |(5202355589/10000000000 : ℝ)|=(5202355589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1425638363/2500000000 : ℝ)|^5207 ≤ (49699847020701/100000000000000 : ℝ)^4183
        have hw : |(1425638363/2500000000 : ℝ)|=(1425638363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20775969/200000000 : ℝ)|^5207 ≤ (5967298696983/100000000000000 : ℝ)^4183
        have hw : |(-20775969/200000000 : ℝ)|=(20775969/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s0_7 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2027499537/5000000000 : ℝ)*x 0 + (5184165359/10000000000 : ℝ)*x 1 + (3108192611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027499537/5000000000 : ℝ)^5207 ≤ (32510731947361/100000000000000 : ℝ)^4183 := by
    have hnat : (2027499537 : ℕ)^5207*100000000000000^4183 ≤ 32510731947361^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027499537 5000000000 32510731947361 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184165359/10000000000 : ℝ)^5207 ≤ (1379374330553/3125000000000 : ℝ)^4183 := by
    have hnat : (5184165359 : ℕ)^5207*3125000000000^4183 ≤ 1379374330553^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184165359 10000000000 1379374330553 3125000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3108192611/10000000000 : ℝ)^5207 ≤ (23349289467841/100000000000000 : ℝ)^4183 := by
    have hnat : (3108192611 : ℕ)^5207*100000000000000^4183 ≤ 23349289467841^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3108192611 10000000000 23349289467841 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2027499537/5000000000 : ℝ), (5184165359/10000000000 : ℝ), (3108192611/10000000000 : ℝ)] ![(32510731947361/100000000000000 : ℝ), (1379374330553/3125000000000 : ℝ), (23349289467841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2027499537/5000000000 : ℝ)|^5207 ≤ (32510731947361/100000000000000 : ℝ)^4183
        have hw : |(2027499537/5000000000 : ℝ)|=(2027499537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184165359/10000000000 : ℝ)|^5207 ≤ (1379374330553/3125000000000 : ℝ)^4183
        have hw : |(5184165359/10000000000 : ℝ)|=(5184165359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3108192611/10000000000 : ℝ)|^5207 ≤ (23349289467841/100000000000000 : ℝ)^4183
        have hw : |(3108192611/10000000000 : ℝ)|=(3108192611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1698_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (711/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1117/5000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5199/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5199 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5199*1^1024 ≤ 0^1024*1^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5199/1024 : ℝ) ≤ (238528081663162941/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5199 ≤ (238528081663162941/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5199*25000000000000000000^1024 ≤ 238528081663162941^1024*5^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 238528081663162941 25000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (238528081663162941/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5199 := by
      have hnat : (1 : ℕ)^1024*1^5199 ≤ 1^5199*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25238528081663162941/25000000000000000000 : ℝ) ≤ (10018720705236627/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (25238528081663162941/25000000000000000000 : ℝ)^1024 ≤ (10018720705236627/10000000000000000 : ℝ)^5199 := by
      have hnat : (25238528081663162941 : ℕ)^1024*10000000000000000^5199 ≤ 10018720705236627^5199*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25238528081663162941 25000000000000000000 10018720705236627 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018720705236627/10000000000000000 : ℝ)) (X := (25238528081663162941/25000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12738528081663162941/12500000000000000000 : ℝ) ≤ (5018720705236627/5000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (12738528081663162941/12500000000000000000 : ℝ)^1024 ≤ (5018720705236627/5000000000000000 : ℝ)^5199 := by
      have hnat : (12738528081663162941 : ℕ)^1024*5000000000000000^5199 ≤ 5018720705236627^5199*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12738528081663162941 12500000000000000000 5018720705236627 5000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5018720705236627/5000000000000000 : ℝ)) (X := (12738528081663162941/12500000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(18720705236627/4000000000000000 : ℝ)*(0 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18720705236627/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(238528081663162941/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(18720705236627/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5199/1024 : ℝ) := by
    rw [show (1 : ℝ)+(18720705236627/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10018720705236627/10000000000000000 : ℝ) by norm_num, show 1+(238528081663162941/25000000000000000000 : ℝ)+(0 : ℝ)=(25238528081663162941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(238528081663162941/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(18720705236627/4000000000000000 : ℝ)*(2/5 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(18720705236627/4000000000000000 : ℝ)*(2/5 : ℝ)=(5018720705236627/5000000000000000 : ℝ) by norm_num, show 1+2*(238528081663162941/25000000000000000000 : ℝ)=(12738528081663162941/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(18720705236627/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18720705236627/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(18720705236627/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18720705236627/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(18720705236627/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (18720705236627/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1372680089/10000000000 : ℝ)*X 0 0+(572251313/1000000000 : ℝ)*X 0 1+(4947089237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((676598317/1250000000 : ℝ)*X 1 0+(-1794263159/10000000000 : ℝ)*X 1 1+(4947088721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((676598251/1250000000 : ℝ)*X 2 0+(4947089219/10000000000 : ℝ)*X 2 1+(-1794263213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4049737683/10000000000 : ℝ)*X 0 0+(610381309/2000000000 : ℝ)*X 0 1+(654824911/1250000000 : ℝ)*X 0 2+(4049737683/10000000000 : ℝ)*X 1 0+(610381309/2000000000 : ℝ)*X 1 1+(654824911/1250000000 : ℝ)*X 1 2+(4049737683/10000000000 : ℝ)*X 2 0+(610381309/2000000000 : ℝ)*X 2 1+(654824911/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-687273227/5000000000 : ℝ)*X 0 0+(2483195933/5000000000 : ℝ)*X 0 1+(356409557/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5202355581/10000000000 : ℝ)*X 1 0+(-207759827/2000000000 : ℝ)*X 1 1+(5702553009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5202355589/10000000000 : ℝ)*X 2 0+(1425638363/2500000000 : ℝ)*X 2 1+(-20775969/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2027499537/5000000000 : ℝ)*X 0 0+(5184165359/10000000000 : ℝ)*X 0 1+(3108192611/10000000000 : ℝ)*X 0 2+(2027499537/5000000000 : ℝ)*X 1 0+(5184165359/10000000000 : ℝ)*X 1 1+(3108192611/10000000000 : ℝ)*X 1 2+(2027499537/5000000000 : ℝ)*X 2 0+(5184165359/10000000000 : ℝ)*X 2 1+(3108192611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (556615066742279133/62500000000000000000000 : ℝ) := by norm_num
    linear_combination (32634839/20000000000000 : ℝ)*(base1) + (69182757/4000000000000 : ℝ)*(base19) + (200471227/12500000000000 : ℝ)*(base23) + (127036571/50000000000000 : ℝ)*(upper3) + (102972113/50000000000000 : ℝ)*(upper5) + (873473142481337/100000000000000 : ℝ)*(major0) + (873473142481337/100000000000000 : ℝ)*(major1) + (873473142481337/100000000000000 : ℝ)*(major2) + (1289623781378347/100000000000000 : ℝ)*(sp0) + (128962814431733/10000000000000 : ℝ)*(sp1) + (32240706752911/2500000000000 : ℝ)*(sp2) + (91462737095829/20000000000000 : ℝ)*(sp3) + (781960263/12500000000000 : ℝ)*(sp4) + (283195213/12500000000000 : ℝ)*(sp7) + (91463222843009/20000000000000 : ℝ)*(f.failure) + (80601867117891/6250000000000 : ℝ)*(f.sum) + (223290309930299/200000000000000000000000000000 : ℝ)*base65 + (34117342330299/400000000000000000000000000000 : ℝ)*base67 + (294033880069701/400000000000000000000000000000 : ℝ)*base70 + (1822287711930299/400000000000000000000000000000 : ℝ)*base71 + (235945541869701/200000000000000000000000000000 : ℝ)*base74 + (2382847382730299/400000000000000000000000000000 : ℝ)*base75 + (931366655930299/400000000000000000000000000000 : ℝ)*base77 + (928321932069701/400000000000000000000000000000 : ℝ)*base80 + (103670720469701/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3821749/2000000000000000000000 : ℝ)*base89 + (3821749/2000000000000000000000 : ℝ)*base91 + (3821749/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162504963873779226970311/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2067515097/100000000000000 : ℝ)*(base19) + (1062713657/50000000000000 : ℝ)*(base23) + (1868311/25000000000000 : ℝ)*(base32) + (87301027/25000000000000 : ℝ)*(upper3) + (308546507/100000000000000 : ℝ)*(upper5) + (460025107755969/50000000000000 : ℝ)*(major0) + (460025107755969/50000000000000 : ℝ)*(major1) + (460025107755969/50000000000000 : ℝ)*(major2) + (1828266457/25000000000000 : ℝ)*(sp1) + (271661681/3125000000000 : ℝ)*(sp2) + (1358398126110133/100000000000000 : ℝ)*(sp4) + (169798593191151/12500000000000 : ℝ)*(sp5) + (679193653754513/50000000000000 : ℝ)*(sp6) + (120425506649721/25000000000000 : ℝ)*(sp7) + (7526594282377/1562500000000 : ℝ)*(f.failure) + (1358398126110133/100000000000000 : ℝ)*(f.sum) + (82729613276563/100000000000000000000000000000 : ℝ)*base65 + (85636390123437/200000000000000000000000000000 : ℝ)*base68 + (892510432676563/200000000000000000000000000000 : ℝ)*base69 + (527444102276563/200000000000000000000000000000 : ℝ)*base71 + (57711754276563/100000000000000000000000000000 : ℝ)*base73 + (525459319876563/200000000000000000000000000000 : ℝ)*base75 + (1565134703476563/200000000000000000000000000000 : ℝ)*base77 + (1857838005476563/200000000000000000000000000000 : ℝ)*base79 + (274958843876563/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1375403/156250000000000000000 : ℝ)*base90 + (1375403/156250000000000000000 : ℝ)*base92 + (1375403/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1698_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1117/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1698_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1698_s1_0 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-90745367/625000000 : ℝ)*x 0 + (5496880701/10000000000 : ℝ)*x 1 + (1024145417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90745367/625000000 : ℝ)^5207 ≤ (4526454172079/50000000000000 : ℝ)^4183 := by
    have hnat : (90745367 : ℕ)^5207*50000000000000^4183 ≤ 4526454172079^4183*625000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90745367 625000000 4526454172079 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496880701/10000000000 : ℝ)^5207 ≤ (47478466710743/100000000000000 : ℝ)^4183 := by
    have hnat : (5496880701 : ℕ)^5207*100000000000000^4183 ≤ 47478466710743^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496880701 10000000000 47478466710743 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024145417/2000000000 : ℝ)^5207 ≤ (43468624932913/100000000000000 : ℝ)^4183 := by
    have hnat : (1024145417 : ℕ)^5207*100000000000000^4183 ≤ 43468624932913^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024145417 2000000000 43468624932913 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90745367/625000000 : ℝ), (5496880701/10000000000 : ℝ), (1024145417/2000000000 : ℝ)] ![(4526454172079/50000000000000 : ℝ), (47478466710743/100000000000000 : ℝ), (43468624932913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90745367/625000000 : ℝ)|^5207 ≤ (4526454172079/50000000000000 : ℝ)^4183
        have hw : |(-90745367/625000000 : ℝ)|=(90745367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496880701/10000000000 : ℝ)|^5207 ≤ (47478466710743/100000000000000 : ℝ)^4183
        have hw : |(5496880701/10000000000 : ℝ)|=(5496880701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1024145417/2000000000 : ℝ)|^5207 ≤ (43468624932913/100000000000000 : ℝ)^4183
        have hw : |(1024145417/2000000000 : ℝ)|=(1024145417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_1 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676338801/5000000000 : ℝ)*x 0 + (-411977053/2500000000 : ℝ)*x 1 + (10241453/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676338801/5000000000 : ℝ)^5207 ≤ (45933039445527/100000000000000 : ℝ)^4183 := by
    have hnat : (2676338801 : ℕ)^5207*100000000000000^4183 ≤ 45933039445527^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676338801 5000000000 45933039445527 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411977053/2500000000 : ℝ)^5207 ≤ (10598341792437/100000000000000 : ℝ)^4183 := by
    have hnat : (411977053 : ℕ)^5207*100000000000000^4183 ≤ 10598341792437^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411977053 2500000000 10598341792437 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10241453/20000000 : ℝ)^5207 ≤ (1358394335979/3125000000000 : ℝ)^4183 := by
    have hnat : (10241453 : ℕ)^5207*3125000000000^4183 ≤ 1358394335979^4183*20000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10241453 20000000 1358394335979 3125000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676338801/5000000000 : ℝ), (-411977053/2500000000 : ℝ), (10241453/20000000 : ℝ)] ![(45933039445527/100000000000000 : ℝ), (10598341792437/100000000000000 : ℝ), (1358394335979/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676338801/5000000000 : ℝ)|^5207 ≤ (45933039445527/100000000000000 : ℝ)^4183
        have hw : |(2676338801/5000000000 : ℝ)|=(2676338801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411977053/2500000000 : ℝ)|^5207 ≤ (10598341792437/100000000000000 : ℝ)^4183
        have hw : |(-411977053/2500000000 : ℝ)|=(411977053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10241453/20000000 : ℝ)|^5207 ≤ (1358394335979/3125000000000 : ℝ)^4183
        have hw : |(10241453/20000000 : ℝ)|=(10241453/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_2 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338169119/2500000000 : ℝ)*x 0 + (2560363739/5000000000 : ℝ)*x 1 + (-823954211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338169119/2500000000 : ℝ)^5207 ≤ (45933027417561/100000000000000 : ℝ)^4183 := by
    have hnat : (1338169119 : ℕ)^5207*100000000000000^4183 ≤ 45933027417561^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338169119 2500000000 45933027417561 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2560363739/5000000000 : ℝ)^5207 ≤ (4346862908567/10000000000000 : ℝ)^4183 := by
    have hnat : (2560363739 : ℕ)^5207*10000000000000^4183 ≤ 4346862908567^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560363739 5000000000 4346862908567 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (823954211/5000000000 : ℝ)^5207 ≤ (5299171736827/50000000000000 : ℝ)^4183 := by
    have hnat : (823954211 : ℕ)^5207*50000000000000^4183 ≤ 5299171736827^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823954211 5000000000 5299171736827 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338169119/2500000000 : ℝ), (2560363739/5000000000 : ℝ), (-823954211/5000000000 : ℝ)] ![(45933027417561/100000000000000 : ℝ), (4346862908567/10000000000000 : ℝ), (5299171736827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338169119/2500000000 : ℝ)|^5207 ≤ (45933027417561/100000000000000 : ℝ)^4183
        have hw : |(1338169119/2500000000 : ℝ)|=(1338169119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2560363739/5000000000 : ℝ)|^5207 ≤ (4346862908567/10000000000000 : ℝ)^4183
        have hw : |(2560363739/5000000000 : ℝ)|=(2560363739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-823954211/5000000000 : ℝ)|^5207 ≤ (5299171736827/50000000000000 : ℝ)^4183
        have hw : |(-823954211/5000000000 : ℝ)|=(823954211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_3 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (128649901/312500000 : ℝ)*x 0 + (451089349/1250000000 : ℝ)*x 1 + (933893359/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128649901/312500000 : ℝ)^5207 ≤ (32352174783/97656250000 : ℝ)^4183 := by
    have hnat : (128649901 : ℕ)^5207*97656250000^4183 ≤ 32352174783^4183*312500000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128649901 312500000 32352174783 97656250000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451089349/1250000000 : ℝ)^5207 ≤ (5623701914459/20000000000000 : ℝ)^4183 := by
    have hnat : (451089349 : ℕ)^5207*20000000000000^4183 ≤ 5623701914459^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451089349 1250000000 5623701914459 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933893359/2000000000 : ℝ)^5207 ≤ (19376431717143/50000000000000 : ℝ)^4183 := by
    have hnat : (933893359 : ℕ)^5207*50000000000000^4183 ≤ 19376431717143^4183*2000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933893359 2000000000 19376431717143 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(128649901/312500000 : ℝ), (451089349/1250000000 : ℝ), (933893359/2000000000 : ℝ)] ![(32352174783/97656250000 : ℝ), (5623701914459/20000000000000 : ℝ), (19376431717143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(128649901/312500000 : ℝ)|^5207 ≤ (32352174783/97656250000 : ℝ)^4183
        have hw : |(128649901/312500000 : ℝ)|=(128649901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451089349/1250000000 : ℝ)|^5207 ≤ (5623701914459/20000000000000 : ℝ)^4183
        have hw : |(451089349/1250000000 : ℝ)|=(451089349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933893359/2000000000 : ℝ)|^5207 ≤ (19376431717143/50000000000000 : ℝ)^4183
        have hw : |(933893359/2000000000 : ℝ)|=(933893359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_4 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1452137101/10000000000 : ℝ)*x 0 + (5125267179/10000000000 : ℝ)*x 1 + (2746132633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1452137101/10000000000 : ℝ)^5207 ≤ (9054547818667/100000000000000 : ℝ)^4183 := by
    have hnat : (1452137101 : ℕ)^5207*100000000000000^4183 ≤ 9054547818667^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452137101 10000000000 9054547818667 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125267179/10000000000 : ℝ)^5207 ≤ (2719787778639/6250000000000 : ℝ)^4183 := by
    have hnat : (5125267179 : ℕ)^5207*6250000000000^4183 ≤ 2719787778639^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125267179 10000000000 2719787778639 6250000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746132633/5000000000 : ℝ)^5207 ≤ (23714423851201/50000000000000 : ℝ)^4183 := by
    have hnat : (2746132633 : ℕ)^5207*50000000000000^4183 ≤ 23714423851201^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746132633 5000000000 23714423851201 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1452137101/10000000000 : ℝ), (5125267179/10000000000 : ℝ), (2746132633/5000000000 : ℝ)] ![(9054547818667/100000000000000 : ℝ), (2719787778639/6250000000000 : ℝ), (23714423851201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1452137101/10000000000 : ℝ)|^5207 ≤ (9054547818667/100000000000000 : ℝ)^4183
        have hw : |(-1452137101/10000000000 : ℝ)|=(1452137101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125267179/10000000000 : ℝ)|^5207 ≤ (2719787778639/6250000000000 : ℝ)^4183
        have hw : |(5125267179/10000000000 : ℝ)|=(5125267179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746132633/5000000000 : ℝ)|^5207 ≤ (23714423851201/50000000000000 : ℝ)^4183
        have hw : |(2746132633/5000000000 : ℝ)|=(2746132633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_5 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625996057/5000000000 : ℝ)*x 0 + (-1276369589/10000000000 : ℝ)*x 1 + (5492265301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625996057/5000000000 : ℝ)^5207 ≤ (44860002094733/100000000000000 : ℝ)^4183 := by
    have hnat : (2625996057 : ℕ)^5207*100000000000000^4183 ≤ 44860002094733^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625996057 5000000000 44860002094733 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276369589/10000000000 : ℝ)^5207 ≤ (7711149810677/100000000000000 : ℝ)^4183 := by
    have hnat : (1276369589 : ℕ)^5207*100000000000000^4183 ≤ 7711149810677^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276369589 10000000000 7711149810677 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492265301/10000000000 : ℝ)^5207 ≤ (47428848078637/100000000000000 : ℝ)^4183 := by
    have hnat : (5492265301 : ℕ)^5207*100000000000000^4183 ≤ 47428848078637^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492265301 10000000000 47428848078637 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625996057/5000000000 : ℝ), (-1276369589/10000000000 : ℝ), (5492265301/10000000000 : ℝ)] ![(44860002094733/100000000000000 : ℝ), (7711149810677/100000000000000 : ℝ), (47428848078637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625996057/5000000000 : ℝ)|^5207 ≤ (44860002094733/100000000000000 : ℝ)^4183
        have hw : |(2625996057/5000000000 : ℝ)|=(2625996057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1276369589/10000000000 : ℝ)|^5207 ≤ (7711149810677/100000000000000 : ℝ)^4183
        have hw : |(-1276369589/10000000000 : ℝ)|=(1276369589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492265301/10000000000 : ℝ)|^5207 ≤ (47428848078637/100000000000000 : ℝ)^4183
        have hw : |(5492265301/10000000000 : ℝ)|=(5492265301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_6 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251991611/10000000000 : ℝ)*x 0 + (274613267/500000000 : ℝ)*x 1 + (-638185123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251991611/10000000000 : ℝ)^5207 ≤ (44859996746591/100000000000000 : ℝ)^4183 := by
    have hnat : (5251991611 : ℕ)^5207*100000000000000^4183 ≤ 44859996746591^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251991611 10000000000 44859996746591 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274613267/500000000 : ℝ)^5207 ≤ (4742884849787/10000000000000 : ℝ)^4183 := by
    have hnat : (274613267 : ℕ)^5207*10000000000000^4183 ≤ 4742884849787^4183*500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274613267 500000000 4742884849787 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638185123/5000000000 : ℝ)^5207 ≤ (7711154751597/100000000000000 : ℝ)^4183 := by
    have hnat : (638185123 : ℕ)^5207*100000000000000^4183 ≤ 7711154751597^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638185123 5000000000 7711154751597 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251991611/10000000000 : ℝ), (274613267/500000000 : ℝ), (-638185123/5000000000 : ℝ)] ![(44859996746591/100000000000000 : ℝ), (4742884849787/10000000000000 : ℝ), (7711154751597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251991611/10000000000 : ℝ)|^5207 ≤ (44859996746591/100000000000000 : ℝ)^4183
        have hw : |(5251991611/10000000000 : ℝ)|=(5251991611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274613267/500000000 : ℝ)|^5207 ≤ (4742884849787/10000000000000 : ℝ)^4183
        have hw : |(274613267/500000000 : ℝ)|=(274613267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-638185123/5000000000 : ℝ)|^5207 ≤ (7711154751597/100000000000000 : ℝ)^4183
        have hw : |(-638185123/5000000000 : ℝ)|=(638185123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s1_7 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2058695121/5000000000 : ℝ)*x 0 + (2328331387/5000000000 : ℝ)*x 1 + (452716171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058695121/5000000000 : ℝ)^5207 ≤ (1325382854133/4000000000000 : ℝ)^4183 := by
    have hnat : (2058695121 : ℕ)^5207*4000000000000^4183 ≤ 1325382854133^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058695121 5000000000 1325382854133 4000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2328331387/5000000000 : ℝ)^5207 ≤ (4827578923843/12500000000000 : ℝ)^4183 := by
    have hnat : (2328331387 : ℕ)^5207*12500000000000^4183 ≤ 4827578923843^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2328331387 5000000000 4827578923843 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452716171/1250000000 : ℝ)^5207 ≤ (7061199311829/25000000000000 : ℝ)^4183 := by
    have hnat : (452716171 : ℕ)^5207*25000000000000^4183 ≤ 7061199311829^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452716171 1250000000 7061199311829 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058695121/5000000000 : ℝ), (2328331387/5000000000 : ℝ), (452716171/1250000000 : ℝ)] ![(1325382854133/4000000000000 : ℝ), (4827578923843/12500000000000 : ℝ), (7061199311829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058695121/5000000000 : ℝ)|^5207 ≤ (1325382854133/4000000000000 : ℝ)^4183
        have hw : |(2058695121/5000000000 : ℝ)|=(2058695121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2328331387/5000000000 : ℝ)|^5207 ≤ (4827578923843/12500000000000 : ℝ)^4183
        have hw : |(2328331387/5000000000 : ℝ)|=(2328331387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452716171/1250000000 : ℝ)|^5207 ≤ (7061199311829/25000000000000 : ℝ)^4183
        have hw : |(452716171/1250000000 : ℝ)|=(452716171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1698_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1117/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9561/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8789/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1117/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (711/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1117/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (711/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1117/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (711/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1117/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (711/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1117/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (711/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1117/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (711/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (711/12500 : ℝ) ^ (5199/1024 : ℝ) ≤ (9544979760567/20000000000000000000 : ℝ) := by
    have hpowers : (711/12500 : ℝ)^5199 ≤ (9544979760567/20000000000000000000 : ℝ)^1024 := by
      have hnat : (711 : ℕ)^5199*20000000000000000000^1024 ≤ 9544979760567^1024*12500^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        711 12500 9544979760567 20000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (711/12500 : ℝ)) (X := (9544979760567/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1117/5000 : ℝ) ^ (5199/1024 : ℝ) ≤ (9913536800432047/20000000000000000000 : ℝ) := by
    have hpowers : (1117/5000 : ℝ)^5199 ≤ (9913536800432047/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1117 : ℕ)^5199*20000000000000000000^1024 ≤ 9913536800432047^1024*5000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1117 5000 9913536800432047 20000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1117/5000 : ℝ)) (X := (9913536800432047/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000009544979760567/10000000000000000000 : ℝ) ≤ (25000004699969/25000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (10000009544979760567/10000000000000000000 : ℝ)^1024 ≤ (25000004699969/25000000000000 : ℝ)^5199 := by
      have hnat : (10000009544979760567 : ℕ)^1024*25000000000000^5199 ≤ 25000004699969^5199*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000009544979760567 10000000000000000000 25000004699969 25000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25000004699969/25000000000000 : ℝ)) (X := (10000009544979760567/10000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004961540890096307/10000000000000000000 : ℝ) ≤ (10000977035205823/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (10004961540890096307/10000000000000000000 : ℝ)^1024 ≤ (10000977035205823/10000000000000000 : ℝ)^5199 := by
      have hnat : (10004961540890096307 : ℕ)^1024*10000000000000000^5199 ≤ 10000977035205823^5199*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004961540890096307 10000000000000000000 10000977035205823 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000977035205823/10000000000000000 : ℝ)) (X := (10004961540890096307/10000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009913536800432047/10000000000000000000 : ℝ) ≤ (5000976095212023/5000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (10009913536800432047/10000000000000000000 : ℝ)^1024 ≤ (5000976095212023/5000000000000000 : ℝ)^5199 := by
      have hnat : (10009913536800432047 : ℕ)^1024*5000000000000000^5199 ≤ 5000976095212023^5199*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009913536800432047 10000000000000000000 5000976095212023 5000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000976095212023/5000000000000000 : ℝ)) (X := (10009913536800432047/10000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9544979760567/20000000000000000000 : ℝ) ≤ ((10406808621236938147/10407500000000000000 : ℝ)+2*(975155218223/1665200000000000 : ℝ)*(711/12500 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (10406808621236938147/10407500000000000000 : ℝ)+2*(975155218223/1665200000000000 : ℝ)*(711/12500 : ℝ)=(25000004699969/25000000000000 : ℝ) by norm_num, show 1+2*(9544979760567/20000000000000000000 : ℝ)=(10000009544979760567/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9913536800432047/20000000000000000000 : ℝ)+(9544979760567/20000000000000000000 : ℝ) ≤ ((10406808621236938147/10407500000000000000 : ℝ)+(975155218223/1665200000000000 : ℝ)*((1117/5000 : ℝ)+(711/12500 : ℝ)))^(5199/1024 : ℝ) := by
    rw [show (10406808621236938147/10407500000000000000 : ℝ)+(975155218223/1665200000000000 : ℝ)*((1117/5000 : ℝ)+(711/12500 : ℝ))=(10000977035205823/10000000000000000 : ℝ) by norm_num, show 1+(9913536800432047/20000000000000000000 : ℝ)+(9544979760567/20000000000000000000 : ℝ)=(10004961540890096307/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9913536800432047/20000000000000000000 : ℝ) ≤ ((10406808621236938147/10407500000000000000 : ℝ)+2*(975155218223/1665200000000000 : ℝ)*(1117/5000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (10406808621236938147/10407500000000000000 : ℝ)+2*(975155218223/1665200000000000 : ℝ)*(1117/5000 : ℝ)=(5000976095212023/5000000000000000 : ℝ) by norm_num, show 1+2*(9913536800432047/20000000000000000000 : ℝ)=(10009913536800432047/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10406808621236938147/10407500000000000000 : ℝ)*(X 1 0+X 2 0)+(975155218223/1665200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (711/12500 : ℝ)) (hi := (1117/5000 : ℝ)) (c := (10406808621236938147/10407500000000000000 : ℝ)) (alpha := (975155218223/1665200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10406808621236938147/10407500000000000000 : ℝ)*(X 0 1+X 2 1)+(975155218223/1665200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (711/12500 : ℝ)) (hi := (1117/5000 : ℝ)) (c := (10406808621236938147/10407500000000000000 : ℝ)) (alpha := (975155218223/1665200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10406808621236938147/10407500000000000000 : ℝ)*(X 0 2+X 1 2)+(975155218223/1665200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (711/12500 : ℝ)) (hi := (1117/5000 : ℝ)) (c := (10406808621236938147/10407500000000000000 : ℝ)) (alpha := (975155218223/1665200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-90745367/625000000 : ℝ)*X 0 0+(5496880701/10000000000 : ℝ)*X 0 1+(1024145417/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676338801/5000000000 : ℝ)*X 1 0+(-411977053/2500000000 : ℝ)*X 1 1+(10241453/20000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338169119/2500000000 : ℝ)*X 2 0+(2560363739/5000000000 : ℝ)*X 2 1+(-823954211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((128649901/312500000 : ℝ)*X 0 0+(451089349/1250000000 : ℝ)*X 0 1+(933893359/2000000000 : ℝ)*X 0 2+(128649901/312500000 : ℝ)*X 1 0+(451089349/1250000000 : ℝ)*X 1 1+(933893359/2000000000 : ℝ)*X 1 2+(128649901/312500000 : ℝ)*X 2 0+(451089349/1250000000 : ℝ)*X 2 1+(933893359/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1452137101/10000000000 : ℝ)*X 0 0+(5125267179/10000000000 : ℝ)*X 0 1+(2746132633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2625996057/5000000000 : ℝ)*X 1 0+(-1276369589/10000000000 : ℝ)*X 1 1+(5492265301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251991611/10000000000 : ℝ)*X 2 0+(274613267/500000000 : ℝ)*X 2 1+(-638185123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2058695121/5000000000 : ℝ)*X 0 0+(2328331387/5000000000 : ℝ)*X 0 1+(452716171/1250000000 : ℝ)*X 0 2+(2058695121/5000000000 : ℝ)*X 1 0+(2328331387/5000000000 : ℝ)*X 1 1+(452716171/1250000000 : ℝ)*X 1 2+(2058695121/5000000000 : ℝ)*X 2 0+(2328331387/5000000000 : ℝ)*X 2 1+(452716171/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (334786936969278955184027277/26018750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1851175631/100000000000000 : ℝ)*(base19) + (1231396101/100000000000000 : ℝ)*(base23) + (6479859/20000000000000 : ℝ)*(lower2) + (3436381/1000000000000 : ℝ)*(upper3) + (22001273/25000000000000 : ℝ)*(upper5) + (90031324734699/5000000000000 : ℝ)*(major0) + (90031324734699/5000000000000 : ℝ)*(major1) + (90031324734699/5000000000000 : ℝ)*(major2) + (166156538371151/6250000000000 : ℝ)*(sp0) + (1329256819287701/50000000000000 : ℝ)*(sp1) + (664628564588733/25000000000000 : ℝ)*(sp2) + (47136586015927/5000000000000 : ℝ)*(sp3) + (10875812617/100000000000000 : ℝ)*(sp4) + (167200427/3125000000000 : ℝ)*(sp7) + (235684267683051/25000000000000 : ℝ)*(f.failure) + (2658515489751033/100000000000000 : ℝ)*(f.sum) + (625208342483/208150000000000000000000000 : ℝ)*base66 + (572924892678418497/52037500000000000000000000000000 : ℝ)*base68 + (417662032826130997/52037500000000000000000000000000 : ℝ)*base70 + (464727653496055997/52037500000000000000000000000000 : ℝ)*base72 + (5499321930019/4163000000000000000000000000 : ℝ)*base74 + (524999498806555997/52037500000000000000000000000000 : ℝ)*base76 + (646933505913105997/52037500000000000000000000000000 : ℝ)*base78 + (364364547693805997/52037500000000000000000000000000 : ℝ)*base80 + (1084626766847/4163000000000000000000000000 : ℝ)*base82 + (33055911/2500000000000000000000 : ℝ)*base89 + (33055911/2500000000000000000000 : ℝ)*base91 + (33055911/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (317341412395229301365872947/26018750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (260647769/12500000000000 : ℝ)*(base19) + (1065102389/50000000000000 : ℝ)*(base23) + (189578877/100000000000000 : ℝ)*(upper2) + (1637151/500000000000 : ℝ)*(upper3) + (181998353/50000000000000 : ℝ)*(upper5) + (369105224760809/20000000000000 : ℝ)*(major0) + (369105224760809/20000000000000 : ℝ)*(major1) + (369105224760809/20000000000000 : ℝ)*(major2) + (16742569467/100000000000000 : ℝ)*(sp1) + (1734347541/12500000000000 : ℝ)*(sp2) + (544961418798699/20000000000000 : ℝ)*(sp4) + (681197066560469/25000000000000 : ℝ)*(sp5) + (681197772252097/25000000000000 : ℝ)*(sp6) + (483122373529907/50000000000000 : ℝ)*(sp7) + (483122373529907/50000000000000 : ℝ)*(f.failure) + (544961418798699/20000000000000 : ℝ)*(f.sum) + (1048737465029/16652000000000000000000000000 : ℝ)*base66 + (1409638455031425327/208150000000000000000000000000000 : ℝ)*base68 + (760355656516575327/208150000000000000000000000000000 : ℝ)*base70 + (517156685943175327/208150000000000000000000000000000 : ℝ)*base72 + (55982271293929/16652000000000000000000000000 : ℝ)*base74 + (1419624053090475327/208150000000000000000000000000000 : ℝ)*base76 + (169390739106875327/208150000000000000000000000000000 : ℝ)*base78 + (1176413761724673/208150000000000000000000000000000 : ℝ)*base79 + (34450895926169/16652000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (66342927/5000000000000000000000 : ℝ)*base89 + (66342927/5000000000000000000000 : ℝ)*base91 + (66342927/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1698_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1117/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9561/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8789/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1698_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1698_s2_0 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182053567/1250000000 : ℝ)*x 0 + (273932651/500000000 : ℝ)*x 1 + (641994029/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182053567/1250000000 : ℝ)^5207 ≤ (908786884323/10000000000000 : ℝ)^4183 := by
    have hnat : (182053567 : ℕ)^5207*10000000000000^4183 ≤ 908786884323^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182053567 1250000000 908786884323 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273932651/500000000 : ℝ)^5207 ≤ (4728256643299/10000000000000 : ℝ)^4183 := by
    have hnat : (273932651 : ℕ)^5207*10000000000000^4183 ≤ 4728256643299^4183*500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273932651 500000000 4728256643299 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (641994029/1250000000 : ℝ)^5207 ≤ (43629564705479/100000000000000 : ℝ)^4183 := by
    have hnat : (641994029 : ℕ)^5207*100000000000000^4183 ≤ 43629564705479^4183*1250000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641994029 1250000000 43629564705479 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182053567/1250000000 : ℝ), (273932651/500000000 : ℝ), (641994029/1250000000 : ℝ)] ![(908786884323/10000000000000 : ℝ), (4728256643299/10000000000000 : ℝ), (43629564705479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182053567/1250000000 : ℝ)|^5207 ≤ (908786884323/10000000000000 : ℝ)^4183
        have hw : |(-182053567/1250000000 : ℝ)|=(182053567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273932651/500000000 : ℝ)|^5207 ≤ (4728256643299/10000000000000 : ℝ)^4183
        have hw : |(273932651/500000000 : ℝ)|=(273932651/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(641994029/1250000000 : ℝ)|^5207 ≤ (43629564705479/100000000000000 : ℝ)^4183
        have hw : |(641994029/1250000000 : ℝ)|=(641994029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_1 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336942107/2500000000 : ℝ)*x 0 + (-25536569/156250000 : ℝ)*x 1 + (5135952179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336942107/2500000000 : ℝ)^5207 ≤ (5735075673453/12500000000000 : ℝ)^4183 := by
    have hnat : (1336942107 : ℕ)^5207*12500000000000^4183 ≤ 5735075673453^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336942107 2500000000 5735075673453 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25536569/156250000 : ℝ)^5207 ≤ (1311228806649/12500000000000 : ℝ)^4183 := by
    have hnat : (25536569 : ℕ)^5207*12500000000000^4183 ≤ 1311228806649^4183*156250000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25536569 156250000 1311228806649 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135952179/10000000000 : ℝ)^5207 ≤ (4362956414503/10000000000000 : ℝ)^4183 := by
    have hnat : (5135952179 : ℕ)^5207*10000000000000^4183 ≤ 4362956414503^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135952179 10000000000 4362956414503 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336942107/2500000000 : ℝ), (-25536569/156250000 : ℝ), (5135952179/10000000000 : ℝ)] ![(5735075673453/12500000000000 : ℝ), (1311228806649/12500000000000 : ℝ), (4362956414503/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336942107/2500000000 : ℝ)|^5207 ≤ (5735075673453/12500000000000 : ℝ)^4183
        have hw : |(1336942107/2500000000 : ℝ)|=(1336942107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25536569/156250000 : ℝ)|^5207 ≤ (1311228806649/12500000000000 : ℝ)^4183
        have hw : |(-25536569/156250000 : ℝ)|=(25536569/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135952179/10000000000 : ℝ)|^5207 ≤ (4362956414503/10000000000000 : ℝ)^4183
        have hw : |(5135952179/10000000000 : ℝ)|=(5135952179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_2 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347768581/10000000000 : ℝ)*x 0 + (1283988037/2500000000 : ℝ)*x 1 + (-408585063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347768581/10000000000 : ℝ)^5207 ≤ (5735075877701/12500000000000 : ℝ)^4183 := by
    have hnat : (5347768581 : ℕ)^5207*12500000000000^4183 ≤ 5735075877701^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347768581 10000000000 5735075877701 12500000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283988037/2500000000 : ℝ)^5207 ≤ (43629563817221/100000000000000 : ℝ)^4183 := by
    have hnat : (1283988037 : ℕ)^5207*100000000000000^4183 ≤ 43629563817221^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283988037 2500000000 43629563817221 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408585063/2500000000 : ℝ)^5207 ≤ (655614321431/6250000000000 : ℝ)^4183 := by
    have hnat : (408585063 : ℕ)^5207*6250000000000^4183 ≤ 655614321431^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408585063 2500000000 655614321431 6250000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347768581/10000000000 : ℝ), (1283988037/2500000000 : ℝ), (-408585063/2500000000 : ℝ)] ![(5735075877701/12500000000000 : ℝ), (43629563817221/100000000000000 : ℝ), (655614321431/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347768581/10000000000 : ℝ)|^5207 ≤ (5735075877701/12500000000000 : ℝ)^4183
        have hw : |(5347768581/10000000000 : ℝ)|=(5347768581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283988037/2500000000 : ℝ)|^5207 ≤ (43629563817221/100000000000000 : ℝ)^4183
        have hw : |(1283988037/2500000000 : ℝ)|=(1283988037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408585063/2500000000 : ℝ)|^5207 ≤ (655614321431/6250000000000 : ℝ)^4183
        have hw : |(-408585063/2500000000 : ℝ)|=(408585063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_3 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4120270957/10000000000 : ℝ)*x 0 + (3655566357/10000000000 : ℝ)*x 1 + (2310990793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4120270957/10000000000 : ℝ)^5207 ≤ (16581715682961/50000000000000 : ℝ)^4183 := by
    have hnat : (4120270957 : ℕ)^5207*50000000000000^4183 ≤ 16581715682961^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120270957 10000000000 16581715682961 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3655566357/10000000000 : ℝ)^5207 ≤ (2857365575741/10000000000000 : ℝ)^4183 := by
    have hnat : (3655566357 : ℕ)^5207*10000000000000^4183 ≤ 2857365575741^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3655566357 10000000000 2857365575741 10000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2310990793/5000000000 : ℝ)^5207 ≤ (38262912863471/100000000000000 : ℝ)^4183 := by
    have hnat : (2310990793 : ℕ)^5207*100000000000000^4183 ≤ 38262912863471^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310990793 5000000000 38262912863471 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4120270957/10000000000 : ℝ), (3655566357/10000000000 : ℝ), (2310990793/5000000000 : ℝ)] ![(16581715682961/50000000000000 : ℝ), (2857365575741/10000000000000 : ℝ), (38262912863471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4120270957/10000000000 : ℝ)|^5207 ≤ (16581715682961/50000000000000 : ℝ)^4183
        have hw : |(4120270957/10000000000 : ℝ)|=(4120270957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3655566357/10000000000 : ℝ)|^5207 ≤ (2857365575741/10000000000000 : ℝ)^4183
        have hw : |(3655566357/10000000000 : ℝ)|=(3655566357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2310990793/5000000000 : ℝ)|^5207 ≤ (38262912863471/100000000000000 : ℝ)^4183
        have hw : |(2310990793/5000000000 : ℝ)|=(2310990793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_4 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-728293839/5000000000 : ℝ)*x 0 + (5139724149/10000000000 : ℝ)*x 1 + (2737412277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (728293839/5000000000 : ℝ)^5207 ≤ (2272276242637/25000000000000 : ℝ)^4183 := by
    have hnat : (728293839 : ℕ)^5207*25000000000000^4183 ≤ 2272276242637^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728293839 5000000000 2272276242637 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139724149/10000000000 : ℝ)^5207 ≤ (21834727202999/50000000000000 : ℝ)^4183 := by
    have hnat : (5139724149 : ℕ)^5207*50000000000000^4183 ≤ 21834727202999^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139724149 10000000000 21834727202999 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2737412277/5000000000 : ℝ)^5207 ≤ (1476295019073/3125000000000 : ℝ)^4183 := by
    have hnat : (2737412277 : ℕ)^5207*3125000000000^4183 ≤ 1476295019073^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737412277 5000000000 1476295019073 3125000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-728293839/5000000000 : ℝ), (5139724149/10000000000 : ℝ), (2737412277/5000000000 : ℝ)] ![(2272276242637/25000000000000 : ℝ), (21834727202999/50000000000000 : ℝ), (1476295019073/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-728293839/5000000000 : ℝ)|^5207 ≤ (2272276242637/25000000000000 : ℝ)^4183
        have hw : |(-728293839/5000000000 : ℝ)|=(728293839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139724149/10000000000 : ℝ)|^5207 ≤ (21834727202999/50000000000000 : ℝ)^4183
        have hw : |(5139724149/10000000000 : ℝ)|=(5139724149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2737412277/5000000000 : ℝ)|^5207 ≤ (1476295019073/3125000000000 : ℝ)^4183
        have hw : |(2737412277/5000000000 : ℝ)|=(2737412277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_5 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628042289/5000000000 : ℝ)*x 0 + (-1295467969/10000000000 : ℝ)*x 1 + (218992983/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628042289/5000000000 : ℝ)^5207 ≤ (11225879830511/25000000000000 : ℝ)^4183 := by
    have hnat : (2628042289 : ℕ)^5207*25000000000000^4183 ≤ 11225879830511^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628042289 5000000000 11225879830511 25000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295467969/10000000000 : ℝ)^5207 ≤ (3927519909701/50000000000000 : ℝ)^4183 := by
    have hnat : (1295467969 : ℕ)^5207*50000000000000^4183 ≤ 3927519909701^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295467969 10000000000 3927519909701 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218992983/400000000 : ℝ)^5207 ≤ (47241440835901/100000000000000 : ℝ)^4183 := by
    have hnat : (218992983 : ℕ)^5207*100000000000000^4183 ≤ 47241440835901^4183*400000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218992983 400000000 47241440835901 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628042289/5000000000 : ℝ), (-1295467969/10000000000 : ℝ), (218992983/400000000 : ℝ)] ![(11225879830511/25000000000000 : ℝ), (3927519909701/50000000000000 : ℝ), (47241440835901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628042289/5000000000 : ℝ)|^5207 ≤ (11225879830511/25000000000000 : ℝ)^4183
        have hw : |(2628042289/5000000000 : ℝ)|=(2628042289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1295467969/10000000000 : ℝ)|^5207 ≤ (3927519909701/50000000000000 : ℝ)^4183
        have hw : |(-1295467969/10000000000 : ℝ)|=(1295467969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218992983/400000000 : ℝ)|^5207 ≤ (47241440835901/100000000000000 : ℝ)^4183
        have hw : |(218992983/400000000 : ℝ)|=(218992983/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_6 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210243383/400000000 : ℝ)*x 0 + (5474824583/10000000000 : ℝ)*x 1 + (-323866991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210243383/400000000 : ℝ)^5207 ≤ (2245175964507/5000000000000 : ℝ)^4183 := by
    have hnat : (210243383 : ℕ)^5207*5000000000000^4183 ≤ 2245175964507^4183*400000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210243383 400000000 2245175964507 5000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474824583/10000000000 : ℝ)^5207 ≤ (47241440921831/100000000000000 : ℝ)^4183 := by
    have hnat : (5474824583 : ℕ)^5207*100000000000000^4183 ≤ 47241440921831^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474824583 10000000000 47241440921831 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323866991/2500000000 : ℝ)^5207 ≤ (7855039781663/100000000000000 : ℝ)^4183 := by
    have hnat : (323866991 : ℕ)^5207*100000000000000^4183 ≤ 7855039781663^4183*2500000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323866991 2500000000 7855039781663 100000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210243383/400000000 : ℝ), (5474824583/10000000000 : ℝ), (-323866991/2500000000 : ℝ)] ![(2245175964507/5000000000000 : ℝ), (47241440921831/100000000000000 : ℝ), (7855039781663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210243383/400000000 : ℝ)|^5207 ≤ (2245175964507/5000000000000 : ℝ)^4183
        have hw : |(210243383/400000000 : ℝ)|=(210243383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474824583/10000000000 : ℝ)|^5207 ≤ (47241440921831/100000000000000 : ℝ)^4183
        have hw : |(5474824583/10000000000 : ℝ)|=(5474824583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323866991/2500000000 : ℝ)|^5207 ≤ (7855039781663/100000000000000 : ℝ)^4183
        have hw : |(-323866991/2500000000 : ℝ)|=(323866991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1698_s2_7 (p : ℝ) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4120719833/10000000000 : ℝ)*x 0 + (2305672373/5000000000 : ℝ)*x 1 + (3666362577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4120719833/10000000000 : ℝ)^5207 ≤ (64781110953/195312500000 : ℝ)^4183 := by
    have hnat : (4120719833 : ℕ)^5207*195312500000^4183 ≤ 64781110953^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120719833 10000000000 64781110953 195312500000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2305672373/5000000000 : ℝ)^5207 ≤ (7630666146869/20000000000000 : ℝ)^4183 := by
    have hnat : (2305672373 : ℕ)^5207*20000000000000^4183 ≤ 7630666146869^4183*5000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305672373 5000000000 7630666146869 20000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3666362577/10000000000 : ℝ)^5207 ≤ (14339370220951/50000000000000 : ℝ)^4183 := by
    have hnat : (3666362577 : ℕ)^5207*50000000000000^4183 ≤ 14339370220951^4183*10000000000^5207 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666362577 10000000000 14339370220951 50000000000000 5207 4183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5207/1024 : ℝ)) 5207 4183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4120719833/10000000000 : ℝ), (2305672373/5000000000 : ℝ), (3666362577/10000000000 : ℝ)] ![(64781110953/195312500000 : ℝ), (7630666146869/20000000000000 : ℝ), (14339370220951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4120719833/10000000000 : ℝ)|^5207 ≤ (64781110953/195312500000 : ℝ)^4183
        have hw : |(4120719833/10000000000 : ℝ)|=(4120719833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2305672373/5000000000 : ℝ)|^5207 ≤ (7630666146869/20000000000000 : ℝ)^4183
        have hw : |(2305672373/5000000000 : ℝ)|=(2305672373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3666362577/10000000000 : ℝ)|^5207 ≤ (14339370220951/50000000000000 : ℝ)^4183
        have hw : |(3666362577/10000000000 : ℝ)|=(3666362577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1698_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8789/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9561/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9893/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4299/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8789/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9561/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8789/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9561/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8789/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9561/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8789/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9561/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8789/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9561/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8789/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9561/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9561/100000 : ℝ) ^ (5199/1024 : ℝ) ≤ (666598013231367/100000000000000000000 : ℝ) := by
    have hpowers : (9561/100000 : ℝ)^5199 ≤ (666598013231367/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9561 : ℕ)^5199*100000000000000000000^1024 ≤ 666598013231367^1024*100000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9561 100000 666598013231367 100000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9561/100000 : ℝ)) (X := (666598013231367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8789/50000 : ℝ) ^ (5199/1024 : ℝ) ≤ (2935133572214439/20000000000000000000 : ℝ) := by
    have hpowers : (8789/50000 : ℝ)^5199 ≤ (2935133572214439/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8789 : ℕ)^5199*20000000000000000000^1024 ≤ 2935133572214439^1024*50000^5199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8789 50000 2935133572214439 20000000000000000000 5199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8789/50000 : ℝ)) (X := (2935133572214439/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000666598013231367/50000000000000000000 : ℝ) ≤ (2000005251723113/2000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (50000666598013231367/50000000000000000000 : ℝ)^1024 ≤ (2000005251723113/2000000000000000 : ℝ)^5199 := by
      have hnat : (50000666598013231367 : ℕ)^1024*2000000000000000^5199 ≤ 2000005251723113^5199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000666598013231367 50000000000000000000 2000005251723113 2000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005251723113/2000000000000000 : ℝ)) (X := (50000666598013231367/50000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007671132937151781/50000000000000000000 : ℝ) ≤ (2500075541029739/2500000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (50007671132937151781/50000000000000000000 : ℝ)^1024 ≤ (2500075541029739/2500000000000000 : ℝ)^5199 := by
      have hnat : (50007671132937151781 : ℕ)^1024*2500000000000000^5199 ≤ 2500075541029739^5199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007671132937151781 50000000000000000000 2500075541029739 2500000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500075541029739/2500000000000000 : ℝ)) (X := (50007671132937151781/50000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002935133572214439/10000000000000000000 : ℝ) ≤ (10000578069622347/10000000000000000 : ℝ) ^ (5199/1024 : ℝ) := by
    have hpowers : (10002935133572214439/10000000000000000000 : ℝ)^1024 ≤ (10000578069622347/10000000000000000 : ℝ)^5199 := by
      have hnat : (10002935133572214439 : ℕ)^1024*10000000000000000^5199 ≤ 10000578069622347^5199*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002935133572214439 10000000000000000000 10000578069622347 10000000000000000 1024 5199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000578069622347/10000000000000000 : ℝ)) (X := (10002935133572214439/10000000000000000000 : ℝ)) (by norm_num) 5199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(666598013231367/100000000000000000000 : ℝ) ≤ ((80164934650285141903/80170000000000000000 : ℝ)+2*(275905503391/801700000000000 : ℝ)*(9561/100000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (80164934650285141903/80170000000000000000 : ℝ)+2*(275905503391/801700000000000 : ℝ)*(9561/100000 : ℝ)=(2000005251723113/2000000000000000 : ℝ) by norm_num, show 1+2*(666598013231367/100000000000000000000 : ℝ)=(50000666598013231367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2935133572214439/20000000000000000000 : ℝ)+(666598013231367/100000000000000000000 : ℝ) ≤ ((80164934650285141903/80170000000000000000 : ℝ)+(275905503391/801700000000000 : ℝ)*((8789/50000 : ℝ)+(9561/100000 : ℝ)))^(5199/1024 : ℝ) := by
    rw [show (80164934650285141903/80170000000000000000 : ℝ)+(275905503391/801700000000000 : ℝ)*((8789/50000 : ℝ)+(9561/100000 : ℝ))=(2500075541029739/2500000000000000 : ℝ) by norm_num, show 1+(2935133572214439/20000000000000000000 : ℝ)+(666598013231367/100000000000000000000 : ℝ)=(50007671132937151781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2935133572214439/20000000000000000000 : ℝ) ≤ ((80164934650285141903/80170000000000000000 : ℝ)+2*(275905503391/801700000000000 : ℝ)*(8789/50000 : ℝ))^(5199/1024 : ℝ) := by
    rw [show (80164934650285141903/80170000000000000000 : ℝ)+2*(275905503391/801700000000000 : ℝ)*(8789/50000 : ℝ)=(10000578069622347/10000000000000000 : ℝ) by norm_num, show 1+2*(2935133572214439/20000000000000000000 : ℝ)=(10002935133572214439/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (80164934650285141903/80170000000000000000 : ℝ)*(X 1 0+X 2 0)+(275905503391/801700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9561/100000 : ℝ)) (hi := (8789/50000 : ℝ)) (c := (80164934650285141903/80170000000000000000 : ℝ)) (alpha := (275905503391/801700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (80164934650285141903/80170000000000000000 : ℝ)*(X 0 1+X 2 1)+(275905503391/801700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9561/100000 : ℝ)) (hi := (8789/50000 : ℝ)) (c := (80164934650285141903/80170000000000000000 : ℝ)) (alpha := (275905503391/801700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (80164934650285141903/80170000000000000000 : ℝ)*(X 0 2+X 1 2)+(275905503391/801700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5199/1024 : ℝ)) (lo := (9561/100000 : ℝ)) (hi := (8789/50000 : ℝ)) (c := (80164934650285141903/80170000000000000000 : ℝ)) (alpha := (275905503391/801700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-182053567/1250000000 : ℝ)*X 0 0+(273932651/500000000 : ℝ)*X 0 1+(641994029/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336942107/2500000000 : ℝ)*X 1 0+(-25536569/156250000 : ℝ)*X 1 1+(5135952179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347768581/10000000000 : ℝ)*X 2 0+(1283988037/2500000000 : ℝ)*X 2 1+(-408585063/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4120270957/10000000000 : ℝ)*X 0 0+(3655566357/10000000000 : ℝ)*X 0 1+(2310990793/5000000000 : ℝ)*X 0 2+(4120270957/10000000000 : ℝ)*X 1 0+(3655566357/10000000000 : ℝ)*X 1 1+(2310990793/5000000000 : ℝ)*X 1 2+(4120270957/10000000000 : ℝ)*X 2 0+(3655566357/10000000000 : ℝ)*X 2 1+(2310990793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-728293839/5000000000 : ℝ)*X 0 0+(5139724149/10000000000 : ℝ)*X 0 1+(2737412277/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628042289/5000000000 : ℝ)*X 1 0+(-1295467969/10000000000 : ℝ)*X 1 1+(218992983/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210243383/400000000 : ℝ)*X 2 0+(5474824583/10000000000 : ℝ)*X 2 1+(-323866991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4120719833/10000000000 : ℝ)*X 0 0+(2305672373/5000000000 : ℝ)*X 0 1+(3666362577/10000000000 : ℝ)*X 0 2+(4120719833/10000000000 : ℝ)*X 1 0+(2305672373/5000000000 : ℝ)*X 1 1+(3666362577/10000000000 : ℝ)*X 1 2+(4120719833/10000000000 : ℝ)*X 2 0+(2305672373/5000000000 : ℝ)*X 2 1+(3666362577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1698_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7611572507800894290541810413/2004250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259768521/50000000000000 : ℝ)*(base19) + (285016369/50000000000000 : ℝ)*(base23) + (17641573/100000000000000 : ℝ)*(lower2) + (1559121/5000000000000 : ℝ)*(upper3) + (60063719/50000000000000 : ℝ)*(upper5) + (1976381399155057/100000000000000 : ℝ)*(major0) + (1976381399155057/100000000000000 : ℝ)*(major1) + (1976381399155057/100000000000000 : ℝ)*(major2) + (1459000589376667/50000000000000 : ℝ)*(sp0) + (1459003369948573/50000000000000 : ℝ)*(sp1) + (58360133788029/2000000000000 : ℝ)*(sp2) + (129344226397227/12500000000000 : ℝ)*(sp3) + (3040340427/50000000000000 : ℝ)*(sp4) + (1601107567/100000000000000 : ℝ)*(sp7) + (517377706142691/50000000000000 : ℝ)*(f.failure) + (729501814858547/25000000000000 : ℝ)*(f.sum) + (4785518306549/5010625000000000000000000000 : ℝ)*base65 + (20665118305366246529/8017000000000000000000000000000000 : ℝ)*base68 + (102353583954589246529/8017000000000000000000000000000000 : ℝ)*base70 + (9743110231286753471/8017000000000000000000000000000000 : ℝ)*base71 + (9363545029143/40085000000000000000000000000 : ℝ)*base74 + (38080898353599246529/8017000000000000000000000000000000 : ℝ)*base76 + (27613992976067246529/8017000000000000000000000000000000 : ℝ)*base78 + (61887752042824246529/8017000000000000000000000000000000 : ℝ)*base80 + (44551136607797/10021250000000000000000000000 : ℝ)*base82 + (22834049/5000000000000000000000 : ℝ)*base90 + (22834049/5000000000000000000000 : ℝ)*base92 + (22834049/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3254560462907789647670109249/250531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (890901663/50000000000000 : ℝ)*(base19) + (242708913/12500000000000 : ℝ)*(base23) + (6917083/2500000000000 : ℝ)*(upper3) + (9055563/12500000000000 : ℝ)*(lower4) + (6849249/2500000000000 : ℝ)*(upper5) + (252650032407189/12500000000000 : ℝ)*(major0) + (252650032407189/12500000000000 : ℝ)*(major1) + (252650032407189/12500000000000 : ℝ)*(major2) + (15813643303/100000000000000 : ℝ)*(sp1) + (4293668197/25000000000000 : ℝ)*(sp2) + (1492089642175057/50000000000000 : ℝ)*(sp4) + (1492080844451743/50000000000000 : ℝ)*(sp5) + (1492080084003011/50000000000000 : ℝ)*(sp6) + (529110400571839/50000000000000 : ℝ)*(sp7) + (529110400571839/50000000000000 : ℝ)*(f.failure) + (1492089642175057/50000000000000 : ℝ)*(f.sum) + (71980172523889/20042500000000000000000000000 : ℝ)*base66 + (654150523937490667/1002125000000000000000000000000000 : ℝ)*base67 + (3331308833937990667/1002125000000000000000000000000000 : ℝ)*base69 + (7174573830695509333/1002125000000000000000000000000000 : ℝ)*base72 + (41184296535159/20042500000000000000000000000 : ℝ)*base74 + (5468163490309615667/1002125000000000000000000000000000 : ℝ)*base75 + (1412326754046740667/1002125000000000000000000000000000 : ℝ)*base77 + (3293061855451490667/1002125000000000000000000000000000 : ℝ)*base79 + (61456375676339/20042500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (30485621/5000000000000000000000 : ℝ)*base90 + (30485621/5000000000000000000000 : ℝ)*base92 + (30485621/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1698_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8789/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9561/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1698_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1698_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1698_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1698_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1698_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5199/1024 : ℝ) ≤ p) (hpb : p ≤ (5207/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190999861/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4299/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1698_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

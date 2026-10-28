-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:11:58.651152+00:00
-- url     : https://prove2.me/submissions/27a9c10e-9b96-46f3-beee-1227ac086651

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
theorem support_rectangle_w1073_s3_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195680693/10000000000 : ℝ)*x 0 + (5436723163/10000000000 : ℝ)*x 1 + (5225130291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195680693/10000000000 : ℝ)^4133 ≤ (13326135485621/100000000000000 : ℝ)^3109 := by
    have hnat : (2195680693 : ℕ)^4133*100000000000000^3109 ≤ 13326135485621^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195680693 10000000000 13326135485621 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436723163/10000000000 : ℝ)^4133 ≤ (2780009123197/6250000000000 : ℝ)^3109 := by
    have hnat : (5436723163 : ℕ)^4133*6250000000000^3109 ≤ 2780009123197^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436723163 10000000000 2780009123197 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225130291/10000000000 : ℝ)^4133 ≤ (42193718527363/100000000000000 : ℝ)^3109 := by
    have hnat : (5225130291 : ℕ)^4133*100000000000000^3109 ≤ 42193718527363^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225130291 10000000000 42193718527363 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195680693/10000000000 : ℝ), (5436723163/10000000000 : ℝ), (5225130291/10000000000 : ℝ)] ![(13326135485621/100000000000000 : ℝ), (2780009123197/6250000000000 : ℝ), (42193718527363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195680693/10000000000 : ℝ)|^4133 ≤ (13326135485621/100000000000000 : ℝ)^3109
        have hw : |(-2195680693/10000000000 : ℝ)|=(2195680693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436723163/10000000000 : ℝ)|^4133 ≤ (2780009123197/6250000000000 : ℝ)^3109
        have hw : |(5436723163/10000000000 : ℝ)|=(5436723163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225130291/10000000000 : ℝ)|^4133 ≤ (42193718527363/100000000000000 : ℝ)^3109
        have hw : |(5225130291/10000000000 : ℝ)|=(5225130291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669438919/1250000000 : ℝ)*x 0 + (-576003549/2500000000 : ℝ)*x 1 + (2612565181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669438919/1250000000 : ℝ)^4133 ≤ (21799528674499/50000000000000 : ℝ)^3109 := by
    have hnat : (669438919 : ℕ)^4133*50000000000000^3109 ≤ 21799528674499^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669438919 1250000000 21799528674499 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576003549/2500000000 : ℝ)^4133 ≤ (14207223348619/100000000000000 : ℝ)^3109 := by
    have hnat : (576003549 : ℕ)^4133*100000000000000^3109 ≤ 14207223348619^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576003549 2500000000 14207223348619 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612565181/5000000000 : ℝ)^4133 ≤ (659276863899/1562500000000 : ℝ)^3109 := by
    have hnat : (2612565181 : ℕ)^4133*1562500000000^3109 ≤ 659276863899^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612565181 5000000000 659276863899 1562500000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669438919/1250000000 : ℝ), (-576003549/2500000000 : ℝ), (2612565181/5000000000 : ℝ)] ![(21799528674499/50000000000000 : ℝ), (14207223348619/100000000000000 : ℝ), (659276863899/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669438919/1250000000 : ℝ)|^4133 ≤ (21799528674499/50000000000000 : ℝ)^3109
        have hw : |(669438919/1250000000 : ℝ)|=(669438919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-576003549/2500000000 : ℝ)|^4133 ≤ (14207223348619/100000000000000 : ℝ)^3109
        have hw : |(-576003549/2500000000 : ℝ)|=(576003549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612565181/5000000000 : ℝ)|^4133 ≤ (659276863899/1562500000000 : ℝ)^3109
        have hw : |(2612565181/5000000000 : ℝ)|=(2612565181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214220453/400000000 : ℝ)*x 0 + (20410667/39062500 : ℝ)*x 1 + (-57600343/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214220453/400000000 : ℝ)^4133 ≤ (8719811411359/20000000000000 : ℝ)^3109 := by
    have hnat : (214220453 : ℕ)^4133*20000000000000^3109 ≤ 8719811411359^3109*400000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214220453 400000000 8719811411359 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20410667/39062500 : ℝ)^4133 ≤ (21096861738061/50000000000000 : ℝ)^3109 := by
    have hnat : (20410667 : ℕ)^4133*50000000000000^3109 ≤ 21096861738061^3109*39062500^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20410667 39062500 21096861738061 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57600343/250000000 : ℝ)^4133 ≤ (14207219446723/100000000000000 : ℝ)^3109 := by
    have hnat : (57600343 : ℕ)^4133*100000000000000^3109 ≤ 14207219446723^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57600343 250000000 14207219446723 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214220453/400000000 : ℝ), (20410667/39062500 : ℝ), (-57600343/250000000 : ℝ)] ![(8719811411359/20000000000000 : ℝ), (21096861738061/50000000000000 : ℝ), (14207219446723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214220453/400000000 : ℝ)|^4133 ≤ (8719811411359/20000000000000 : ℝ)^3109
        have hw : |(214220453/400000000 : ℝ)|=(214220453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20410667/39062500 : ℝ)|^4133 ≤ (21096861738061/50000000000000 : ℝ)^3109
        have hw : |(20410667/39062500 : ℝ)|=(20410667/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-57600343/250000000 : ℝ)|^4133 ≤ (14207219446723/100000000000000 : ℝ)^3109
        have hw : |(-57600343/250000000 : ℝ)|=(57600343/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273233681/625000000 : ℝ)*x 0 + (833816807/2000000000 : ℝ)*x 1 + (229217579/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273233681/625000000 : ℝ)^4133 ≤ (33288774264989/100000000000000 : ℝ)^3109 := by
    have hnat : (273233681 : ℕ)^4133*100000000000000^3109 ≤ 33288774264989^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273233681 625000000 33288774264989 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833816807/2000000000 : ℝ)^4133 ≤ (31253223840431/100000000000000 : ℝ)^3109 := by
    have hnat : (833816807 : ℕ)^4133*100000000000000^3109 ≤ 31253223840431^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833816807 2000000000 31253223840431 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229217579/500000000 : ℝ)^4133 ≤ (354580018813/1000000000000 : ℝ)^3109 := by
    have hnat : (229217579 : ℕ)^4133*1000000000000^3109 ≤ 354580018813^3109*500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229217579 500000000 354580018813 1000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273233681/625000000 : ℝ), (833816807/2000000000 : ℝ), (229217579/500000000 : ℝ)] ![(33288774264989/100000000000000 : ℝ), (31253223840431/100000000000000 : ℝ), (354580018813/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273233681/625000000 : ℝ)|^4133 ≤ (33288774264989/100000000000000 : ℝ)^3109
        have hw : |(273233681/625000000 : ℝ)|=(273233681/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833816807/2000000000 : ℝ)|^4133 ≤ (31253223840431/100000000000000 : ℝ)^3109
        have hw : |(833816807/2000000000 : ℝ)|=(833816807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229217579/500000000 : ℝ)|^4133 ≤ (354580018813/1000000000000 : ℝ)^3109
        have hw : |(229217579/500000000 : ℝ)|=(229217579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-548925761/2500000000 : ℝ)*x 0 + (2612996549/5000000000 : ℝ)*x 1 + (5435854937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548925761/2500000000 : ℝ)^4133 ≤ (832894738721/6250000000000 : ℝ)^3109 := by
    have hnat : (548925761 : ℕ)^4133*6250000000000^3109 ≤ 832894738721^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548925761 2500000000 832894738721 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612996549/5000000000 : ℝ)^4133 ≤ (1688119234789/4000000000000 : ℝ)^3109 := by
    have hnat : (2612996549 : ℕ)^4133*4000000000000^3109 ≤ 1688119234789^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612996549 5000000000 1688119234789 4000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435854937/10000000000 : ℝ)^4133 ≤ (44470703296363/100000000000000 : ℝ)^3109 := by
    have hnat : (5435854937 : ℕ)^4133*100000000000000^3109 ≤ 44470703296363^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435854937 10000000000 44470703296363 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548925761/2500000000 : ℝ), (2612996549/5000000000 : ℝ), (5435854937/10000000000 : ℝ)] ![(832894738721/6250000000000 : ℝ), (1688119234789/4000000000000 : ℝ), (44470703296363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548925761/2500000000 : ℝ)|^4133 ≤ (832894738721/6250000000000 : ℝ)^3109
        have hw : |(-548925761/2500000000 : ℝ)|=(548925761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612996549/5000000000 : ℝ)|^4133 ≤ (1688119234789/4000000000000 : ℝ)^3109
        have hw : |(2612996549/5000000000 : ℝ)|=(2612996549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435854937/10000000000 : ℝ)|^4133 ≤ (44470703296363/100000000000000 : ℝ)^3109
        have hw : |(5435854937/10000000000 : ℝ)|=(5435854937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302182621/10000000000 : ℝ)*x 0 + (-83731599/400000000 : ℝ)*x 1 + (1358963721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302182621/10000000000 : ℝ)^4133 ≤ (21511432344147/50000000000000 : ℝ)^3109 := by
    have hnat : (5302182621 : ℕ)^4133*50000000000000^3109 ≤ 21511432344147^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302182621 10000000000 21511432344147 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83731599/400000000 : ℝ)^4133 ≤ (12506432572931/100000000000000 : ℝ)^3109 := by
    have hnat : (83731599 : ℕ)^4133*100000000000000^3109 ≤ 12506432572931^3109*400000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83731599 400000000 12506432572931 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358963721/2500000000 : ℝ)^4133 ≤ (44470702719959/100000000000000 : ℝ)^3109 := by
    have hnat : (1358963721 : ℕ)^4133*100000000000000^3109 ≤ 44470702719959^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358963721 2500000000 44470702719959 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302182621/10000000000 : ℝ), (-83731599/400000000 : ℝ), (1358963721/2500000000 : ℝ)] ![(21511432344147/50000000000000 : ℝ), (12506432572931/100000000000000 : ℝ), (44470702719959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302182621/10000000000 : ℝ)|^4133 ≤ (21511432344147/50000000000000 : ℝ)^3109
        have hw : |(5302182621/10000000000 : ℝ)|=(5302182621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83731599/400000000 : ℝ)|^4133 ≤ (12506432572931/100000000000000 : ℝ)^3109
        have hw : |(-83731599/400000000 : ℝ)|=(83731599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358963721/2500000000 : ℝ)|^4133 ≤ (44470702719959/100000000000000 : ℝ)^3109
        have hw : |(1358963721/2500000000 : ℝ)|=(1358963721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302182867/10000000000 : ℝ)*x 0 + (1358963809/2500000000 : ℝ)*x 1 + (-2093289159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302182867/10000000000 : ℝ)^4133 ≤ (21511433670913/50000000000000 : ℝ)^3109 := by
    have hnat : (5302182867 : ℕ)^4133*50000000000000^3109 ≤ 21511433670913^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302182867 10000000000 21511433670913 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358963809/2500000000 : ℝ)^4133 ≤ (44470706548149/100000000000000 : ℝ)^3109 := by
    have hnat : (1358963809 : ℕ)^4133*100000000000000^3109 ≤ 44470706548149^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358963809 2500000000 44470706548149 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2093289159/10000000000 : ℝ)^4133 ≤ (6253213045989/50000000000000 : ℝ)^3109 := by
    have hnat : (2093289159 : ℕ)^4133*50000000000000^3109 ≤ 6253213045989^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093289159 10000000000 6253213045989 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302182867/10000000000 : ℝ), (1358963809/2500000000 : ℝ), (-2093289159/10000000000 : ℝ)] ![(21511433670913/50000000000000 : ℝ), (44470706548149/100000000000000 : ℝ), (6253213045989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302182867/10000000000 : ℝ)|^4133 ≤ (21511433670913/50000000000000 : ℝ)^3109
        have hw : |(5302182867/10000000000 : ℝ)|=(5302182867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358963809/2500000000 : ℝ)|^4133 ≤ (44470706548149/100000000000000 : ℝ)^3109
        have hw : |(1358963809/2500000000 : ℝ)|=(1358963809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2093289159/10000000000 : ℝ)|^4133 ≤ (6253213045989/50000000000000 : ℝ)^3109
        have hw : |(-2093289159/10000000000 : ℝ)|=(2093289159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s3_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546472663/1250000000 : ℝ)*x 0 + (2291329433/5000000000 : ℝ)*x 1 + (4170787227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546472663/1250000000 : ℝ)^4133 ≤ (2080575221321/6250000000000 : ℝ)^3109 := by
    have hnat : (546472663 : ℕ)^4133*6250000000000^3109 ≤ 2080575221321^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546472663 1250000000 2080575221321 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291329433/5000000000 : ℝ)^4133 ≤ (8860149579271/25000000000000 : ℝ)^3109 := by
    have hnat : (2291329433 : ℕ)^4133*25000000000000^3109 ≤ 8860149579271^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291329433 5000000000 8860149579271 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4170787227/10000000000 : ℝ)^4133 ≤ (31270198132859/100000000000000 : ℝ)^3109 := by
    have hnat : (4170787227 : ℕ)^4133*100000000000000^3109 ≤ 31270198132859^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4170787227 10000000000 31270198132859 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546472663/1250000000 : ℝ), (2291329433/5000000000 : ℝ), (4170787227/10000000000 : ℝ)] ![(2080575221321/6250000000000 : ℝ), (8860149579271/25000000000000 : ℝ), (31270198132859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546472663/1250000000 : ℝ)|^4133 ≤ (2080575221321/6250000000000 : ℝ)^3109
        have hw : |(546472663/1250000000 : ℝ)|=(546472663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2291329433/5000000000 : ℝ)|^4133 ≤ (8860149579271/25000000000000 : ℝ)^3109
        have hw : |(2291329433/5000000000 : ℝ)|=(2291329433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4170787227/10000000000 : ℝ)|^4133 ≤ (31270198132859/100000000000000 : ℝ)^3109
        have hw : |(4170787227/10000000000 : ℝ)|=(4170787227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (931/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8359/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8359/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8359/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4373/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (268218785115651/5000000000000000000 : ℝ) := by
    have hpowers : (4373/50000 : ℝ)^8265 ≤ (268218785115651/5000000000000000000 : ℝ)^2048 := by
      have hnat : (4373 : ℕ)^8265*5000000000000000000^2048 ≤ 268218785115651^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4373 50000 268218785115651 5000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4373/50000 : ℝ)) (X := (268218785115651/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8359/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (73290562153169233/100000000000000000000 : ℝ) := by
    have hpowers : (8359/50000 : ℝ)^8265 ≤ (73290562153169233/100000000000000000000 : ℝ)^2048 := by
      have hnat : (8359 : ℕ)^8265*100000000000000000000^2048 ≤ 73290562153169233^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8359 50000 73290562153169233 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8359/50000 : ℝ)) (X := (73290562153169233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500268218785115651/2500000000000000000 : ℝ) ≤ (10000265839035871/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (2500268218785115651/2500000000000000000 : ℝ)^2048 ≤ (10000265839035871/10000000000000000 : ℝ)^8265 := by
      have hnat : (2500268218785115651 : ℕ)^2048*10000000000000000^8265 ≤ 10000265839035871^8265*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500268218785115651 2500000000000000000 10000265839035871 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000265839035871/10000000000000000 : ℝ)) (X := (2500268218785115651/2500000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078654937855482253/100000000000000000000 : ℝ) ≤ (2000389685859989/2000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (100078654937855482253/100000000000000000000 : ℝ)^2048 ≤ (2000389685859989/2000000000000000 : ℝ)^8265 := by
      have hnat : (100078654937855482253 : ℕ)^2048*2000000000000000^8265 ≤ 2000389685859989^8265*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078654937855482253 100000000000000000000 2000389685859989 2000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000389685859989/2000000000000000 : ℝ)) (X := (100078654937855482253/100000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073290562153169233/50000000000000000000 : ℝ) ≤ (10003631019564019/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50073290562153169233/50000000000000000000 : ℝ)^2048 ≤ (10003631019564019/10000000000000000 : ℝ)^8265 := by
      have hnat : (50073290562153169233 : ℕ)^2048*10000000000000000^8265 ≤ 10003631019564019^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073290562153169233 50000000000000000000 10003631019564019 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003631019564019/10000000000000000 : ℝ)) (X := (50073290562153169233/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(268218785115651/5000000000000000000 : ℝ) ≤ ((19923171849973695301/19930000000000000000 : ℝ)+2*(841295132037/398600000000000 : ℝ)*(4373/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (19923171849973695301/19930000000000000000 : ℝ)+2*(841295132037/398600000000000 : ℝ)*(4373/50000 : ℝ)=(10000265839035871/10000000000000000 : ℝ) by norm_num, show 1+2*(268218785115651/5000000000000000000 : ℝ)=(2500268218785115651/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73290562153169233/100000000000000000000 : ℝ)+(268218785115651/5000000000000000000 : ℝ) ≤ ((19923171849973695301/19930000000000000000 : ℝ)+(841295132037/398600000000000 : ℝ)*((8359/50000 : ℝ)+(4373/50000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (19923171849973695301/19930000000000000000 : ℝ)+(841295132037/398600000000000 : ℝ)*((8359/50000 : ℝ)+(4373/50000 : ℝ))=(2000389685859989/2000000000000000 : ℝ) by norm_num, show 1+(73290562153169233/100000000000000000000 : ℝ)+(268218785115651/5000000000000000000 : ℝ)=(100078654937855482253/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73290562153169233/100000000000000000000 : ℝ) ≤ ((19923171849973695301/19930000000000000000 : ℝ)+2*(841295132037/398600000000000 : ℝ)*(8359/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (19923171849973695301/19930000000000000000 : ℝ)+2*(841295132037/398600000000000 : ℝ)*(8359/50000 : ℝ)=(10003631019564019/10000000000000000 : ℝ) by norm_num, show 1+2*(73290562153169233/100000000000000000000 : ℝ)=(50073290562153169233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19923171849973695301/19930000000000000000 : ℝ)*(X 1 0+X 2 0)+(841295132037/398600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (4373/50000 : ℝ)) (hi := (8359/50000 : ℝ)) (c := (19923171849973695301/19930000000000000000 : ℝ)) (alpha := (841295132037/398600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19923171849973695301/19930000000000000000 : ℝ)*(X 0 1+X 2 1)+(841295132037/398600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (4373/50000 : ℝ)) (hi := (8359/50000 : ℝ)) (c := (19923171849973695301/19930000000000000000 : ℝ)) (alpha := (841295132037/398600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19923171849973695301/19930000000000000000 : ℝ)*(X 0 2+X 1 2)+(841295132037/398600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (4373/50000 : ℝ)) (hi := (8359/50000 : ℝ)) (c := (19923171849973695301/19930000000000000000 : ℝ)) (alpha := (841295132037/398600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2195680693/10000000000 : ℝ)*X 0 0+(5436723163/10000000000 : ℝ)*X 0 1+(5225130291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669438919/1250000000 : ℝ)*X 1 0+(-576003549/2500000000 : ℝ)*X 1 1+(2612565181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214220453/400000000 : ℝ)*X 2 0+(20410667/39062500 : ℝ)*X 2 1+(-57600343/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273233681/625000000 : ℝ)*X 0 0+(833816807/2000000000 : ℝ)*X 0 1+(229217579/500000000 : ℝ)*X 0 2+(273233681/625000000 : ℝ)*X 1 0+(833816807/2000000000 : ℝ)*X 1 1+(229217579/500000000 : ℝ)*X 1 2+(273233681/625000000 : ℝ)*X 2 0+(833816807/2000000000 : ℝ)*X 2 1+(229217579/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548925761/2500000000 : ℝ)*X 0 0+(2612996549/5000000000 : ℝ)*X 0 1+(5435854937/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302182621/10000000000 : ℝ)*X 1 0+(-83731599/400000000 : ℝ)*X 1 1+(1358963721/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302182867/10000000000 : ℝ)*X 2 0+(1358963809/2500000000 : ℝ)*X 2 1+(-2093289159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546472663/1250000000 : ℝ)*X 0 0+(2291329433/5000000000 : ℝ)*X 0 1+(4170787227/10000000000 : ℝ)*X 0 2+(546472663/1250000000 : ℝ)*X 1 0+(2291329433/5000000000 : ℝ)*X 1 1+(4170787227/10000000000 : ℝ)*X 1 2+(546472663/1250000000 : ℝ)*X 2 0+(2291329433/5000000000 : ℝ)*X 2 1+(4170787227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (763459586101028195343723231/124562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212875957/12500000000000 : ℝ)*(base19) + (643658163/50000000000000 : ℝ)*(base23) + (20986343/10000000000000 : ℝ)*(lower2) + (42069901/100000000000000 : ℝ)*(upper3) + (202217231/100000000000000 : ℝ)*(upper5) + (891779743520477/25000000000000 : ℝ)*(major0) + (891779743520477/25000000000000 : ℝ)*(major1) + (891779743520477/25000000000000 : ℝ)*(major2) + (4726086757744083/100000000000000 : ℝ)*(sp0) + (2363061619808451/50000000000000 : ℝ)*(sp1) + (4726123655308231/100000000000000 : ℝ)*(sp2) + (2408099766603119/100000000000000 : ℝ)*(sp3) + (19092440237/50000000000000 : ℝ)*(sp4) + (3258657961/25000000000000 : ℝ)*(sp7) + (1204056400617481/50000000000000 : ℝ)*(f.failure) + (2363062471312279/50000000000000 : ℝ)*(f.sum) + (28243062497827/9965000000000000000000000000 : ℝ)*base66 + (601442597427871423/498250000000000000000000000000000 : ℝ)*base68 + (3690819724192121423/498250000000000000000000000000000 : ℝ)*base70 + (1272802412033371423/498250000000000000000000000000000 : ℝ)*base72 + (11438928062007/9965000000000000000000000000 : ℝ)*base74 + (1514194785284371423/498250000000000000000000000000000 : ℝ)*base76 + (2367340055465878577/498250000000000000000000000000000 : ℝ)*base77 + (3135321238648621423/498250000000000000000000000000000 : ℝ)*base80 + (33737117875811/4982500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (14312889/5000000000000000000000 : ℝ)*base90 + (14312889/5000000000000000000000 : ℝ)*base92 + (14312889/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17436456726488068562696409/2491250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (703782703/50000000000000 : ℝ)*(base19) + (265614687/12500000000000 : ℝ)*(base23) + (34076997/25000000000000 : ℝ)*(upper2) + (182909673/100000000000000 : ℝ)*(upper3) + (96888021/50000000000000 : ℝ)*(upper5) + (17982455810847/500000000000 : ℝ)*(major0) + (17982455810847/500000000000 : ℝ)*(major1) + (17982455810847/500000000000 : ℝ)*(major2) + (20608369879/100000000000000 : ℝ)*(sp1) + (4439038277/10000000000000 : ℝ)*(sp2) + (4765040530893029/100000000000000 : ℝ)*(sp4) + (953003702991549/20000000000000 : ℝ)*(sp5) + (4764994015592763/100000000000000 : ℝ)*(sp6) + (606985390035779/25000000000000 : ℝ)*(sp7) + (606985390035779/25000000000000 : ℝ)*(f.failure) + (4765040530893029/100000000000000 : ℝ)*(f.sum) + (64978369269/124562500000000000000000000 : ℝ)*base66 + (54725139466109947/9965000000000000000000000000000 : ℝ)*base67 + (116897440058354947/9965000000000000000000000000000 : ℝ)*base69 + (45317790641774947/9965000000000000000000000000000 : ℝ)*base71 + (8403658982641/1993000000000000000000000000 : ℝ)*base74 + (31273091809529947/9965000000000000000000000000000 : ℝ)*base75 + (171275931561904947/9965000000000000000000000000000 : ℝ)*base77 + (1526152174580053/9965000000000000000000000000000 : ℝ)*base80 + (450956761417/398600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (5755949/2500000000000000000000 : ℝ)*base89 + (5755949/2500000000000000000000 : ℝ)*base91 + (5755949/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (931/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_s4_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199290891/10000000000 : ℝ)*x 0 + (5405431661/10000000000 : ℝ)*x 1 + (2627031513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199290891/10000000000 : ℝ)^4133 ≤ (2671054275053/20000000000000 : ℝ)^3109 := by
    have hnat : (2199290891 : ℕ)^4133*20000000000000^3109 ≤ 2671054275053^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199290891 10000000000 2671054275053 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405431661/10000000000 : ℝ)^4133 ≤ (44140139090359/100000000000000 : ℝ)^3109 := by
    have hnat : (5405431661 : ℕ)^4133*100000000000000^3109 ≤ 44140139090359^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405431661 10000000000 44140139090359 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627031513/5000000000 : ℝ)^4133 ≤ (8500917905239/20000000000000 : ℝ)^3109 := by
    have hnat : (2627031513 : ℕ)^4133*20000000000000^3109 ≤ 8500917905239^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627031513 5000000000 8500917905239 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199290891/10000000000 : ℝ), (5405431661/10000000000 : ℝ), (2627031513/5000000000 : ℝ)] ![(2671054275053/20000000000000 : ℝ), (44140139090359/100000000000000 : ℝ), (8500917905239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199290891/10000000000 : ℝ)|^4133 ≤ (2671054275053/20000000000000 : ℝ)^3109
        have hw : |(-2199290891/10000000000 : ℝ)|=(2199290891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405431661/10000000000 : ℝ)|^4133 ≤ (44140139090359/100000000000000 : ℝ)^3109
        have hw : |(5405431661/10000000000 : ℝ)|=(5405431661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627031513/5000000000 : ℝ)|^4133 ≤ (8500917905239/20000000000000 : ℝ)^3109
        have hw : |(2627031513/5000000000 : ℝ)|=(2627031513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673876913/5000000000 : ℝ)*x 0 + (-2276274801/10000000000 : ℝ)*x 1 + (1050812591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673876913/5000000000 : ℝ)^4133 ≤ (8703024572671/20000000000000 : ℝ)^3109 := by
    have hnat : (2673876913 : ℕ)^4133*20000000000000^3109 ≤ 8703024572671^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673876913 5000000000 8703024572671 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2276274801/10000000000 : ℝ)^4133 ≤ (13980288363731/100000000000000 : ℝ)^3109 := by
    have hnat : (2276274801 : ℕ)^4133*100000000000000^3109 ≤ 13980288363731^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276274801 10000000000 13980288363731 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050812591/2000000000 : ℝ)^4133 ≤ (21252294381317/50000000000000 : ℝ)^3109 := by
    have hnat : (1050812591 : ℕ)^4133*50000000000000^3109 ≤ 21252294381317^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050812591 2000000000 21252294381317 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673876913/5000000000 : ℝ), (-2276274801/10000000000 : ℝ), (1050812591/2000000000 : ℝ)] ![(8703024572671/20000000000000 : ℝ), (13980288363731/100000000000000 : ℝ), (21252294381317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673876913/5000000000 : ℝ)|^4133 ≤ (8703024572671/20000000000000 : ℝ)^3109
        have hw : |(2673876913/5000000000 : ℝ)|=(2673876913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2276274801/10000000000 : ℝ)|^4133 ≤ (13980288363731/100000000000000 : ℝ)^3109
        have hw : |(-2276274801/10000000000 : ℝ)|=(2276274801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050812591/2000000000 : ℝ)|^4133 ≤ (21252294381317/50000000000000 : ℝ)^3109
        have hw : |(1050812591/2000000000 : ℝ)|=(1050812591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347753953/10000000000 : ℝ)*x 0 + (2627031467/5000000000 : ℝ)*x 1 + (-2276274661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347753953/10000000000 : ℝ)^4133 ≤ (8703024847427/20000000000000 : ℝ)^3109 := by
    have hnat : (5347753953 : ℕ)^4133*20000000000000^3109 ≤ 8703024847427^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347753953 10000000000 8703024847427 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627031467/5000000000 : ℝ)^4133 ≤ (5313073567099/12500000000000 : ℝ)^3109 := by
    have hnat : (2627031467 : ℕ)^4133*12500000000000^3109 ≤ 5313073567099^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627031467 5000000000 5313073567099 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276274661/10000000000 : ℝ)^4133 ≤ (3495071805171/25000000000000 : ℝ)^3109 := by
    have hnat : (2276274661 : ℕ)^4133*25000000000000^3109 ≤ 3495071805171^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276274661 10000000000 3495071805171 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347753953/10000000000 : ℝ), (2627031467/5000000000 : ℝ), (-2276274661/10000000000 : ℝ)] ![(8703024847427/20000000000000 : ℝ), (5313073567099/12500000000000 : ℝ), (3495071805171/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347753953/10000000000 : ℝ)|^4133 ≤ (8703024847427/20000000000000 : ℝ)^3109
        have hw : |(5347753953/10000000000 : ℝ)|=(5347753953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627031467/5000000000 : ℝ)|^4133 ≤ (5313073567099/12500000000000 : ℝ)^3109
        have hw : |(2627031467/5000000000 : ℝ)|=(2627031467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276274661/10000000000 : ℝ)|^4133 ≤ (3495071805171/25000000000000 : ℝ)^3109
        have hw : |(-2276274661/10000000000 : ℝ)|=(2276274661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2186943373/5000000000 : ℝ)*x 0 + (422789953/1000000000 : ℝ)*x 1 + (2262486643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186943373/5000000000 : ℝ)^4133 ≤ (1040953676871/3125000000000 : ℝ)^3109 := by
    have hnat : (2186943373 : ℕ)^4133*3125000000000^3109 ≤ 1040953676871^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186943373 5000000000 1040953676871 3125000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422789953/1000000000 : ℝ)^4133 ≤ (6368141359317/20000000000000 : ℝ)^3109 := by
    have hnat : (422789953 : ℕ)^4133*20000000000000^3109 ≤ 6368141359317^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422789953 1000000000 6368141359317 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262486643/5000000000 : ℝ)^4133 ≤ (17424387764093/50000000000000 : ℝ)^3109 := by
    have hnat : (2262486643 : ℕ)^4133*50000000000000^3109 ≤ 17424387764093^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262486643 5000000000 17424387764093 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186943373/5000000000 : ℝ), (422789953/1000000000 : ℝ), (2262486643/5000000000 : ℝ)] ![(1040953676871/3125000000000 : ℝ), (6368141359317/20000000000000 : ℝ), (17424387764093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186943373/5000000000 : ℝ)|^4133 ≤ (1040953676871/3125000000000 : ℝ)^3109
        have hw : |(2186943373/5000000000 : ℝ)|=(2186943373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422789953/1000000000 : ℝ)|^4133 ≤ (6368141359317/20000000000000 : ℝ)^3109
        have hw : |(422789953/1000000000 : ℝ)|=(422789953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262486643/5000000000 : ℝ)|^4133 ≤ (17424387764093/50000000000000 : ℝ)^3109
        have hw : |(2262486643/5000000000 : ℝ)|=(2262486643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219929917/1000000000 : ℝ)*x 0 + (2627252657/5000000000 : ℝ)*x 1 + (2702493661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219929917/1000000000 : ℝ)^4133 ≤ (13355338208561/100000000000000 : ℝ)^3109 := by
    have hnat : (219929917 : ℕ)^4133*100000000000000^3109 ≤ 13355338208561^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219929917 1000000000 13355338208561 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627252657/5000000000 : ℝ)^4133 ≤ (5313668265469/12500000000000 : ℝ)^3109 := by
    have hnat : (2627252657 : ℕ)^4133*12500000000000^3109 ≤ 5313668265469^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627252657 5000000000 5313668265469 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702493661/5000000000 : ℝ)^4133 ≤ (5516914456749/12500000000000 : ℝ)^3109 := by
    have hnat : (2702493661 : ℕ)^4133*12500000000000^3109 ≤ 5516914456749^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702493661 5000000000 5516914456749 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219929917/1000000000 : ℝ), (2627252657/5000000000 : ℝ), (2702493661/5000000000 : ℝ)] ![(13355338208561/100000000000000 : ℝ), (5313668265469/12500000000000 : ℝ), (5516914456749/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219929917/1000000000 : ℝ)|^4133 ≤ (13355338208561/100000000000000 : ℝ)^3109
        have hw : |(-219929917/1000000000 : ℝ)|=(219929917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627252657/5000000000 : ℝ)|^4133 ≤ (5313668265469/12500000000000 : ℝ)^3109
        have hw : |(2627252657/5000000000 : ℝ)|=(2627252657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702493661/5000000000 : ℝ)|^4133 ≤ (5516914456749/12500000000000 : ℝ)^3109
        have hw : |(2702493661/5000000000 : ℝ)|=(2702493661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327402073/2500000000 : ℝ)*x 0 + (-212534991/1000000000 : ℝ)*x 1 + (2702493609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327402073/2500000000 : ℝ)^4133 ≤ (43102981775489/100000000000000 : ℝ)^3109 := by
    have hnat : (1327402073 : ℕ)^4133*100000000000000^3109 ≤ 43102981775489^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327402073 2500000000 43102981775489 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212534991/1000000000 : ℝ)^4133 ≤ (12761703680079/100000000000000 : ℝ)^3109 := by
    have hnat : (212534991 : ℕ)^4133*100000000000000^3109 ≤ 12761703680079^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212534991 1000000000 12761703680079 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702493609/5000000000 : ℝ)^4133 ≤ (8827062905011/20000000000000 : ℝ)^3109 := by
    have hnat : (2702493609 : ℕ)^4133*20000000000000^3109 ≤ 8827062905011^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702493609 5000000000 8827062905011 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327402073/2500000000 : ℝ), (-212534991/1000000000 : ℝ), (2702493609/5000000000 : ℝ)] ![(43102981775489/100000000000000 : ℝ), (12761703680079/100000000000000 : ℝ), (8827062905011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327402073/2500000000 : ℝ)|^4133 ≤ (43102981775489/100000000000000 : ℝ)^3109
        have hw : |(1327402073/2500000000 : ℝ)|=(1327402073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212534991/1000000000 : ℝ)|^4133 ≤ (12761703680079/100000000000000 : ℝ)^3109
        have hw : |(-212534991/1000000000 : ℝ)|=(212534991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702493609/5000000000 : ℝ)|^4133 ≤ (8827062905011/20000000000000 : ℝ)^3109
        have hw : |(2702493609/5000000000 : ℝ)|=(2702493609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2654804071/5000000000 : ℝ)*x 0 + (2702493583/5000000000 : ℝ)*x 1 + (-2125350183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654804071/5000000000 : ℝ)^4133 ≤ (8620596031347/20000000000000 : ℝ)^3109 := by
    have hnat : (2654804071 : ℕ)^4133*20000000000000^3109 ≤ 8620596031347^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654804071 5000000000 8620596031347 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702493583/5000000000 : ℝ)^4133 ≤ (44135313960587/100000000000000 : ℝ)^3109 := by
    have hnat : (2702493583 : ℕ)^4133*100000000000000^3109 ≤ 44135313960587^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702493583 5000000000 44135313960587 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125350183/10000000000 : ℝ)^4133 ≤ (12761705859221/100000000000000 : ℝ)^3109 := by
    have hnat : (2125350183 : ℕ)^4133*100000000000000^3109 ≤ 12761705859221^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125350183 10000000000 12761705859221 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654804071/5000000000 : ℝ), (2702493583/5000000000 : ℝ), (-2125350183/10000000000 : ℝ)] ![(8620596031347/20000000000000 : ℝ), (44135313960587/100000000000000 : ℝ), (12761705859221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654804071/5000000000 : ℝ)|^4133 ≤ (8620596031347/20000000000000 : ℝ)^3109
        have hw : |(2654804071/5000000000 : ℝ)|=(2654804071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702493583/5000000000 : ℝ)|^4133 ≤ (44135313960587/100000000000000 : ℝ)^3109
        have hw : |(2702493583/5000000000 : ℝ)|=(2702493583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2125350183/10000000000 : ℝ)|^4133 ≤ (12761705859221/100000000000000 : ℝ)^3109
        have hw : |(-2125350183/10000000000 : ℝ)|=(2125350183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s4_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4373902467/10000000000 : ℝ)*x 0 + (2262052491/5000000000 : ℝ)*x 1 + (2114385759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373902467/10000000000 : ℝ)^4133 ≤ (33310676821713/100000000000000 : ℝ)^3109 := by
    have hnat : (4373902467 : ℕ)^4133*100000000000000^3109 ≤ 33310676821713^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373902467 10000000000 33310676821713 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262052491/5000000000 : ℝ)^4133 ≤ (17419943045523/50000000000000 : ℝ)^3109 := by
    have hnat : (2262052491 : ℕ)^4133*50000000000000^3109 ≤ 17419943045523^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262052491 5000000000 17419943045523 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114385759/5000000000 : ℝ)^4133 ≤ (31849437072767/100000000000000 : ℝ)^3109 := by
    have hnat : (2114385759 : ℕ)^4133*100000000000000^3109 ≤ 31849437072767^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114385759 5000000000 31849437072767 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373902467/10000000000 : ℝ), (2262052491/5000000000 : ℝ), (2114385759/5000000000 : ℝ)] ![(33310676821713/100000000000000 : ℝ), (17419943045523/50000000000000 : ℝ), (31849437072767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373902467/10000000000 : ℝ)|^4133 ≤ (33310676821713/100000000000000 : ℝ)^3109
        have hw : |(4373902467/10000000000 : ℝ)|=(4373902467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262052491/5000000000 : ℝ)|^4133 ≤ (17419943045523/50000000000000 : ℝ)^3109
        have hw : |(2262052491/5000000000 : ℝ)|=(2262052491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114385759/5000000000 : ℝ)|^4133 ≤ (31849437072767/100000000000000 : ℝ)^3109
        have hw : |(2114385759/5000000000 : ℝ)|=(2114385759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (931/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11037/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (931/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (931/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (931/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (931/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (931/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (931/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10419/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (2717909741954733/25000000000000000000 : ℝ) := by
    have hpowers : (10419/100000 : ℝ)^8265 ≤ (2717909741954733/25000000000000000000 : ℝ)^2048 := by
      have hnat : (10419 : ℕ)^8265*25000000000000000000^2048 ≤ 2717909741954733^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10419 100000 2717909741954733 25000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10419/100000 : ℝ)) (X := (2717909741954733/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (931/6250 : ℝ) ^ (8265/2048 : ℝ) ≤ (11501199028903211/25000000000000000000 : ℝ) := by
    have hpowers : (931/6250 : ℝ)^8265 ≤ (11501199028903211/25000000000000000000 : ℝ)^2048 := by
      have hnat : (931 : ℕ)^8265*25000000000000000000^2048 ≤ 11501199028903211^2048*6250^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        931 6250 11501199028903211 25000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (931/6250 : ℝ)) (X := (11501199028903211/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502717909741954733/12500000000000000000 : ℝ) ≤ (2000107747349329/2000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (12502717909741954733/12500000000000000000 : ℝ)^2048 ≤ (2000107747349329/2000000000000000 : ℝ)^8265 := by
      have hnat : (12502717909741954733 : ℕ)^2048*2000000000000000^8265 ≤ 2000107747349329^8265*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502717909741954733 12500000000000000000 2000107747349329 2000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107747349329/2000000000000000 : ℝ)) (X := (12502717909741954733/12500000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126777388596357243/3125000000000000000 : ℝ) ≤ (10001409050573823/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (3126777388596357243/3125000000000000000 : ℝ)^2048 ≤ (10001409050573823/10000000000000000 : ℝ)^8265 := by
      have hnat : (3126777388596357243 : ℕ)^2048*10000000000000000^8265 ≤ 10001409050573823^8265*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126777388596357243 3125000000000000000 10001409050573823 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001409050573823/10000000000000000 : ℝ)) (X := (3126777388596357243/3125000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12511501199028903211/12500000000000000000 : ℝ) ≤ (10002279364401001/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (12511501199028903211/12500000000000000000 : ℝ)^2048 ≤ (10002279364401001/10000000000000000 : ℝ)^8265 := by
      have hnat : (12511501199028903211 : ℕ)^2048*10000000000000000^8265 ≤ 10002279364401001^8265*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12511501199028903211 12500000000000000000 10002279364401001 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002279364401001/10000000000000000 : ℝ)) (X := (12511501199028903211/12500000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2717909741954733/25000000000000000000 : ℝ) ≤ ((44754276324883994501/44770000000000000000 : ℝ)+2*(435156913589/223850000000000 : ℝ)*(10419/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (44754276324883994501/44770000000000000000 : ℝ)+2*(435156913589/223850000000000 : ℝ)*(10419/100000 : ℝ)=(2000107747349329/2000000000000000 : ℝ) by norm_num, show 1+2*(2717909741954733/25000000000000000000 : ℝ)=(12502717909741954733/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11501199028903211/25000000000000000000 : ℝ)+(2717909741954733/25000000000000000000 : ℝ) ≤ ((44754276324883994501/44770000000000000000 : ℝ)+(435156913589/223850000000000 : ℝ)*((931/6250 : ℝ)+(10419/100000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (44754276324883994501/44770000000000000000 : ℝ)+(435156913589/223850000000000 : ℝ)*((931/6250 : ℝ)+(10419/100000 : ℝ))=(10001409050573823/10000000000000000 : ℝ) by norm_num, show 1+(11501199028903211/25000000000000000000 : ℝ)+(2717909741954733/25000000000000000000 : ℝ)=(3126777388596357243/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11501199028903211/25000000000000000000 : ℝ) ≤ ((44754276324883994501/44770000000000000000 : ℝ)+2*(435156913589/223850000000000 : ℝ)*(931/6250 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (44754276324883994501/44770000000000000000 : ℝ)+2*(435156913589/223850000000000 : ℝ)*(931/6250 : ℝ)=(10002279364401001/10000000000000000 : ℝ) by norm_num, show 1+2*(11501199028903211/25000000000000000000 : ℝ)=(12511501199028903211/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44754276324883994501/44770000000000000000 : ℝ)*(X 1 0+X 2 0)+(435156913589/223850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (10419/100000 : ℝ)) (hi := (931/6250 : ℝ)) (c := (44754276324883994501/44770000000000000000 : ℝ)) (alpha := (435156913589/223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44754276324883994501/44770000000000000000 : ℝ)*(X 0 1+X 2 1)+(435156913589/223850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (10419/100000 : ℝ)) (hi := (931/6250 : ℝ)) (c := (44754276324883994501/44770000000000000000 : ℝ)) (alpha := (435156913589/223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44754276324883994501/44770000000000000000 : ℝ)*(X 0 2+X 1 2)+(435156913589/223850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (10419/100000 : ℝ)) (hi := (931/6250 : ℝ)) (c := (44754276324883994501/44770000000000000000 : ℝ)) (alpha := (435156913589/223850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2199290891/10000000000 : ℝ)*X 0 0+(5405431661/10000000000 : ℝ)*X 0 1+(2627031513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673876913/5000000000 : ℝ)*X 1 0+(-2276274801/10000000000 : ℝ)*X 1 1+(1050812591/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347753953/10000000000 : ℝ)*X 2 0+(2627031467/5000000000 : ℝ)*X 2 1+(-2276274661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186943373/5000000000 : ℝ)*X 0 0+(422789953/1000000000 : ℝ)*X 0 1+(2262486643/5000000000 : ℝ)*X 0 2+(2186943373/5000000000 : ℝ)*X 1 0+(422789953/1000000000 : ℝ)*X 1 1+(2262486643/5000000000 : ℝ)*X 1 2+(2186943373/5000000000 : ℝ)*X 2 0+(422789953/1000000000 : ℝ)*X 2 1+(2262486643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219929917/1000000000 : ℝ)*X 0 0+(2627252657/5000000000 : ℝ)*X 0 1+(2702493661/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327402073/2500000000 : ℝ)*X 1 0+(-212534991/1000000000 : ℝ)*X 1 1+(2702493609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654804071/5000000000 : ℝ)*X 2 0+(2702493583/5000000000 : ℝ)*X 2 1+(-2125350183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373902467/10000000000 : ℝ)*X 0 0+(2262052491/5000000000 : ℝ)*X 0 1+(2114385759/5000000000 : ℝ)*X 0 2+(4373902467/10000000000 : ℝ)*X 1 0+(2262052491/5000000000 : ℝ)*X 1 1+(2114385759/5000000000 : ℝ)*X 1 2+(4373902467/10000000000 : ℝ)*X 2 0+(2262052491/5000000000 : ℝ)*X 2 1+(2114385759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (304382878391949332444829171/50875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (469562463/50000000000000 : ℝ)*(base19) + (627375489/100000000000000 : ℝ)*(base23) + (250617461/100000000000000 : ℝ)*(lower2) + (34906563/25000000000000 : ℝ)*(upper3) + (2725313/50000000000000 : ℝ)*(upper5) + (2493151277047127/50000000000000 : ℝ)*(major0) + (2493151277047127/50000000000000 : ℝ)*(major1) + (2493151277047127/50000000000000 : ℝ)*(major2) + (1651600920482213/25000000000000 : ℝ)*(sp0) + (3303209957525759/50000000000000 : ℝ)*(sp1) + (1321284045360191/20000000000000 : ℝ)*(sp2) + (3366173086602519/100000000000000 : ℝ)*(sp3) + (17172247593/100000000000000 : ℝ)*(sp4) + (10967977671/100000000000000 : ℝ)*(sp7) + (336618405458019/10000000000000 : ℝ)*(f.failure) + (1651605213544111/25000000000000 : ℝ)*(f.sum) + (63907789519553/22385000000000000000000000000 : ℝ)*base66 + (52508169744244551373/2238500000000000000000000000000000 : ℝ)*base68 + (7725765642688551373/2238500000000000000000000000000000 : ℝ)*base70 + (52154195813115051373/2238500000000000000000000000000000 : ℝ)*base72 + (85605507098139/11192500000000000000000000000 : ℝ)*base74 + (11134775221619448627/2238500000000000000000000000000000 : ℝ)*base75 + (59482635720524551373/2238500000000000000000000000000000 : ℝ)*base78 + (8116273874890551373/2238500000000000000000000000000000 : ℝ)*base80 + (74343354589767/22385000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (17253389/1000000000000000000000 : ℝ)*base89 + (17253389/1000000000000000000000 : ℝ)*base91 + (17253389/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (398346465536138017195501371/101750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8174353/400000000000 : ℝ)*(base19) + (1871755373/100000000000000 : ℝ)*(base23) + (76022761/100000000000000 : ℝ)*(upper3) + (58148377/100000000000000 : ℝ)*(lower4) + (35404387/25000000000000 : ℝ)*(upper5) + (5015655873253527/100000000000000 : ℝ)*(major0) + (5015655873253527/100000000000000 : ℝ)*(major1) + (5015655873253527/100000000000000 : ℝ)*(major2) + (52602371269/100000000000000 : ℝ)*(sp1) + (9892914331/25000000000000 : ℝ)*(sp2) + (6645311540673363/100000000000000 : ℝ)*(sp4) + (6645256894713843/100000000000000 : ℝ)*(sp5) + (3322635048630333/50000000000000 : ℝ)*(sp6) + (3386000075335251/100000000000000 : ℝ)*(sp7) + (3386000075335251/100000000000000 : ℝ)*(f.failure) + (6645311540673363/100000000000000 : ℝ)*(f.sum) + (38203162932611/22385000000000000000000000000 : ℝ)*base65 + (4901230829800544973/4477000000000000000000000000000000 : ℝ)*base68 + (49574140100680544973/4477000000000000000000000000000000 : ℝ)*base70 + (4107477098931544973/4477000000000000000000000000000000 : ℝ)*base72 + (62271201664149/22385000000000000000000000000 : ℝ)*base74 + (42562239344171544973/4477000000000000000000000000000000 : ℝ)*base76 + (62510537513069544973/4477000000000000000000000000000000 : ℝ)*base78 + (33408949789569455027/4477000000000000000000000000000000 : ℝ)*base79 + (63030734812977/11192500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (97821981/10000000000000000000000 : ℝ)*base89 + (97821981/10000000000000000000000 : ℝ)*base91 + (97821981/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1073_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (931/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_s5_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200100781/10000000000 : ℝ)*x 0 + (5396798351/10000000000 : ℝ)*x 1 + (2631082579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200100781/10000000000 : ℝ)^4133 ≤ (6680904854589/50000000000000 : ℝ)^3109 := by
    have hnat : (2200100781 : ℕ)^4133*50000000000000^3109 ≤ 6680904854589^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200100781 10000000000 6680904854589 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396798351/10000000000 : ℝ)^4133 ≤ (440464452481/1000000000000 : ℝ)^3109 := by
    have hnat : (5396798351 : ℕ)^4133*1000000000000^3109 ≤ 440464452481^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396798351 10000000000 440464452481 1000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631082579/5000000000 : ℝ)^4133 ≤ (1064793625583/2500000000000 : ℝ)^3109 := by
    have hnat : (2631082579 : ℕ)^4133*2500000000000^3109 ≤ 1064793625583^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631082579 5000000000 1064793625583 2500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200100781/10000000000 : ℝ), (5396798351/10000000000 : ℝ), (2631082579/5000000000 : ℝ)] ![(6680904854589/50000000000000 : ℝ), (440464452481/1000000000000 : ℝ), (1064793625583/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200100781/10000000000 : ℝ)|^4133 ≤ (6680904854589/50000000000000 : ℝ)^3109
        have hw : |(-2200100781/10000000000 : ℝ)|=(2200100781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396798351/10000000000 : ℝ)|^4133 ≤ (440464452481/1000000000000 : ℝ)^3109
        have hw : |(5396798351/10000000000 : ℝ)|=(5396798351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631082579/5000000000 : ℝ)|^4133 ≤ (1064793625583/2500000000000 : ℝ)^3109
        have hw : |(2631082579/5000000000 : ℝ)|=(2631082579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345602239/10000000000 : ℝ)*x 0 + (-2268444721/10000000000 : ℝ)*x 1 + (5262166057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345602239/10000000000 : ℝ)^4133 ≤ (8698370066413/20000000000000 : ℝ)^3109 := by
    have hnat : (5345602239 : ℕ)^4133*20000000000000^3109 ≤ 8698370066413^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345602239 10000000000 8698370066413 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268444721/10000000000 : ℝ)^4133 ≤ (13916394957807/100000000000000 : ℝ)^3109 := by
    have hnat : (2268444721 : ℕ)^4133*100000000000000^3109 ≤ 13916394957807^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268444721 10000000000 13916394957807 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262166057/10000000000 : ℝ)^4133 ≤ (42591754696413/100000000000000 : ℝ)^3109 := by
    have hnat : (5262166057 : ℕ)^4133*100000000000000^3109 ≤ 42591754696413^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262166057 10000000000 42591754696413 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345602239/10000000000 : ℝ), (-2268444721/10000000000 : ℝ), (5262166057/10000000000 : ℝ)] ![(8698370066413/20000000000000 : ℝ), (13916394957807/100000000000000 : ℝ), (42591754696413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345602239/10000000000 : ℝ)|^4133 ≤ (8698370066413/20000000000000 : ℝ)^3109
        have hw : |(5345602239/10000000000 : ℝ)|=(5345602239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2268444721/10000000000 : ℝ)|^4133 ≤ (13916394957807/100000000000000 : ℝ)^3109
        have hw : |(-2268444721/10000000000 : ℝ)|=(2268444721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262166057/10000000000 : ℝ)|^4133 ≤ (42591754696413/100000000000000 : ℝ)^3109
        have hw : |(5262166057/10000000000 : ℝ)|=(5262166057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345602183/10000000000 : ℝ)*x 0 + (164442667/312500000 : ℝ)*x 1 + (-283555717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345602183/10000000000 : ℝ)^4133 ≤ (2718240607899/6250000000000 : ℝ)^3109 := by
    have hnat : (5345602183 : ℕ)^4133*6250000000000^3109 ≤ 2718240607899^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345602183 10000000000 2718240607899 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164442667/312500000 : ℝ)^4133 ≤ (42591747024649/100000000000000 : ℝ)^3109 := by
    have hnat : (164442667 : ℕ)^4133*100000000000000^3109 ≤ 42591747024649^3109*312500000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164442667 312500000 42591747024649 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283555717/1250000000 : ℝ)^4133 ≤ (13916403235499/100000000000000 : ℝ)^3109 := by
    have hnat : (283555717 : ℕ)^4133*100000000000000^3109 ≤ 13916403235499^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283555717 1250000000 13916403235499 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345602183/10000000000 : ℝ), (164442667/312500000 : ℝ), (-283555717/1250000000 : ℝ)] ![(2718240607899/6250000000000 : ℝ), (42591747024649/100000000000000 : ℝ), (13916403235499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345602183/10000000000 : ℝ)|^4133 ≤ (2718240607899/6250000000000 : ℝ)^3109
        have hw : |(5345602183/10000000000 : ℝ)|=(5345602183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164442667/312500000 : ℝ)|^4133 ≤ (42591747024649/100000000000000 : ℝ)^3109
        have hw : |(164442667/312500000 : ℝ)|=(164442667/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283555717/1250000000 : ℝ)|^4133 ≤ (13916403235499/100000000000000 : ℝ)^3109
        have hw : |(-283555717/1250000000 : ℝ)|=(283555717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4374357217/10000000000 : ℝ)*x 0 + (42442601/100000000 : ℝ)*x 1 + (2254244623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374357217/10000000000 : ℝ)^4133 ≤ (520551263481/1562500000000 : ℝ)^3109 := by
    have hnat : (4374357217 : ℕ)^4133*1562500000000^3109 ≤ 520551263481^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374357217 10000000000 520551263481 1562500000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42442601/100000000 : ℝ)^4133 ≤ (6400921256423/20000000000000 : ℝ)^3109 := by
    have hnat : (42442601 : ℕ)^4133*20000000000000^3109 ≤ 6400921256423^3109*100000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42442601 100000000 6400921256423 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254244623/5000000000 : ℝ)^4133 ≤ (3468011284251/10000000000000 : ℝ)^3109 := by
    have hnat : (2254244623 : ℕ)^4133*10000000000000^3109 ≤ 3468011284251^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254244623 5000000000 3468011284251 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374357217/10000000000 : ℝ), (42442601/100000000 : ℝ), (2254244623/5000000000 : ℝ)] ![(520551263481/1562500000000 : ℝ), (6400921256423/20000000000000 : ℝ), (3468011284251/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374357217/10000000000 : ℝ)|^4133 ≤ (520551263481/1562500000000 : ℝ)^3109
        have hw : |(4374357217/10000000000 : ℝ)|=(4374357217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42442601/100000000 : ℝ)|^4133 ≤ (6400921256423/20000000000000 : ℝ)^3109
        have hw : |(42442601/100000000 : ℝ)|=(42442601/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254244623/5000000000 : ℝ)|^4133 ≤ (3468011284251/10000000000000 : ℝ)^3109
        have hw : |(2254244623/5000000000 : ℝ)|=(2254244623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-440021263/2000000000 : ℝ)*x 0 + (5262515501/10000000000 : ℝ)*x 1 + (2698223393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (440021263/2000000000 : ℝ)^4133 ≤ (3340463597129/25000000000000 : ℝ)^3109 := by
    have hnat : (440021263 : ℕ)^4133*25000000000000^3109 ≤ 3340463597129^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440021263 2000000000 3340463597129 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262515501/10000000000 : ℝ)^4133 ≤ (665554917153/1562500000000 : ℝ)^3109 := by
    have hnat : (5262515501 : ℕ)^4133*1562500000000^3109 ≤ 665554917153^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262515501 10000000000 665554917153 1562500000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698223393/5000000000 : ℝ)^4133 ≤ (44042630899953/100000000000000 : ℝ)^3109 := by
    have hnat : (2698223393 : ℕ)^4133*100000000000000^3109 ≤ 44042630899953^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698223393 5000000000 44042630899953 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-440021263/2000000000 : ℝ), (5262515501/10000000000 : ℝ), (2698223393/5000000000 : ℝ)] ![(3340463597129/25000000000000 : ℝ), (665554917153/1562500000000 : ℝ), (44042630899953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-440021263/2000000000 : ℝ)|^4133 ≤ (3340463597129/25000000000000 : ℝ)^3109
        have hw : |(-440021263/2000000000 : ℝ)|=(440021263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262515501/10000000000 : ℝ)|^4133 ≤ (665554917153/1562500000000 : ℝ)^3109
        have hw : |(5262515501/10000000000 : ℝ)|=(5262515501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698223393/5000000000 : ℝ)|^4133 ≤ (44042630899953/100000000000000 : ℝ)^3109
        have hw : |(2698223393/5000000000 : ℝ)|=(2698223393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132791823/250000000 : ℝ)*x 0 + (-533540937/2500000000 : ℝ)*x 1 + (269822337/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132791823/250000000 : ℝ)^4133 ≤ (8625052806051/20000000000000 : ℝ)^3109 := by
    have hnat : (132791823 : ℕ)^4133*20000000000000^3109 ≤ 8625052806051^3109*250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132791823 250000000 8625052806051 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533540937/2500000000 : ℝ)^4133 ≤ (12832105548447/100000000000000 : ℝ)^3109 := by
    have hnat : (533540937 : ℕ)^4133*100000000000000^3109 ≤ 12832105548447^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533540937 2500000000 12832105548447 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269822337/500000000 : ℝ)^4133 ≤ (352341043207/800000000000 : ℝ)^3109 := by
    have hnat : (269822337 : ℕ)^4133*800000000000^3109 ≤ 352341043207^3109*500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269822337 500000000 352341043207 800000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132791823/250000000 : ℝ), (-533540937/2500000000 : ℝ), (269822337/500000000 : ℝ)] ![(8625052806051/20000000000000 : ℝ), (12832105548447/100000000000000 : ℝ), (352341043207/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132791823/250000000 : ℝ)|^4133 ≤ (8625052806051/20000000000000 : ℝ)^3109
        have hw : |(132791823/250000000 : ℝ)|=(132791823/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533540937/2500000000 : ℝ)|^4133 ≤ (12832105548447/100000000000000 : ℝ)^3109
        have hw : |(-533540937/2500000000 : ℝ)|=(533540937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269822337/500000000 : ℝ)|^4133 ≤ (352341043207/800000000000 : ℝ)^3109
        have hw : |(269822337/500000000 : ℝ)|=(269822337/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531167289/1000000000 : ℝ)*x 0 + (5396446787/10000000000 : ℝ)*x 1 + (-1067081863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531167289/1000000000 : ℝ)^4133 ≤ (43125263706463/100000000000000 : ℝ)^3109 := by
    have hnat : (531167289 : ℕ)^4133*100000000000000^3109 ≤ 43125263706463^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531167289 1000000000 43125263706463 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396446787/10000000000 : ℝ)^4133 ≤ (22021315455401/50000000000000 : ℝ)^3109 := by
    have hnat : (5396446787 : ℕ)^4133*50000000000000^3109 ≤ 22021315455401^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396446787 10000000000 22021315455401 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067081863/5000000000 : ℝ)^4133 ≤ (12832105372599/100000000000000 : ℝ)^3109 := by
    have hnat : (1067081863 : ℕ)^4133*100000000000000^3109 ≤ 12832105372599^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067081863 5000000000 12832105372599 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531167289/1000000000 : ℝ), (5396446787/10000000000 : ℝ), (-1067081863/5000000000 : ℝ)] ![(43125263706463/100000000000000 : ℝ), (22021315455401/50000000000000 : ℝ), (12832105372599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531167289/1000000000 : ℝ)|^4133 ≤ (43125263706463/100000000000000 : ℝ)^3109
        have hw : |(531167289/1000000000 : ℝ)|=(531167289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396446787/10000000000 : ℝ)|^4133 ≤ (22021315455401/50000000000000 : ℝ)^3109
        have hw : |(5396446787/10000000000 : ℝ)|=(5396446787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067081863/5000000000 : ℝ)|^4133 ≤ (12832105372599/100000000000000 : ℝ)^3109
        have hw : |(-1067081863/5000000000 : ℝ)|=(1067081863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s5_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (437436817/1000000000 : ℝ)*x 0 + (4507801801/10000000000 : ℝ)*x 1 + (2122475129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437436817/1000000000 : ℝ)^4133 ≤ (33315391756563/100000000000000 : ℝ)^3109 := by
    have hnat : (437436817 : ℕ)^4133*100000000000000^3109 ≤ 33315391756563^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437436817 1000000000 33315391756563 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507801801/10000000000 : ℝ)^4133 ≤ (2167067712181/6250000000000 : ℝ)^3109 := by
    have hnat : (4507801801 : ℕ)^4133*6250000000000^3109 ≤ 2167067712181^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507801801 10000000000 2167067712181 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122475129/5000000000 : ℝ)^4133 ≤ (32011524836151/100000000000000 : ℝ)^3109 := by
    have hnat : (2122475129 : ℕ)^4133*100000000000000^3109 ≤ 32011524836151^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122475129 5000000000 32011524836151 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437436817/1000000000 : ℝ), (4507801801/10000000000 : ℝ), (2122475129/5000000000 : ℝ)] ![(33315391756563/100000000000000 : ℝ), (2167067712181/6250000000000 : ℝ), (32011524836151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437436817/1000000000 : ℝ)|^4133 ≤ (33315391756563/100000000000000 : ℝ)^3109
        have hw : |(437436817/1000000000 : ℝ)|=(437436817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507801801/10000000000 : ℝ)|^4133 ≤ (2167067712181/6250000000000 : ℝ)^3109
        have hw : |(4507801801/10000000000 : ℝ)|=(4507801801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2122475129/5000000000 : ℝ)|^4133 ≤ (32011524836151/100000000000000 : ℝ)^3109
        have hw : |(2122475129/5000000000 : ℝ)|=(2122475129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1121/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11037/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11037/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11037/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11037/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (1371788141572383/10000000000000000000 : ℝ) := by
    have hpowers : (11037/100000 : ℝ)^8265 ≤ (1371788141572383/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11037 : ℕ)^8265*10000000000000000000^2048 ≤ 1371788141572383^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11037 100000 1371788141572383 10000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11037/100000 : ℝ)) (X := (1371788141572383/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7121/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (38380741434800803/100000000000000000000 : ℝ) := by
    have hpowers : (7121/50000 : ℝ)^8265 ≤ (38380741434800803/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7121 : ℕ)^8265*100000000000000000000^2048 ≤ 38380741434800803^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 50000 38380741434800803 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/50000 : ℝ)) (X := (38380741434800803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001371788141572383/5000000000000000000 : ℝ) ≤ (10000679765823231/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (5001371788141572383/5000000000000000000 : ℝ)^2048 ≤ (10000679765823231/10000000000000000 : ℝ)^8265 := by
      have hnat : (5001371788141572383 : ℕ)^2048*10000000000000000^8265 ≤ 10000679765823231^8265*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001371788141572383 5000000000000000000 10000679765823231 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679765823231/10000000000000000 : ℝ)) (X := (5001371788141572383/5000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052098622850524633/100000000000000000000 : ℝ) ≤ (10001290708760053/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (100052098622850524633/100000000000000000000 : ℝ)^2048 ≤ (10001290708760053/10000000000000000 : ℝ)^8265 := by
      have hnat : (100052098622850524633 : ℕ)^2048*10000000000000000^8265 ≤ 10001290708760053^8265*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052098622850524633 100000000000000000000 10001290708760053 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290708760053/10000000000000000 : ℝ)) (X := (100052098622850524633/100000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038380741434800803/50000000000000000000 : ℝ) ≤ (3200608528543/3200000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50038380741434800803/50000000000000000000 : ℝ)^2048 ≤ (3200608528543/3200000000000 : ℝ)^8265 := by
      have hnat : (50038380741434800803 : ℕ)^2048*3200000000000^8265 ≤ 3200608528543^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038380741434800803 50000000000000000000 3200608528543 3200000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3200608528543/3200000000000 : ℝ)) (X := (50038380741434800803/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1371788141572383/10000000000000000000 : ℝ) ≤ ((32038692695076046527/32050000000000000000 : ℝ)+2*(305471468411/160250000000000 : ℝ)*(11037/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (32038692695076046527/32050000000000000000 : ℝ)+2*(305471468411/160250000000000 : ℝ)*(11037/100000 : ℝ)=(10000679765823231/10000000000000000 : ℝ) by norm_num, show 1+2*(1371788141572383/10000000000000000000 : ℝ)=(5001371788141572383/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38380741434800803/100000000000000000000 : ℝ)+(1371788141572383/10000000000000000000 : ℝ) ≤ ((32038692695076046527/32050000000000000000 : ℝ)+(305471468411/160250000000000 : ℝ)*((7121/50000 : ℝ)+(11037/100000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (32038692695076046527/32050000000000000000 : ℝ)+(305471468411/160250000000000 : ℝ)*((7121/50000 : ℝ)+(11037/100000 : ℝ))=(10001290708760053/10000000000000000 : ℝ) by norm_num, show 1+(38380741434800803/100000000000000000000 : ℝ)+(1371788141572383/10000000000000000000 : ℝ)=(100052098622850524633/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38380741434800803/100000000000000000000 : ℝ) ≤ ((32038692695076046527/32050000000000000000 : ℝ)+2*(305471468411/160250000000000 : ℝ)*(7121/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (32038692695076046527/32050000000000000000 : ℝ)+2*(305471468411/160250000000000 : ℝ)*(7121/50000 : ℝ)=(3200608528543/3200000000000 : ℝ) by norm_num, show 1+2*(38380741434800803/100000000000000000000 : ℝ)=(50038380741434800803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32038692695076046527/32050000000000000000 : ℝ)*(X 1 0+X 2 0)+(305471468411/160250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (32038692695076046527/32050000000000000000 : ℝ)) (alpha := (305471468411/160250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32038692695076046527/32050000000000000000 : ℝ)*(X 0 1+X 2 1)+(305471468411/160250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (32038692695076046527/32050000000000000000 : ℝ)) (alpha := (305471468411/160250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32038692695076046527/32050000000000000000 : ℝ)*(X 0 2+X 1 2)+(305471468411/160250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11037/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (32038692695076046527/32050000000000000000 : ℝ)) (alpha := (305471468411/160250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2200100781/10000000000 : ℝ)*X 0 0+(5396798351/10000000000 : ℝ)*X 0 1+(2631082579/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345602239/10000000000 : ℝ)*X 1 0+(-2268444721/10000000000 : ℝ)*X 1 1+(5262166057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345602183/10000000000 : ℝ)*X 2 0+(164442667/312500000 : ℝ)*X 2 1+(-283555717/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374357217/10000000000 : ℝ)*X 0 0+(42442601/100000000 : ℝ)*X 0 1+(2254244623/5000000000 : ℝ)*X 0 2+(4374357217/10000000000 : ℝ)*X 1 0+(42442601/100000000 : ℝ)*X 1 1+(2254244623/5000000000 : ℝ)*X 1 2+(4374357217/10000000000 : ℝ)*X 2 0+(42442601/100000000 : ℝ)*X 2 1+(2254244623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-440021263/2000000000 : ℝ)*X 0 0+(5262515501/10000000000 : ℝ)*X 0 1+(2698223393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132791823/250000000 : ℝ)*X 1 0+(-533540937/2500000000 : ℝ)*X 1 1+(269822337/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531167289/1000000000 : ℝ)*X 2 0+(5396446787/10000000000 : ℝ)*X 2 1+(-1067081863/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437436817/1000000000 : ℝ)*X 0 0+(4507801801/10000000000 : ℝ)*X 0 1+(2122475129/5000000000 : ℝ)*X 0 2+(437436817/1000000000 : ℝ)*X 1 0+(4507801801/10000000000 : ℝ)*X 1 1+(2122475129/5000000000 : ℝ)*X 1 2+(437436817/1000000000 : ℝ)*X 2 0+(4507801801/10000000000 : ℝ)*X 2 1+(2122475129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7253085433196560902482990739/1602500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (626617/6250000000000 : ℝ)*(base21) + (1601567/2000000000000 : ℝ)*(upper2) + (62169521/20000000000000 : ℝ)*(upper3) + (44188377/50000000000000 : ℝ)*(lower4) + (5606148892572719/100000000000000 : ℝ)*(major0) + (5606148892572719/100000000000000 : ℝ)*(major1) + (5606148892572719/100000000000000 : ℝ)*(major2) + (7427637290642687/100000000000000 : ℝ)*(sp0) + (7427663869064659/100000000000000 : ℝ)*(sp1) + (7427625094121909/100000000000000 : ℝ)*(sp2) + (946153060117219/25000000000000 : ℝ)*(sp3) + (6644605493/25000000000000 : ℝ)*(sp4) + (19382458439/50000000000000 : ℝ)*(sp6) + (4304948333/20000000000000 : ℝ)*(sp7) + (189231688260527/5000000000000 : ℝ)*(f.failure) + (7427663869064659/100000000000000 : ℝ)*(f.sum) + (1987841759883643/16025000000000000000000000000 : ℝ)*base65 + (5019144181393303087/3205000000000000000000000000000000 : ℝ)*base68 + (40061028443543303087/3205000000000000000000000000000000 : ℝ)*base70 + (177043222811461696913/3205000000000000000000000000000000 : ℝ)*base71 + (12948977383783/4006250000000000000000000000 : ℝ)*base74 + (27939712113668303087/3205000000000000000000000000000000 : ℝ)*base76 + (57790322393931696913/3205000000000000000000000000000000 : ℝ)*base77 + (10003866492858303087/3205000000000000000000000000000000 : ℝ)*base80 + (28059104076333/4006250000000000000000000000 : ℝ)*base82 + (2835263/500000000000000000000 : ℝ)*base90 + (2835263/500000000000000000000 : ℝ)*base92 + (2835263/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1044627793644620051153263233/200312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20359323/2000000000000 : ℝ)*(base19) + (1093420069/100000000000000 : ℝ)*(base23) + (105304003/100000000000000 : ℝ)*(upper3) + (48233731/100000000000000 : ℝ)*(lower4) + (43485977/50000000000000 : ℝ)*(upper5) + (704433865679569/12500000000000 : ℝ)*(major0) + (704433865679569/12500000000000 : ℝ)*(major1) + (704433865679569/12500000000000 : ℝ)*(major2) + (24499143727/100000000000000 : ℝ)*(sp1) + (28697439769/100000000000000 : ℝ)*(sp2) + (7466513012020847/100000000000000 : ℝ)*(sp4) + (746648749491097/10000000000000 : ℝ)*(sp5) + (746648322116101/10000000000000 : ℝ)*(sp6) + (380442866501923/10000000000000 : ℝ)*(sp7) + (380442866501923/10000000000000 : ℝ)*(f.failure) + (7466513012020847/100000000000000 : ℝ)*(f.sum) + (7560501790369/16025000000000000000000000000 : ℝ)*base65 + (4030644307278481863/400625000000000000000000000000000 : ℝ)*base67 + (3691785063712856863/400625000000000000000000000000000 : ℝ)*base69 + (2568297484580981863/400625000000000000000000000000000 : ℝ)*base71 + (20405402092831/16025000000000000000000000000 : ℝ)*base74 + (778253974602231863/400625000000000000000000000000000 : ℝ)*base75 + (2958707559059731863/400625000000000000000000000000000 : ℝ)*base77 + (3986298701766606863/400625000000000000000000000000000 : ℝ)*base79 + (3033314925543/2003125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5988787/1000000000000000000000 : ℝ)*base90 + (5988787/1000000000000000000000 : ℝ)*base92 + (5988787/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1073_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11037/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1073_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1073_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1073_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1073_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8359/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1121/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14061/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

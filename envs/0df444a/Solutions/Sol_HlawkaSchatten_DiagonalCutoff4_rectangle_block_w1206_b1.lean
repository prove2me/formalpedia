-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1206_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:05:25.975588+00:00
-- url     : https://prove2.me/submissions/a89d28fe-508a-4e0b-9227-4e0638901bc8

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
theorem support_rectangle_w1206_s3_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066747171/5000000000 : ℝ)*x 0 + (5422904567/10000000000 : ℝ)*x 1 + (5237744407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066747171/5000000000 : ℝ)^8399 ≤ (12964159521123/100000000000000 : ℝ)^6351 := by
    have hnat : (1066747171 : ℕ)^8399*100000000000000^6351 ≤ 12964159521123^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066747171 5000000000 12964159521123 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422904567/10000000000 : ℝ)^8399 ≤ (11129356208953/25000000000000 : ℝ)^6351 := by
    have hnat : (5422904567 : ℕ)^8399*25000000000000^6351 ≤ 11129356208953^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422904567 10000000000 11129356208953 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237744407/10000000000 : ℝ)^8399 ≤ (265740097703/625000000000 : ℝ)^6351 := by
    have hnat : (5237744407 : ℕ)^8399*625000000000^6351 ≤ 265740097703^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237744407 10000000000 265740097703 625000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066747171/5000000000 : ℝ), (5422904567/10000000000 : ℝ), (5237744407/10000000000 : ℝ)] ![(12964159521123/100000000000000 : ℝ), (11129356208953/25000000000000 : ℝ), (265740097703/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066747171/5000000000 : ℝ)|^8399 ≤ (12964159521123/100000000000000 : ℝ)^6351
        have hw : |(-1066747171/5000000000 : ℝ)|=(1066747171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422904567/10000000000 : ℝ)|^8399 ≤ (11129356208953/25000000000000 : ℝ)^6351
        have hw : |(5422904567/10000000000 : ℝ)|=(5422904567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237744407/10000000000 : ℝ)|^8399 ≤ (265740097703/625000000000 : ℝ)^6351
        have hw : |(5237744407/10000000000 : ℝ)|=(5237744407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352295197/10000000000 : ℝ)*x 0 + (-557004061/2500000000 : ℝ)*x 1 + (523774419/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352295197/10000000000 : ℝ)^8399 ≤ (8750495874109/20000000000000 : ℝ)^6351 := by
    have hnat : (5352295197 : ℕ)^8399*20000000000000^6351 ≤ 8750495874109^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352295197 10000000000 8750495874109 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557004061/2500000000 : ℝ)^8399 ≤ (6864553657561/50000000000000 : ℝ)^6351 := by
    have hnat : (557004061 : ℕ)^8399*50000000000000^6351 ≤ 6864553657561^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557004061 2500000000 6864553657561 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523774419/1000000000 : ℝ)^8399 ≤ (21259206651449/50000000000000 : ℝ)^6351 := by
    have hnat : (523774419 : ℕ)^8399*50000000000000^6351 ≤ 21259206651449^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523774419 1000000000 21259206651449 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352295197/10000000000 : ℝ), (-557004061/2500000000 : ℝ), (523774419/1000000000 : ℝ)] ![(8750495874109/20000000000000 : ℝ), (6864553657561/50000000000000 : ℝ), (21259206651449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352295197/10000000000 : ℝ)|^8399 ≤ (8750495874109/20000000000000 : ℝ)^6351
        have hw : |(5352295197/10000000000 : ℝ)|=(5352295197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557004061/2500000000 : ℝ)|^8399 ≤ (6864553657561/50000000000000 : ℝ)^6351
        have hw : |(-557004061/2500000000 : ℝ)|=(557004061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523774419/1000000000 : ℝ)|^8399 ≤ (21259206651449/50000000000000 : ℝ)^6351
        have hw : |(523774419/1000000000 : ℝ)|=(523774419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676147651/5000000000 : ℝ)*x 0 + (2618872041/5000000000 : ℝ)*x 1 + (-2228016247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676147651/5000000000 : ℝ)^8399 ≤ (21876240252827/50000000000000 : ℝ)^6351 := by
    have hnat : (2676147651 : ℕ)^8399*50000000000000^6351 ≤ 21876240252827^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676147651 5000000000 21876240252827 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618872041/5000000000 : ℝ)^8399 ≤ (1700736485739/4000000000000 : ℝ)^6351 := by
    have hnat : (2618872041 : ℕ)^8399*4000000000000^6351 ≤ 1700736485739^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618872041 5000000000 1700736485739 4000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228016247/10000000000 : ℝ)^8399 ≤ (13729107339569/100000000000000 : ℝ)^6351 := by
    have hnat : (2228016247 : ℕ)^8399*100000000000000^6351 ≤ 13729107339569^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228016247 10000000000 13729107339569 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676147651/5000000000 : ℝ), (2618872041/5000000000 : ℝ), (-2228016247/10000000000 : ℝ)] ![(21876240252827/50000000000000 : ℝ), (1700736485739/4000000000000 : ℝ), (13729107339569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676147651/5000000000 : ℝ)|^8399 ≤ (21876240252827/50000000000000 : ℝ)^6351
        have hw : |(2676147651/5000000000 : ℝ)|=(2676147651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618872041/5000000000 : ℝ)|^8399 ≤ (1700736485739/4000000000000 : ℝ)^6351
        have hw : |(2618872041/5000000000 : ℝ)|=(2618872041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228016247/10000000000 : ℝ)|^8399 ≤ (13729107339569/100000000000000 : ℝ)^6351
        have hw : |(-2228016247/10000000000 : ℝ)|=(2228016247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353852601/10000000000 : ℝ)*x 0 + (4171263169/10000000000 : ℝ)*x 1 + (454426473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353852601/10000000000 : ℝ)^8399 ≤ (33298274367161/100000000000000 : ℝ)^6351 := by
    have hnat : (4353852601 : ℕ)^8399*100000000000000^6351 ≤ 33298274367161^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353852601 10000000000 33298274367161 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171263169/10000000000 : ℝ)^8399 ≤ (15732063903433/50000000000000 : ℝ)^6351 := by
    have hnat : (4171263169 : ℕ)^8399*50000000000000^6351 ≤ 15732063903433^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171263169 10000000000 15732063903433 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454426473/1000000000 : ℝ)^8399 ≤ (17618798901093/50000000000000 : ℝ)^6351 := by
    have hnat : (454426473 : ℕ)^8399*50000000000000^6351 ≤ 17618798901093^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454426473 1000000000 17618798901093 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353852601/10000000000 : ℝ), (4171263169/10000000000 : ℝ), (454426473/1000000000 : ℝ)] ![(33298274367161/100000000000000 : ℝ), (15732063903433/50000000000000 : ℝ), (17618798901093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353852601/10000000000 : ℝ)|^8399 ≤ (33298274367161/100000000000000 : ℝ)^6351
        have hw : |(4353852601/10000000000 : ℝ)|=(4353852601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171263169/10000000000 : ℝ)|^8399 ≤ (15732063903433/50000000000000 : ℝ)^6351
        have hw : |(4171263169/10000000000 : ℝ)|=(4171263169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(454426473/1000000000 : ℝ)|^8399 ≤ (17618798901093/50000000000000 : ℝ)^6351
        have hw : |(454426473/1000000000 : ℝ)|=(454426473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066754757/5000000000 : ℝ)*x 0 + (1309608101/2500000000 : ℝ)*x 1 + (216888519/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066754757/5000000000 : ℝ)^8399 ≤ (12964281443009/100000000000000 : ℝ)^6351 := by
    have hnat : (1066754757 : ℕ)^8399*100000000000000^6351 ≤ 12964281443009^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066754757 5000000000 12964281443009 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309608101/2500000000 : ℝ)^8399 ≤ (8505160342409/20000000000000 : ℝ)^6351 := by
    have hnat : (1309608101 : ℕ)^8399*20000000000000^6351 ≤ 8505160342409^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309608101 2500000000 8505160342409 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216888519/400000000 : ℝ)^8399 ≤ (44509916830499/100000000000000 : ℝ)^6351 := by
    have hnat : (216888519 : ℕ)^8399*100000000000000^6351 ≤ 44509916830499^6351*400000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216888519 400000000 44509916830499 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066754757/5000000000 : ℝ), (1309608101/2500000000 : ℝ), (216888519/400000000 : ℝ)] ![(12964281443009/100000000000000 : ℝ), (8505160342409/20000000000000 : ℝ), (44509916830499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066754757/5000000000 : ℝ)|^8399 ≤ (12964281443009/100000000000000 : ℝ)^6351
        have hw : |(-1066754757/5000000000 : ℝ)|=(1066754757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309608101/2500000000 : ℝ)|^8399 ≤ (8505160342409/20000000000000 : ℝ)^6351
        have hw : |(1309608101/2500000000 : ℝ)|=(1309608101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216888519/400000000 : ℝ)|^8399 ≤ (44509916830499/100000000000000 : ℝ)^6351
        have hw : |(216888519/400000000 : ℝ)|=(216888519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305171937/10000000000 : ℝ)*x 0 + (-1021773813/5000000000 : ℝ)*x 1 + (5422212659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305171937/10000000000 : ℝ)^8399 ≤ (4324377527969/10000000000000 : ℝ)^6351 := by
    have hnat : (5305171937 : ℕ)^8399*10000000000000^6351 ≤ 4324377527969^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305171937 10000000000 4324377527969 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021773813/5000000000 : ℝ)^8399 ≤ (12246311306587/100000000000000 : ℝ)^6351 := by
    have hnat : (1021773813 : ℕ)^8399*100000000000000^6351 ≤ 12246311306587^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021773813 5000000000 12246311306587 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422212659/10000000000 : ℝ)^8399 ≤ (11127478350009/25000000000000 : ℝ)^6351 := by
    have hnat : (5422212659 : ℕ)^8399*25000000000000^6351 ≤ 11127478350009^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422212659 10000000000 11127478350009 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305171937/10000000000 : ℝ), (-1021773813/5000000000 : ℝ), (5422212659/10000000000 : ℝ)] ![(4324377527969/10000000000000 : ℝ), (12246311306587/100000000000000 : ℝ), (11127478350009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305171937/10000000000 : ℝ)|^8399 ≤ (4324377527969/10000000000000 : ℝ)^6351
        have hw : |(5305171937/10000000000 : ℝ)|=(5305171937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021773813/5000000000 : ℝ)|^8399 ≤ (12246311306587/100000000000000 : ℝ)^6351
        have hw : |(-1021773813/5000000000 : ℝ)|=(1021773813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422212659/10000000000 : ℝ)|^8399 ≤ (11127478350009/25000000000000 : ℝ)^6351
        have hw : |(5422212659/10000000000 : ℝ)|=(5422212659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1326292953/2500000000 : ℝ)*x 0 + (677776581/1250000000 : ℝ)*x 1 + (-204354781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326292953/2500000000 : ℝ)^8399 ≤ (43243773932219/100000000000000 : ℝ)^6351 := by
    have hnat : (1326292953 : ℕ)^8399*100000000000000^6351 ≤ 43243773932219^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326292953 2500000000 43243773932219 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677776581/1250000000 : ℝ)^8399 ≤ (44509913280621/100000000000000 : ℝ)^6351 := by
    have hnat : (677776581 : ℕ)^8399*100000000000000^6351 ≤ 44509913280621^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677776581 1250000000 44509913280621 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204354781/1000000000 : ℝ)^8399 ≤ (1224631276481/10000000000000 : ℝ)^6351 := by
    have hnat : (204354781 : ℕ)^8399*10000000000000^6351 ≤ 1224631276481^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204354781 1000000000 1224631276481 10000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326292953/2500000000 : ℝ), (677776581/1250000000 : ℝ), (-204354781/1000000000 : ℝ)] ![(43243773932219/100000000000000 : ℝ), (44509913280621/100000000000000 : ℝ), (1224631276481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326292953/2500000000 : ℝ)|^8399 ≤ (43243773932219/100000000000000 : ℝ)^6351
        have hw : |(1326292953/2500000000 : ℝ)|=(1326292953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677776581/1250000000 : ℝ)|^8399 ≤ (44509913280621/100000000000000 : ℝ)^6351
        have hw : |(677776581/1250000000 : ℝ)|=(677776581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-204354781/1000000000 : ℝ)|^8399 ≤ (1224631276481/10000000000000 : ℝ)^6351
        have hw : |(-204354781/1000000000 : ℝ)|=(204354781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s3_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435388347/1000000000 : ℝ)*x 0 + (45428781/100000000 : ℝ)*x 1 + (2086328593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435388347/1000000000 : ℝ)^8399 ≤ (665971731683/2000000000000 : ℝ)^6351 := by
    have hnat : (435388347 : ℕ)^8399*2000000000000^6351 ≤ 665971731683^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435388347 1000000000 665971731683 2000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45428781/100000000 : ℝ)^8399 ≤ (35223378857577/100000000000000 : ℝ)^6351 := by
    have hnat : (45428781 : ℕ)^8399*100000000000000^6351 ≤ 35223378857577^6351*100000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45428781 100000000 35223378857577 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086328593/5000000000 : ℝ)^8399 ≤ (1967377158597/6250000000000 : ℝ)^6351 := by
    have hnat : (2086328593 : ℕ)^8399*6250000000000^6351 ≤ 1967377158597^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086328593 5000000000 1967377158597 6250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435388347/1000000000 : ℝ), (45428781/100000000 : ℝ), (2086328593/5000000000 : ℝ)] ![(665971731683/2000000000000 : ℝ), (35223378857577/100000000000000 : ℝ), (1967377158597/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435388347/1000000000 : ℝ)|^8399 ≤ (665971731683/2000000000000 : ℝ)^6351
        have hw : |(435388347/1000000000 : ℝ)|=(435388347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45428781/100000000 : ℝ)|^8399 ≤ (35223378857577/100000000000000 : ℝ)^6351
        have hw : |(45428781/100000000 : ℝ)|=(45428781/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086328593/5000000000 : ℝ)|^8399 ≤ (1967377158597/6250000000000 : ℝ)^6351
        have hw : |(2086328593/5000000000 : ℝ)|=(2086328593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (338/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2947/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16319/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (187/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16319/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (187/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16319/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (187/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16319/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (187/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16319/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (187/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16319/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (187/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (187/2000 : ℝ) ^ (4199/1024 : ℝ) ≤ (23522560769883/390625000000000000 : ℝ) := by
    have hpowers : (187/2000 : ℝ)^4199 ≤ (23522560769883/390625000000000000 : ℝ)^1024 := by
      have hnat : (187 : ℕ)^4199*390625000000000000^1024 ≤ 23522560769883^1024*2000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        187 2000 23522560769883 390625000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (187/2000 : ℝ)) (X := (23522560769883/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16319/100000 : ℝ) ^ (4199/1024 : ℝ) ≤ (29549641469467627/50000000000000000000 : ℝ) := by
    have hpowers : (16319/100000 : ℝ)^4199 ≤ (29549641469467627/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16319 : ℕ)^4199*50000000000000000000^1024 ≤ 29549641469467627^1024*100000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16319 100000 29549641469467627 50000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16319/100000 : ℝ)) (X := (29549641469467627/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (195336022560769883/195312500000000000 : ℝ) ≤ (2000058737960683/2000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (195336022560769883/195312500000000000 : ℝ)^1024 ≤ (2000058737960683/2000000000000000 : ℝ)^4199 := by
      have hnat : (195336022560769883 : ℕ)^1024*2000000000000000^4199 ≤ 2000058737960683^4199*195312500000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195336022560769883 195312500000000000 2000058737960683 2000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000058737960683/2000000000000000 : ℝ)) (X := (195336022560769883/195312500000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50032560529248012651/50000000000000000000 : ℝ) ≤ (10001587700702929/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50032560529248012651/50000000000000000000 : ℝ)^1024 ≤ (10001587700702929/10000000000000000 : ℝ)^4199 := by
      have hnat : (50032560529248012651 : ℕ)^1024*10000000000000000^4199 ≤ 10001587700702929^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032560529248012651 50000000000000000000 10001587700702929 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001587700702929/10000000000000000 : ℝ)) (X := (50032560529248012651/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25029549641469467627/25000000000000000000 : ℝ) ≤ (10002881711602443/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (25029549641469467627/25000000000000000000 : ℝ)^1024 ≤ (10002881711602443/10000000000000000 : ℝ)^4199 := by
      have hnat : (25029549641469467627 : ℕ)^1024*10000000000000000^4199 ≤ 10002881711602443^4199*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25029549641469467627 25000000000000000000 10002881711602443 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002881711602443/10000000000000000 : ℝ)) (X := (25029549641469467627/25000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23522560769883/390625000000000000 : ℝ) ≤ ((13933569744083817467/13938000000000000000 : ℝ)+2*(647005449757/348450000000000 : ℝ)*(187/2000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (13933569744083817467/13938000000000000000 : ℝ)+2*(647005449757/348450000000000 : ℝ)*(187/2000 : ℝ)=(2000058737960683/2000000000000000 : ℝ) by norm_num, show 1+2*(23522560769883/390625000000000000 : ℝ)=(195336022560769883/195312500000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29549641469467627/50000000000000000000 : ℝ)+(23522560769883/390625000000000000 : ℝ) ≤ ((13933569744083817467/13938000000000000000 : ℝ)+(647005449757/348450000000000 : ℝ)*((16319/100000 : ℝ)+(187/2000 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (13933569744083817467/13938000000000000000 : ℝ)+(647005449757/348450000000000 : ℝ)*((16319/100000 : ℝ)+(187/2000 : ℝ))=(10001587700702929/10000000000000000 : ℝ) by norm_num, show 1+(29549641469467627/50000000000000000000 : ℝ)+(23522560769883/390625000000000000 : ℝ)=(50032560529248012651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29549641469467627/50000000000000000000 : ℝ) ≤ ((13933569744083817467/13938000000000000000 : ℝ)+2*(647005449757/348450000000000 : ℝ)*(16319/100000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (13933569744083817467/13938000000000000000 : ℝ)+2*(647005449757/348450000000000 : ℝ)*(16319/100000 : ℝ)=(10002881711602443/10000000000000000 : ℝ) by norm_num, show 1+2*(29549641469467627/50000000000000000000 : ℝ)=(25029549641469467627/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13933569744083817467/13938000000000000000 : ℝ)*(X 1 0+X 2 0)+(647005449757/348450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (187/2000 : ℝ)) (hi := (16319/100000 : ℝ)) (c := (13933569744083817467/13938000000000000000 : ℝ)) (alpha := (647005449757/348450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13933569744083817467/13938000000000000000 : ℝ)*(X 0 1+X 2 1)+(647005449757/348450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (187/2000 : ℝ)) (hi := (16319/100000 : ℝ)) (c := (13933569744083817467/13938000000000000000 : ℝ)) (alpha := (647005449757/348450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13933569744083817467/13938000000000000000 : ℝ)*(X 0 2+X 1 2)+(647005449757/348450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (187/2000 : ℝ)) (hi := (16319/100000 : ℝ)) (c := (13933569744083817467/13938000000000000000 : ℝ)) (alpha := (647005449757/348450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066747171/5000000000 : ℝ)*X 0 0+(5422904567/10000000000 : ℝ)*X 0 1+(5237744407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352295197/10000000000 : ℝ)*X 1 0+(-557004061/2500000000 : ℝ)*X 1 1+(523774419/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676147651/5000000000 : ℝ)*X 2 0+(2618872041/5000000000 : ℝ)*X 2 1+(-2228016247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353852601/10000000000 : ℝ)*X 0 0+(4171263169/10000000000 : ℝ)*X 0 1+(454426473/1000000000 : ℝ)*X 0 2+(4353852601/10000000000 : ℝ)*X 1 0+(4171263169/10000000000 : ℝ)*X 1 1+(454426473/1000000000 : ℝ)*X 1 2+(4353852601/10000000000 : ℝ)*X 2 0+(4171263169/10000000000 : ℝ)*X 2 1+(454426473/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1066754757/5000000000 : ℝ)*X 0 0+(1309608101/2500000000 : ℝ)*X 0 1+(216888519/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305171937/10000000000 : ℝ)*X 1 0+(-1021773813/5000000000 : ℝ)*X 1 1+(5422212659/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326292953/2500000000 : ℝ)*X 2 0+(677776581/1250000000 : ℝ)*X 2 1+(-204354781/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435388347/1000000000 : ℝ)*X 0 0+(45428781/100000000 : ℝ)*X 0 1+(2086328593/5000000000 : ℝ)*X 0 2+(435388347/1000000000 : ℝ)*X 1 0+(45428781/100000000 : ℝ)*X 1 1+(2086328593/5000000000 : ℝ)*X 1 2+(435388347/1000000000 : ℝ)*X 2 0+(45428781/100000000 : ℝ)*X 2 1+(2086328593/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (270999428343223745122756551/29037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2102558857/100000000000000 : ℝ)*(base19) + (261154319/12500000000000 : ℝ)*(base23) + (63839923/100000000000000 : ℝ)*(lower2) + (7930437/3125000000000 : ℝ)*(upper3) + (11133557/6250000000000 : ℝ)*(upper5) + (505111828405047/12500000000000 : ℝ)*(major0) + (505111828405047/12500000000000 : ℝ)*(major1) + (505111828405047/12500000000000 : ℝ)*(major2) + (1350191085021227/25000000000000 : ℝ)*(sp0) + (5400796407087169/100000000000000 : ℝ)*(sp1) + (2700398210205737/50000000000000 : ℝ)*(sp2) + (2680971156482011/100000000000000 : ℝ)*(sp3) + (17084780559/50000000000000 : ℝ)*(sp4) + (19277261389/100000000000000 : ℝ)*(sp7) + (13404952168717/500000000000 : ℝ)*(f.failure) + (2700399254823013/50000000000000 : ℝ)*(f.sum) + (24134695874507/11615000000000000000000000000 : ℝ)*base66 + (295020284671546983/58075000000000000000000000000000 : ℝ)*base67 + (212710429033321983/58075000000000000000000000000000 : ℝ)*base69 + (410452973225521983/58075000000000000000000000000000 : ℝ)*base71 + (28080628115557/11615000000000000000000000000 : ℝ)*base74 + (216817062386478017/58075000000000000000000000000000 : ℝ)*base76 + (42419817453603017/58075000000000000000000000000000 : ℝ)*base78 + (167385700214546983/58075000000000000000000000000000 : ℝ)*base79 + (1769531564949/5807500000000000000000000000 : ℝ)*base81 + (83679/12500000000000000000 : ℝ)*base89 + (83679/12500000000000000000 : ℝ)*base91 + (83679/12500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98965837599778275086797653/23230000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (247110123/25000000000000 : ℝ)*(base19) + (505108633/50000000000000 : ℝ)*(base23) + (5510813/5000000000000 : ℝ)*(lower4) + (41214537/25000000000000 : ℝ)*(upper5) + (407118372980453/10000000000000 : ℝ)*(major0) + (407118372980453/10000000000000 : ℝ)*(major1) + (407118372980453/10000000000000 : ℝ)*(major2) + (1823286681/50000000000000 : ℝ)*(sp0) + (18854732811/100000000000000 : ℝ)*(sp1) + (12351025193/100000000000000 : ℝ)*(sp2) + (2720638745372147/50000000000000 : ℝ)*(sp4) + (2720630647072177/50000000000000 : ℝ)*(sp5) + (2720633888037599/50000000000000 : ℝ)*(sp6) + (675271545070683/25000000000000 : ℝ)*(sp7) + (675271545070683/25000000000000 : ℝ)*(f.failure) + (5441281137317657/100000000000000 : ℝ)*(f.sum) + (4067016514399/1742250000000000000000000000 : ℝ)*base66 + (269170561109862483/46460000000000000000000000000000 : ℝ)*base68 + (81750777362622483/46460000000000000000000000000000 : ℝ)*base70 + (622899637846362483/46460000000000000000000000000000 : ℝ)*base72 + (4814571722311/1742250000000000000000000000 : ℝ)*base74 + (489906262814942483/46460000000000000000000000000000 : ℝ)*base76 + (134979486722982483/46460000000000000000000000000000 : ℝ)*base78 + (418089500655862483/46460000000000000000000000000000 : ℝ)*base80 + (5674470953837/1393800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (7704121/625000000000000000000 : ℝ)*base89 + (7704121/625000000000000000000 : ℝ)*base91 + (7704121/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1206_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1206_s4_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136020839/10000000000 : ℝ)*x 0 + (1349747721/2500000000 : ℝ)*x 1 + (131500087/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136020839/10000000000 : ℝ)^8399 ≤ (12984466252229/100000000000000 : ℝ)^6351 := by
    have hnat : (2136020839 : ℕ)^8399*100000000000000^6351 ≤ 12984466252229^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136020839 10000000000 12984466252229 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349747721/2500000000 : ℝ)^8399 ≤ (44257994471601/100000000000000 : ℝ)^6351 := by
    have hnat : (1349747721 : ℕ)^8399*100000000000000^6351 ≤ 44257994471601^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349747721 2500000000 44257994471601 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131500087/250000000 : ℝ)^8399 ≤ (855150785389/2000000000000 : ℝ)^6351 := by
    have hnat : (131500087 : ℕ)^8399*2000000000000^6351 ≤ 855150785389^6351*250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131500087 250000000 855150785389 2000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136020839/10000000000 : ℝ), (1349747721/2500000000 : ℝ), (131500087/250000000 : ℝ)] ![(12984466252229/100000000000000 : ℝ), (44257994471601/100000000000000 : ℝ), (855150785389/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136020839/10000000000 : ℝ)|^8399 ≤ (12984466252229/100000000000000 : ℝ)^6351
        have hw : |(-2136020839/10000000000 : ℝ)|=(2136020839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349747721/2500000000 : ℝ)|^8399 ≤ (44257994471601/100000000000000 : ℝ)^6351
        have hw : |(1349747721/2500000000 : ℝ)|=(1349747721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131500087/250000000 : ℝ)|^8399 ≤ (855150785389/2000000000000 : ℝ)^6351
        have hw : |(131500087/250000000 : ℝ)|=(131500087/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069257239/2000000000 : ℝ)*x 0 + (-55165231/250000000 : ℝ)*x 1 + (5260003463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069257239/2000000000 : ℝ)^8399 ≤ (43687530472699/100000000000000 : ℝ)^6351 := by
    have hnat : (1069257239 : ℕ)^8399*100000000000000^6351 ≤ 43687530472699^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069257239 2000000000 43687530472699 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55165231/250000000 : ℝ)^8399 ≤ (33887326069/250000000000 : ℝ)^6351 := by
    have hnat : (55165231 : ℕ)^8399*250000000000^6351 ≤ 33887326069^6351*250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55165231 250000000 33887326069 250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260003463/10000000000 : ℝ)^8399 ≤ (21378769543349/50000000000000 : ℝ)^6351 := by
    have hnat : (5260003463 : ℕ)^8399*50000000000000^6351 ≤ 21378769543349^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260003463 10000000000 21378769543349 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069257239/2000000000 : ℝ), (-55165231/250000000 : ℝ), (5260003463/10000000000 : ℝ)] ![(43687530472699/100000000000000 : ℝ), (33887326069/250000000000 : ℝ), (21378769543349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069257239/2000000000 : ℝ)|^8399 ≤ (43687530472699/100000000000000 : ℝ)^6351
        have hw : |(1069257239/2000000000 : ℝ)|=(1069257239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55165231/250000000 : ℝ)|^8399 ≤ (33887326069/250000000000 : ℝ)^6351
        have hw : |(-55165231/250000000 : ℝ)|=(55165231/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260003463/10000000000 : ℝ)|^8399 ≤ (21378769543349/50000000000000 : ℝ)^6351
        have hw : |(5260003463/10000000000 : ℝ)|=(5260003463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346286171/10000000000 : ℝ)*x 0 + (2630001747/5000000000 : ℝ)*x 1 + (-220660923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346286171/10000000000 : ℝ)^8399 ≤ (2184376510667/5000000000000 : ℝ)^6351 := by
    have hnat : (5346286171 : ℕ)^8399*5000000000000^6351 ≤ 2184376510667^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346286171 10000000000 2184376510667 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630001747/5000000000 : ℝ)^8399 ≤ (42757539419951/100000000000000 : ℝ)^6351 := by
    have hnat : (2630001747 : ℕ)^8399*100000000000000^6351 ≤ 42757539419951^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630001747 5000000000 42757539419951 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220660923/1000000000 : ℝ)^8399 ≤ (6777465173181/50000000000000 : ℝ)^6351 := by
    have hnat : (220660923 : ℕ)^8399*50000000000000^6351 ≤ 6777465173181^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220660923 1000000000 6777465173181 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346286171/10000000000 : ℝ), (2630001747/5000000000 : ℝ), (-220660923/1000000000 : ℝ)] ![(2184376510667/5000000000000 : ℝ), (42757539419951/100000000000000 : ℝ), (6777465173181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346286171/10000000000 : ℝ)|^8399 ≤ (2184376510667/5000000000000 : ℝ)^6351
        have hw : |(5346286171/10000000000 : ℝ)|=(5346286171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630001747/5000000000 : ℝ)|^8399 ≤ (42757539419951/100000000000000 : ℝ)^6351
        have hw : |(2630001747/5000000000 : ℝ)|=(2630001747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220660923/1000000000 : ℝ)|^8399 ≤ (6777465173181/50000000000000 : ℝ)^6351
        have hw : |(-220660923/1000000000 : ℝ)|=(220660923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355364813/10000000000 : ℝ)*x 0 + (4217576393/10000000000 : ℝ)*x 1 + (562195441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355364813/10000000000 : ℝ)^8399 ≤ (33313570106443/100000000000000 : ℝ)^6351 := by
    have hnat : (4355364813 : ℕ)^8399*100000000000000^6351 ≤ 33313570106443^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355364813 10000000000 33313570106443 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4217576393/10000000000 : ℝ)^8399 ≤ (49885858117/156250000000 : ℝ)^6351 := by
    have hnat : (4217576393 : ℕ)^8399*156250000000^6351 ≤ 49885858117^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4217576393 10000000000 49885858117 156250000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562195441/1250000000 : ℝ)^8399 ≤ (2172467542619/6250000000000 : ℝ)^6351 := by
    have hnat : (562195441 : ℕ)^8399*6250000000000^6351 ≤ 2172467542619^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562195441 1250000000 2172467542619 6250000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355364813/10000000000 : ℝ), (4217576393/10000000000 : ℝ), (562195441/1250000000 : ℝ)] ![(33313570106443/100000000000000 : ℝ), (49885858117/156250000000 : ℝ), (2172467542619/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355364813/10000000000 : ℝ)|^8399 ≤ (33313570106443/100000000000000 : ℝ)^6351
        have hw : |(4355364813/10000000000 : ℝ)|=(4355364813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4217576393/10000000000 : ℝ)|^8399 ≤ (49885858117/156250000000 : ℝ)^6351
        have hw : |(4217576393/10000000000 : ℝ)|=(4217576393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562195441/1250000000 : ℝ)|^8399 ≤ (2172467542619/6250000000000 : ℝ)^6351
        have hw : |(562195441/1250000000 : ℝ)|=(562195441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068013401/5000000000 : ℝ)*x 0 + (526039173/1000000000 : ℝ)*x 1 + (2699300727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068013401/5000000000 : ℝ)^8399 ≤ (2596902837807/20000000000000 : ℝ)^6351 := by
    have hnat : (1068013401 : ℕ)^8399*20000000000000^6351 ≤ 2596902837807^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068013401 5000000000 2596902837807 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526039173/1000000000 : ℝ)^8399 ≤ (10690428260487/25000000000000 : ℝ)^6351 := by
    have hnat : (526039173 : ℕ)^8399*25000000000000^6351 ≤ 10690428260487^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526039173 1000000000 10690428260487 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699300727/5000000000 : ℝ)^8399 ≤ (22126886378073/50000000000000 : ℝ)^6351 := by
    have hnat : (2699300727 : ℕ)^8399*50000000000000^6351 ≤ 22126886378073^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699300727 5000000000 22126886378073 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068013401/5000000000 : ℝ), (526039173/1000000000 : ℝ), (2699300727/5000000000 : ℝ)] ![(2596902837807/20000000000000 : ℝ), (10690428260487/25000000000000 : ℝ), (22126886378073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068013401/5000000000 : ℝ)|^8399 ≤ (2596902837807/20000000000000 : ℝ)^6351
        have hw : |(-1068013401/5000000000 : ℝ)|=(1068013401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526039173/1000000000 : ℝ)|^8399 ≤ (10690428260487/25000000000000 : ℝ)^6351
        have hw : |(526039173/1000000000 : ℝ)|=(526039173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699300727/5000000000 : ℝ)|^8399 ≤ (22126886378073/50000000000000 : ℝ)^6351
        have hw : |(2699300727/5000000000 : ℝ)|=(2699300727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327728037/2500000000 : ℝ)*x 0 + (-413602453/2000000000 : ℝ)*x 1 + (215944033/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327728037/2500000000 : ℝ)^8399 ≤ (8661132848473/20000000000000 : ℝ)^6351 := by
    have hnat : (1327728037 : ℕ)^8399*20000000000000^6351 ≤ 8661132848473^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327728037 2500000000 8661132848473 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413602453/2000000000 : ℝ)^8399 ≤ (12440569813593/100000000000000 : ℝ)^6351 := by
    have hnat : (413602453 : ℕ)^8399*100000000000000^6351 ≤ 12440569813593^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413602453 2000000000 12440569813593 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215944033/400000000 : ℝ)^8399 ≤ (44253765937391/100000000000000 : ℝ)^6351 := by
    have hnat : (215944033 : ℕ)^8399*100000000000000^6351 ≤ 44253765937391^6351*400000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215944033 400000000 44253765937391 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327728037/2500000000 : ℝ), (-413602453/2000000000 : ℝ), (215944033/400000000 : ℝ)] ![(8661132848473/20000000000000 : ℝ), (12440569813593/100000000000000 : ℝ), (44253765937391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327728037/2500000000 : ℝ)|^8399 ≤ (8661132848473/20000000000000 : ℝ)^6351
        have hw : |(1327728037/2500000000 : ℝ)|=(1327728037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413602453/2000000000 : ℝ)|^8399 ≤ (12440569813593/100000000000000 : ℝ)^6351
        have hw : |(-413602453/2000000000 : ℝ)|=(413602453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215944033/400000000 : ℝ)|^8399 ≤ (44253765937391/100000000000000 : ℝ)^6351
        have hw : |(215944033/400000000 : ℝ)|=(215944033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655456521/5000000000 : ℝ)*x 0 + (5398600231/10000000000 : ℝ)*x 1 + (-1034005931/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655456521/5000000000 : ℝ)^8399 ≤ (43305673882843/100000000000000 : ℝ)^6351 := by
    have hnat : (2655456521 : ℕ)^8399*100000000000000^6351 ≤ 43305673882843^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655456521 5000000000 43305673882843 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398600231/10000000000 : ℝ)^8399 ≤ (44253759498057/100000000000000 : ℝ)^6351 := by
    have hnat : (5398600231 : ℕ)^8399*100000000000000^6351 ≤ 44253759498057^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398600231 10000000000 44253759498057 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034005931/5000000000 : ℝ)^8399 ≤ (12440566607489/100000000000000 : ℝ)^6351 := by
    have hnat : (1034005931 : ℕ)^8399*100000000000000^6351 ≤ 12440566607489^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034005931 5000000000 12440566607489 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655456521/5000000000 : ℝ), (5398600231/10000000000 : ℝ), (-1034005931/5000000000 : ℝ)] ![(43305673882843/100000000000000 : ℝ), (44253759498057/100000000000000 : ℝ), (12440566607489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655456521/5000000000 : ℝ)|^8399 ≤ (43305673882843/100000000000000 : ℝ)^6351
        have hw : |(2655456521/5000000000 : ℝ)|=(2655456521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398600231/10000000000 : ℝ)|^8399 ≤ (44253759498057/100000000000000 : ℝ)^6351
        have hw : |(5398600231/10000000000 : ℝ)|=(5398600231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034005931/5000000000 : ℝ)|^8399 ≤ (12440566607489/100000000000000 : ℝ)^6351
        have hw : |(-1034005931/5000000000 : ℝ)|=(1034005931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s4_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088844587/2500000000 : ℝ)*x 0 + (4496780723/10000000000 : ℝ)*x 1 + (4218361871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088844587/2500000000 : ℝ)^8399 ≤ (666274140363/2000000000000 : ℝ)^6351 := by
    have hnat : (1088844587 : ℕ)^8399*2000000000000^6351 ≤ 666274140363^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088844587 2500000000 666274140363 2000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496780723/10000000000 : ℝ)^8399 ≤ (34751480076631/100000000000000 : ℝ)^6351 := by
    have hnat : (4496780723 : ℕ)^8399*100000000000000^6351 ≤ 34751480076631^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496780723 10000000000 34751480076631 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218361871/10000000000 : ℝ)^8399 ≤ (31934812895987/100000000000000 : ℝ)^6351 := by
    have hnat : (4218361871 : ℕ)^8399*100000000000000^6351 ≤ 31934812895987^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218361871 10000000000 31934812895987 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088844587/2500000000 : ℝ), (4496780723/10000000000 : ℝ), (4218361871/10000000000 : ℝ)] ![(666274140363/2000000000000 : ℝ), (34751480076631/100000000000000 : ℝ), (31934812895987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088844587/2500000000 : ℝ)|^8399 ≤ (666274140363/2000000000000 : ℝ)^6351
        have hw : |(1088844587/2500000000 : ℝ)|=(1088844587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496780723/10000000000 : ℝ)|^8399 ≤ (34751480076631/100000000000000 : ℝ)^6351
        have hw : |(4496780723/10000000000 : ℝ)|=(4496780723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218361871/10000000000 : ℝ)|^8399 ≤ (31934812895987/100000000000000 : ℝ)^6351
        have hw : |(4218361871/10000000000 : ℝ)|=(4218361871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11291/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (338/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (338/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (338/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2947/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (338/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (338/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2947/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (338/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (338/3125 : ℝ) ^ (4199/1024 : ℝ) ≤ (10942269469000057/100000000000000000000 : ℝ) := by
    have hpowers : (338/3125 : ℝ)^4199 ≤ (10942269469000057/100000000000000000000 : ℝ)^1024 := by
      have hnat : (338 : ℕ)^4199*100000000000000000000^1024 ≤ 10942269469000057^1024*3125^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        338 3125 10942269469000057 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (338/3125 : ℝ)) (X := (10942269469000057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2947/20000 : ℝ) ^ (4199/1024 : ℝ) ≤ (38881971708080463/100000000000000000000 : ℝ) := by
    have hpowers : (2947/20000 : ℝ)^4199 ≤ (38881971708080463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2947 : ℕ)^4199*100000000000000000000^1024 ≤ 38881971708080463^1024*20000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2947 20000 38881971708080463 100000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2947/20000 : ℝ)) (X := (38881971708080463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010942269469000057/50000000000000000000 : ℝ) ≤ (1250066706102553/1250000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50010942269469000057/50000000000000000000 : ℝ)^1024 ≤ (1250066706102553/1250000000000000 : ℝ)^4199 := by
      have hnat : (50010942269469000057 : ℕ)^1024*1250000000000000^4199 ≤ 1250066706102553^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010942269469000057 50000000000000000000 1250066706102553 1250000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250066706102553/1250000000000000 : ℝ)) (X := (50010942269469000057/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501245606029427013/2500000000000000000 : ℝ) ≤ (625075926433669/625000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (2501245606029427013/2500000000000000000 : ℝ)^1024 ≤ (625075926433669/625000000000000 : ℝ)^4199 := by
      have hnat : (2501245606029427013 : ℕ)^1024*625000000000000^4199 ≤ 625075926433669^4199*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501245606029427013 2500000000000000000 625075926433669 625000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625075926433669/625000000000000 : ℝ)) (X := (2501245606029427013/2500000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038881971708080463/50000000000000000000 : ℝ) ≤ (1250236999632123/1250000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (50038881971708080463/50000000000000000000 : ℝ)^1024 ≤ (1250236999632123/1250000000000000 : ℝ)^4199 := by
      have hnat : (50038881971708080463 : ℕ)^1024*1250000000000000^4199 ≤ 1250236999632123^4199*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038881971708080463 50000000000000000000 1250236999632123 1250000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250236999632123/1250000000000000 : ℝ)) (X := (50038881971708080463/50000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10942269469000057/100000000000000000000 : ℝ) ≤ ((4897169526400076087/4898750000000000000 : ℝ)+2*(17029352957/9797500000000 : ℝ)*(338/3125 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (4897169526400076087/4898750000000000000 : ℝ)+2*(17029352957/9797500000000 : ℝ)*(338/3125 : ℝ)=(1250066706102553/1250000000000000 : ℝ) by norm_num, show 1+2*(10942269469000057/100000000000000000000 : ℝ)=(50010942269469000057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38881971708080463/100000000000000000000 : ℝ)+(10942269469000057/100000000000000000000 : ℝ) ≤ ((4897169526400076087/4898750000000000000 : ℝ)+(17029352957/9797500000000 : ℝ)*((2947/20000 : ℝ)+(338/3125 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (4897169526400076087/4898750000000000000 : ℝ)+(17029352957/9797500000000 : ℝ)*((2947/20000 : ℝ)+(338/3125 : ℝ))=(625075926433669/625000000000000 : ℝ) by norm_num, show 1+(38881971708080463/100000000000000000000 : ℝ)+(10942269469000057/100000000000000000000 : ℝ)=(2501245606029427013/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38881971708080463/100000000000000000000 : ℝ) ≤ ((4897169526400076087/4898750000000000000 : ℝ)+2*(17029352957/9797500000000 : ℝ)*(2947/20000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (4897169526400076087/4898750000000000000 : ℝ)+2*(17029352957/9797500000000 : ℝ)*(2947/20000 : ℝ)=(1250236999632123/1250000000000000 : ℝ) by norm_num, show 1+2*(38881971708080463/100000000000000000000 : ℝ)=(50038881971708080463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4897169526400076087/4898750000000000000 : ℝ)*(X 1 0+X 2 0)+(17029352957/9797500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (4897169526400076087/4898750000000000000 : ℝ)) (alpha := (17029352957/9797500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4897169526400076087/4898750000000000000 : ℝ)*(X 0 1+X 2 1)+(17029352957/9797500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (4897169526400076087/4898750000000000000 : ℝ)) (alpha := (17029352957/9797500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4897169526400076087/4898750000000000000 : ℝ)*(X 0 2+X 1 2)+(17029352957/9797500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (338/3125 : ℝ)) (hi := (2947/20000 : ℝ)) (c := (4897169526400076087/4898750000000000000 : ℝ)) (alpha := (17029352957/9797500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136020839/10000000000 : ℝ)*X 0 0+(1349747721/2500000000 : ℝ)*X 0 1+(131500087/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069257239/2000000000 : ℝ)*X 1 0+(-55165231/250000000 : ℝ)*X 1 1+(5260003463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346286171/10000000000 : ℝ)*X 2 0+(2630001747/5000000000 : ℝ)*X 2 1+(-220660923/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355364813/10000000000 : ℝ)*X 0 0+(4217576393/10000000000 : ℝ)*X 0 1+(562195441/1250000000 : ℝ)*X 0 2+(4355364813/10000000000 : ℝ)*X 1 0+(4217576393/10000000000 : ℝ)*X 1 1+(562195441/1250000000 : ℝ)*X 1 2+(4355364813/10000000000 : ℝ)*X 2 0+(4217576393/10000000000 : ℝ)*X 2 1+(562195441/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1068013401/5000000000 : ℝ)*X 0 0+(526039173/1000000000 : ℝ)*X 0 1+(2699300727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327728037/2500000000 : ℝ)*X 1 0+(-413602453/2000000000 : ℝ)*X 1 1+(215944033/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655456521/5000000000 : ℝ)*X 2 0+(5398600231/10000000000 : ℝ)*X 2 1+(-1034005931/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088844587/2500000000 : ℝ)*X 0 0+(4496780723/10000000000 : ℝ)*X 0 1+(4218361871/10000000000 : ℝ)*X 0 2+(1088844587/2500000000 : ℝ)*X 1 0+(4496780723/10000000000 : ℝ)*X 1 1+(4218361871/10000000000 : ℝ)*X 1 2+(1088844587/2500000000 : ℝ)*X 2 0+(4496780723/10000000000 : ℝ)*X 2 1+(4218361871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18140674861569579803907/1959500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1727838369/100000000000000 : ℝ)*(base19) + (1480806367/100000000000000 : ℝ)*(base23) + (4592097/4000000000000 : ℝ)*(lower2) + (237480189/100000000000000 : ℝ)*(upper3) + (42690753/50000000000000 : ℝ)*(upper5) + (2691654410838517/50000000000000 : ℝ)*(major0) + (2691654410838517/50000000000000 : ℝ)*(major1) + (2691654410838517/50000000000000 : ℝ)*(major2) + (143898831290433/2000000000000 : ℝ)*(sp0) + (7194980911102527/100000000000000 : ℝ)*(sp1) + (719498115813453/10000000000000 : ℝ)*(sp2) + (111612867159539/3125000000000 : ℝ)*(sp3) + (41074419247/100000000000000 : ℝ)*(sp4) + (11473357157/50000000000000 : ℝ)*(sp7) + (1785817347909781/50000000000000 : ℝ)*(f.failure) + (7194982638940897/100000000000000 : ℝ)*(f.sum) + (2365006813479/979750000000000000000000000 : ℝ)*base65 + (2737474684278007021/244937500000000000000000000000000 : ℝ)*base68 + (1622780667758242979/244937500000000000000000000000000 : ℝ)*base69 + (1852878314123944521/244937500000000000000000000000000 : ℝ)*base72 + (969698747721/391900000000000000000000000 : ℝ)*base74 + (2952075129064680479/244937500000000000000000000000000 : ℝ)*base75 + (702586498317617979/244937500000000000000000000000000 : ℝ)*base77 + (1924228765858632021/244937500000000000000000000000000 : ℝ)*base80 + (8593048334059/1959500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10033847/1250000000000000000000 : ℝ)*base89 + (10033847/1250000000000000000000 : ℝ)*base91 + (10033847/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1057093592610436973957830683/122468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86120703/20000000000000 : ℝ)*(base19) + (2124258421/100000000000000 : ℝ)*(base23) + (259131563/100000000000000 : ℝ)*(lower2) + (39838789/10000000000000 : ℝ)*(lower4) + (102995983/100000000000000 : ℝ)*(upper5) + (2706786726110597/50000000000000 : ℝ)*(major0) + (2706786726110597/50000000000000 : ℝ)*(major1) + (2706786726110597/50000000000000 : ℝ)*(major2) + (28969899/156250000000 : ℝ)*(sp0) + (32052988127/100000000000000 : ℝ)*(sp2) + (361770693497427/5000000000000 : ℝ)*(sp4) + (1447086396016077/20000000000000 : ℝ)*(sp5) + (7235398233437351/100000000000000 : ℝ)*(sp6) + (718342841208113/20000000000000 : ℝ)*(sp7) + (718342841208113/20000000000000 : ℝ)*(f.failure) + (72354324106839/1000000000000 : ℝ)*(f.sum) + (11191295111059/979750000000000000000000000 : ℝ)*base66 + (6004904132774931439/244937500000000000000000000000000 : ℝ)*base67 + (3450165313858681439/244937500000000000000000000000000 : ℝ)*base69 + (1033446232516493939/244937500000000000000000000000000 : ℝ)*base71 + (4038610254667/1959500000000000000000000000 : ℝ)*base73 + (3829153721087256061/244937500000000000000000000000000 : ℝ)*base76 + (1369416723183568561/244937500000000000000000000000000 : ℝ)*base78 + (3664499039381118939/244937500000000000000000000000000 : ℝ)*base79 + (10927427408047/3919000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (247531/500000000000000000000 : ℝ)*base89 + (247531/500000000000000000000 : ℝ)*base91 + (247531/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1206_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2947/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (338/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1206_s5_0 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136528811/10000000000 : ℝ)*x 0 + (674161023/1250000000 : ℝ)*x 1 + (5265372597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136528811/10000000000 : ℝ)^8399 ≤ (2597710003009/20000000000000 : ℝ)^6351 := by
    have hnat : (2136528811 : ℕ)^8399*20000000000000^6351 ≤ 2597710003009^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136528811 10000000000 2597710003009 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674161023/1250000000 : ℝ)^8399 ≤ (176784730827/400000000000 : ℝ)^6351 := by
    have hnat : (674161023 : ℕ)^8399*400000000000^6351 ≤ 176784730827^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674161023 1250000000 176784730827 400000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265372597/10000000000 : ℝ)^8399 ≤ (2140763363141/5000000000000 : ℝ)^6351 := by
    have hnat : (5265372597 : ℕ)^8399*5000000000000^6351 ≤ 2140763363141^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265372597 10000000000 2140763363141 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136528811/10000000000 : ℝ), (674161023/1250000000 : ℝ), (5265372597/10000000000 : ℝ)] ![(2597710003009/20000000000000 : ℝ), (176784730827/400000000000 : ℝ), (2140763363141/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136528811/10000000000 : ℝ)|^8399 ≤ (2597710003009/20000000000000 : ℝ)^6351
        have hw : |(-2136528811/10000000000 : ℝ)|=(2136528811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674161023/1250000000 : ℝ)|^8399 ≤ (176784730827/400000000000 : ℝ)^6351
        have hw : |(674161023/1250000000 : ℝ)|=(674161023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265372597/10000000000 : ℝ)|^8399 ≤ (2140763363141/5000000000000 : ℝ)^6351
        have hw : |(5265372597/10000000000 : ℝ)|=(5265372597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_1 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334053019/625000000 : ℝ)*x 0 + (-1100706919/5000000000 : ℝ)*x 1 + (5265372607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334053019/625000000 : ℝ)^8399 ≤ (43671992373419/100000000000000 : ℝ)^6351 := by
    have hnat : (334053019 : ℕ)^8399*100000000000000^6351 ≤ 43671992373419^6351*625000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334053019 625000000 43671992373419 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100706919/5000000000 : ℝ)^8399 ≤ (2702548047169/20000000000000 : ℝ)^6351 := by
    have hnat : (1100706919 : ℕ)^8399*20000000000000^6351 ≤ 2702548047169^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100706919 5000000000 2702548047169 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265372607/10000000000 : ℝ)^8399 ≤ (10703816842589/25000000000000 : ℝ)^6351 := by
    have hnat : (5265372607 : ℕ)^8399*25000000000000^6351 ≤ 10703816842589^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265372607 10000000000 10703816842589 25000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334053019/625000000 : ℝ), (-1100706919/5000000000 : ℝ), (5265372607/10000000000 : ℝ)] ![(43671992373419/100000000000000 : ℝ), (2702548047169/20000000000000 : ℝ), (10703816842589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334053019/625000000 : ℝ)|^8399 ≤ (43671992373419/100000000000000 : ℝ)^6351
        have hw : |(334053019/625000000 : ℝ)|=(334053019/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100706919/5000000000 : ℝ)|^8399 ≤ (2702548047169/20000000000000 : ℝ)^6351
        have hw : |(-1100706919/5000000000 : ℝ)|=(1100706919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265372607/10000000000 : ℝ)|^8399 ≤ (10703816842589/25000000000000 : ℝ)^6351
        have hw : |(5265372607/10000000000 : ℝ)|=(5265372607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_2 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534484827/1000000000 : ℝ)*x 0 + (5265372697/10000000000 : ℝ)*x 1 + (-440282753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534484827/1000000000 : ℝ)^8399 ≤ (1746879680241/4000000000000 : ℝ)^6351 := by
    have hnat : (534484827 : ℕ)^8399*4000000000000^6351 ≤ 1746879680241^6351*1000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534484827 1000000000 1746879680241 4000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265372697/10000000000 : ℝ)^8399 ≤ (42815268338183/100000000000000 : ℝ)^6351 := by
    have hnat : (5265372697 : ℕ)^8399*100000000000000^6351 ≤ 42815268338183^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265372697 10000000000 42815268338183 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440282753/2000000000 : ℝ)^8399 ≤ (13512739643261/100000000000000 : ℝ)^6351 := by
    have hnat : (440282753 : ℕ)^8399*100000000000000^6351 ≤ 13512739643261^6351*2000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440282753 2000000000 13512739643261 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534484827/1000000000 : ℝ), (5265372697/10000000000 : ℝ), (-440282753/2000000000 : ℝ)] ![(1746879680241/4000000000000 : ℝ), (42815268338183/100000000000000 : ℝ), (13512739643261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534484827/1000000000 : ℝ)|^8399 ≤ (1746879680241/4000000000000 : ℝ)^6351
        have hw : |(534484827/1000000000 : ℝ)|=(534484827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265372697/10000000000 : ℝ)|^8399 ≤ (42815268338183/100000000000000 : ℝ)^6351
        have hw : |(5265372697/10000000000 : ℝ)|=(5265372697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440282753/2000000000 : ℝ)|^8399 ≤ (13512739643261/100000000000000 : ℝ)^6351
        have hw : |(-440282753/2000000000 : ℝ)|=(440282753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_3 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088915859/2500000000 : ℝ)*x 0 + (2114345121/5000000000 : ℝ)*x 1 + (4486373/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088915859/2500000000 : ℝ)^8399 ≤ (16658295412149/50000000000000 : ℝ)^6351 := by
    have hnat : (1088915859 : ℕ)^8399*50000000000000^6351 ≤ 16658295412149^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088915859 2500000000 16658295412149 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114345121/5000000000 : ℝ)^8399 ≤ (32038257814037/100000000000000 : ℝ)^6351 := by
    have hnat : (2114345121 : ℕ)^8399*100000000000000^6351 ≤ 32038257814037^6351*5000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114345121 5000000000 32038257814037 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486373/10000000 : ℝ)^8399 ≤ (34645151351589/100000000000000 : ℝ)^6351 := by
    have hnat : (4486373 : ℕ)^8399*100000000000000^6351 ≤ 34645151351589^6351*10000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486373 10000000 34645151351589 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088915859/2500000000 : ℝ), (2114345121/5000000000 : ℝ), (4486373/10000000 : ℝ)] ![(16658295412149/50000000000000 : ℝ), (32038257814037/100000000000000 : ℝ), (34645151351589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088915859/2500000000 : ℝ)|^8399 ≤ (16658295412149/50000000000000 : ℝ)^6351
        have hw : |(1088915859/2500000000 : ℝ)|=(1088915859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114345121/5000000000 : ℝ)|^8399 ≤ (32038257814037/100000000000000 : ℝ)^6351
        have hw : |(2114345121/5000000000 : ℝ)|=(2114345121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486373/10000000 : ℝ)|^8399 ≤ (34645151351589/100000000000000 : ℝ)^6351
        have hw : |(4486373/10000000 : ℝ)|=(4486373/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_4 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267066693/1250000000 : ℝ)*x 0 + (1316425583/2500000000 : ℝ)*x 1 + (5392957473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267066693/1250000000 : ℝ)^8399 ≤ (1623573508343/12500000000000 : ℝ)^6351 := by
    have hnat : (267066693 : ℕ)^8399*12500000000000^6351 ≤ 1623573508343^6351*1250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267066693 1250000000 1623573508343 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316425583/2500000000 : ℝ)^8399 ≤ (42818813146233/100000000000000 : ℝ)^6351 := by
    have hnat : (1316425583 : ℕ)^8399*100000000000000^6351 ≤ 42818813146233^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316425583 2500000000 42818813146233 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392957473/10000000000 : ℝ)^8399 ≤ (883851975299/2000000000000 : ℝ)^6351 := by
    have hnat : (5392957473 : ℕ)^8399*2000000000000^6351 ≤ 883851975299^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392957473 10000000000 883851975299 2000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267066693/1250000000 : ℝ), (1316425583/2500000000 : ℝ), (5392957473/10000000000 : ℝ)] ![(1623573508343/12500000000000 : ℝ), (42818813146233/100000000000000 : ℝ), (883851975299/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267066693/1250000000 : ℝ)|^8399 ≤ (1623573508343/12500000000000 : ℝ)^6351
        have hw : |(-267066693/1250000000 : ℝ)|=(267066693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316425583/2500000000 : ℝ)|^8399 ≤ (42818813146233/100000000000000 : ℝ)^6351
        have hw : |(1316425583/2500000000 : ℝ)|=(1316425583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392957473/10000000000 : ℝ)|^8399 ≤ (883851975299/2000000000000 : ℝ)^6351
        have hw : |(5392957473/10000000000 : ℝ)|=(5392957473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_5 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312291403/10000000000 : ℝ)*x 0 + (-103691431/500000000 : ℝ)*x 1 + (1348239363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312291403/10000000000 : ℝ)^8399 ≤ (8664107621273/20000000000000 : ℝ)^6351 := by
    have hnat : (5312291403 : ℕ)^8399*20000000000000^6351 ≤ 8664107621273^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312291403 10000000000 8664107621273 20000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103691431/500000000 : ℝ)^8399 ≤ (390214479527/3125000000000 : ℝ)^6351 := by
    have hnat : (103691431 : ℕ)^8399*3125000000000^6351 ≤ 390214479527^6351*500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103691431 500000000 390214479527 3125000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348239363/2500000000 : ℝ)^8399 ≤ (22096299268687/50000000000000 : ℝ)^6351 := by
    have hnat : (1348239363 : ℕ)^8399*50000000000000^6351 ≤ 22096299268687^6351*2500000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348239363 2500000000 22096299268687 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312291403/10000000000 : ℝ), (-103691431/500000000 : ℝ), (1348239363/2500000000 : ℝ)] ![(8664107621273/20000000000000 : ℝ), (390214479527/3125000000000 : ℝ), (22096299268687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312291403/10000000000 : ℝ)|^8399 ≤ (8664107621273/20000000000000 : ℝ)^6351
        have hw : |(5312291403/10000000000 : ℝ)|=(5312291403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103691431/500000000 : ℝ)|^8399 ≤ (390214479527/3125000000000 : ℝ)^6351
        have hw : |(-103691431/500000000 : ℝ)|=(103691431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348239363/2500000000 : ℝ)|^8399 ≤ (22096299268687/50000000000000 : ℝ)^6351
        have hw : |(1348239363/2500000000 : ℝ)|=(1348239363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_6 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106245821/200000000 : ℝ)*x 0 + (5392957877/10000000000 : ℝ)*x 1 + (-51845713/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106245821/200000000 : ℝ)^8399 ≤ (2166026714973/5000000000000 : ℝ)^6351 := by
    have hnat : (106245821 : ℕ)^8399*5000000000000^6351 ≤ 2166026714973^6351*200000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106245821 200000000 2166026714973 5000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392957877/10000000000 : ℝ)^8399 ≤ (44192603143087/100000000000000 : ℝ)^6351 := by
    have hnat : (5392957877 : ℕ)^8399*100000000000000^6351 ≤ 44192603143087^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392957877 10000000000 44192603143087 100000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51845713/250000000 : ℝ)^8399 ≤ (1560857818573/12500000000000 : ℝ)^6351 := by
    have hnat : (51845713 : ℕ)^8399*12500000000000^6351 ≤ 1560857818573^6351*250000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51845713 250000000 1560857818573 12500000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106245821/200000000 : ℝ), (5392957877/10000000000 : ℝ), (-51845713/250000000 : ℝ)] ![(2166026714973/5000000000000 : ℝ), (44192603143087/100000000000000 : ℝ), (1560857818573/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106245821/200000000 : ℝ)|^8399 ≤ (2166026714973/5000000000000 : ℝ)^6351
        have hw : |(106245821/200000000 : ℝ)|=(106245821/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392957877/10000000000 : ℝ)|^8399 ≤ (44192603143087/100000000000000 : ℝ)^6351
        have hw : |(5392957877/10000000000 : ℝ)|=(5392957877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51845713/250000000 : ℝ)|^8399 ≤ (1560857818573/12500000000000 : ℝ)^6351
        have hw : |(-51845713/250000000 : ℝ)|=(51845713/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1206_s5_7 (p : ℝ) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355673977/10000000000 : ℝ)*x 0 + (35885677/80000000 : ℝ)*x 1 + (4229355717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355673977/10000000000 : ℝ)^8399 ≤ (16658348726447/50000000000000 : ℝ)^6351 := by
    have hnat : (4355673977 : ℕ)^8399*50000000000000^6351 ≤ 16658348726447^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355673977 10000000000 16658348726447 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35885677/80000000 : ℝ)^8399 ≤ (17319188394189/50000000000000 : ℝ)^6351 := by
    have hnat : (35885677 : ℕ)^8399*50000000000000^6351 ≤ 17319188394189^6351*80000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35885677 80000000 17319188394189 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229355717/10000000000 : ℝ)^8399 ≤ (16022462873699/50000000000000 : ℝ)^6351 := by
    have hnat : (4229355717 : ℕ)^8399*50000000000000^6351 ≤ 16022462873699^6351*10000000000^8399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229355717 10000000000 16022462873699 50000000000000 8399 6351 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8399/2048 : ℝ)) 8399 6351 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355673977/10000000000 : ℝ), (35885677/80000000 : ℝ), (4229355717/10000000000 : ℝ)] ![(16658348726447/50000000000000 : ℝ), (17319188394189/50000000000000 : ℝ), (16022462873699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355673977/10000000000 : ℝ)|^8399 ≤ (16658348726447/50000000000000 : ℝ)^6351
        have hw : |(4355673977/10000000000 : ℝ)|=(4355673977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35885677/80000000 : ℝ)|^8399 ≤ (17319188394189/50000000000000 : ℝ)^6351
        have hw : |(35885677/80000000 : ℝ)|=(35885677/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229355717/10000000000 : ℝ)|^8399 ≤ (16022462873699/50000000000000 : ℝ)^6351
        have hw : |(4229355717/10000000000 : ℝ)|=(4229355717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1206_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5703/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2823/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11291/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11291/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11291/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11291/100000 : ℝ) ^ (4199/1024 : ℝ) ≤ (52204485756641/400000000000000000 : ℝ) := by
    have hpowers : (11291/100000 : ℝ)^4199 ≤ (52204485756641/400000000000000000 : ℝ)^1024 := by
      have hnat : (11291 : ℕ)^4199*400000000000000000^1024 ≤ 52204485756641^1024*100000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11291 100000 52204485756641 400000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11291/100000 : ℝ)) (X := (52204485756641/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4199/1024 : ℝ) ≤ (3374967176889153/10000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4199 ≤ (3374967176889153/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4199*10000000000000000000^1024 ≤ 3374967176889153^1024*20000^4199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 3374967176889153 10000000000000000000 4199 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (3374967176889153/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (200052204485756641/200000000000000000 : ℝ) ≤ (10000636486292501/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (200052204485756641/200000000000000000 : ℝ)^1024 ≤ (10000636486292501/10000000000000000 : ℝ)^4199 := by
      have hnat : (200052204485756641 : ℕ)^1024*10000000000000000^4199 ≤ 10000636486292501^4199*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200052204485756641 200000000000000000 10000636486292501 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000636486292501/10000000000000000 : ℝ)) (X := (200052204485756641/200000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002340039660402589/5000000000000000000 : ℝ) ≤ (250028527944147/250000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (5002340039660402589/5000000000000000000 : ℝ)^1024 ≤ (250028527944147/250000000000000 : ℝ)^4199 := by
      have hnat : (5002340039660402589 : ℕ)^1024*250000000000000^4199 ≤ 250028527944147^4199*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002340039660402589 5000000000000000000 250028527944147 250000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250028527944147/250000000000000 : ℝ)) (X := (5002340039660402589/5000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003374967176889153/5000000000000000000 : ℝ) ≤ (10001645749239259/10000000000000000 : ℝ) ^ (4199/1024 : ℝ) := by
    have hpowers : (5003374967176889153/5000000000000000000 : ℝ)^1024 ≤ (10001645749239259/10000000000000000 : ℝ)^4199 := by
      have hnat : (5003374967176889153 : ℕ)^1024*10000000000000000^4199 ≤ 10001645749239259^4199*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003374967176889153 5000000000000000000 10001645749239259 10000000000000000 1024 4199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001645749239259/10000000000000000 : ℝ)) (X := (5003374967176889153/5000000000000000000 : ℝ)) (by norm_num) 4199 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52204485756641/400000000000000000 : ℝ) ≤ ((14715239113856639183/14720000000000000000 : ℝ)+2*(504631473379/294400000000000 : ℝ)*(11291/100000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (14715239113856639183/14720000000000000000 : ℝ)+2*(504631473379/294400000000000 : ℝ)*(11291/100000 : ℝ)=(10000636486292501/10000000000000000 : ℝ) by norm_num, show 1+2*(52204485756641/400000000000000000 : ℝ)=(200052204485756641/200000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3374967176889153/10000000000000000000 : ℝ)+(52204485756641/400000000000000000 : ℝ) ≤ ((14715239113856639183/14720000000000000000 : ℝ)+(504631473379/294400000000000 : ℝ)*((2847/20000 : ℝ)+(11291/100000 : ℝ)))^(4199/1024 : ℝ) := by
    rw [show (14715239113856639183/14720000000000000000 : ℝ)+(504631473379/294400000000000 : ℝ)*((2847/20000 : ℝ)+(11291/100000 : ℝ))=(250028527944147/250000000000000 : ℝ) by norm_num, show 1+(3374967176889153/10000000000000000000 : ℝ)+(52204485756641/400000000000000000 : ℝ)=(5002340039660402589/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3374967176889153/10000000000000000000 : ℝ) ≤ ((14715239113856639183/14720000000000000000 : ℝ)+2*(504631473379/294400000000000 : ℝ)*(2847/20000 : ℝ))^(4199/1024 : ℝ) := by
    rw [show (14715239113856639183/14720000000000000000 : ℝ)+2*(504631473379/294400000000000 : ℝ)*(2847/20000 : ℝ)=(10001645749239259/10000000000000000 : ℝ) by norm_num, show 1+2*(3374967176889153/10000000000000000000 : ℝ)=(5003374967176889153/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14715239113856639183/14720000000000000000 : ℝ)*(X 1 0+X 2 0)+(504631473379/294400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (14715239113856639183/14720000000000000000 : ℝ)) (alpha := (504631473379/294400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14715239113856639183/14720000000000000000 : ℝ)*(X 0 1+X 2 1)+(504631473379/294400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (14715239113856639183/14720000000000000000 : ℝ)) (alpha := (504631473379/294400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14715239113856639183/14720000000000000000 : ℝ)*(X 0 2+X 1 2)+(504631473379/294400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4199/1024 : ℝ)) (lo := (11291/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (14715239113856639183/14720000000000000000 : ℝ)) (alpha := (504631473379/294400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136528811/10000000000 : ℝ)*X 0 0+(674161023/1250000000 : ℝ)*X 0 1+(5265372597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334053019/625000000 : ℝ)*X 1 0+(-1100706919/5000000000 : ℝ)*X 1 1+(5265372607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534484827/1000000000 : ℝ)*X 2 0+(5265372697/10000000000 : ℝ)*X 2 1+(-440282753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088915859/2500000000 : ℝ)*X 0 0+(2114345121/5000000000 : ℝ)*X 0 1+(4486373/10000000 : ℝ)*X 0 2+(1088915859/2500000000 : ℝ)*X 1 0+(2114345121/5000000000 : ℝ)*X 1 1+(4486373/10000000 : ℝ)*X 1 2+(1088915859/2500000000 : ℝ)*X 2 0+(2114345121/5000000000 : ℝ)*X 2 1+(4486373/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267066693/1250000000 : ℝ)*X 0 0+(1316425583/2500000000 : ℝ)*X 0 1+(5392957473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312291403/10000000000 : ℝ)*X 1 0+(-103691431/500000000 : ℝ)*X 1 1+(1348239363/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106245821/200000000 : ℝ)*X 2 0+(5392957877/10000000000 : ℝ)*X 2 1+(-51845713/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355673977/10000000000 : ℝ)*X 0 0+(35885677/80000000 : ℝ)*X 0 1+(4229355717/10000000000 : ℝ)*X 0 2+(4355673977/10000000000 : ℝ)*X 1 0+(35885677/80000000 : ℝ)*X 1 1+(4229355717/10000000000 : ℝ)*X 1 2+(4355673977/10000000000 : ℝ)*X 2 0+(35885677/80000000 : ℝ)*X 2 1+(4229355717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1206_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (112537508556447996361136823/36800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162294067/20000000000000 : ℝ)*(base19) + (177127329/25000000000000 : ℝ)*(base23) + (25914139/100000000000000 : ℝ)*(upper3) + (5690179/20000000000000 : ℝ)*(upper4) + (95947887/100000000000000 : ℝ)*(upper5) + (584923449737973/10000000000000 : ℝ)*(major0) + (584923449737973/10000000000000 : ℝ)*(major1) + (584923449737973/10000000000000 : ℝ)*(major2) + (781768032192853/10000000000000 : ℝ)*(sp0) + (1954427051359369/25000000000000 : ℝ)*(sp1) + (1563541661679699/20000000000000 : ℝ)*(sp2) + (776150204236643/20000000000000 : ℝ)*(sp3) + (358687241/1250000000000 : ℝ)*(sp4) + (8854732277/100000000000000 : ℝ)*(sp7) + (970189968978873/25000000000000 : ℝ)*(f.failure) + (7817709016907811/100000000000000 : ℝ)*(f.sum) + (1012727193601/1472000000000000000000000000 : ℝ)*base66 + (119914759457441133/6400000000000000000000000000000 : ℝ)*base67 + (44184840583841133/6400000000000000000000000000000 : ℝ)*base69 + (51591569454241133/6400000000000000000000000000000 : ℝ)*base71 + (6990703264257/1472000000000000000000000000 : ℝ)*base74 + (12589355140958867/6400000000000000000000000000000 : ℝ)*base76 + (81705406599841133/6400000000000000000000000000000 : ℝ)*base77 + (36460548033441133/6400000000000000000000000000000 : ℝ)*base79 + (4449630390081/1472000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4287651/625000000000000000000 : ℝ)*base89 + (4287651/625000000000000000000 : ℝ)*base91 + (4287651/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1624119461109669246981/640000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53211221/6250000000000 : ℝ)*(base19) + (1146551341/100000000000000 : ℝ)*(base23) + (360190223/100000000000000 : ℝ)*(lower4) + (12349809/100000000000000 : ℝ)*(lower5) + (5879540125506619/100000000000000 : ℝ)*(major0) + (5879540125506619/100000000000000 : ℝ)*(major1) + (5879540125506619/100000000000000 : ℝ)*(major2) + (29449573389/100000000000000 : ℝ)*(sp1) + (52181121489/100000000000000 : ℝ)*(sp2) + (7339578243/100000000000000 : ℝ)*(sp3) + (1571642715968681/20000000000000 : ℝ)*(sp4) + (7858183278890479/100000000000000 : ℝ)*(sp5) + (314326410086823/4000000000000 : ℝ)*(sp6) + (3900859247002027/100000000000000 : ℝ)*(sp7) + (3900866586580269/100000000000000 : ℝ)*(f.failure) + (1571642715968681/20000000000000 : ℝ)*(f.sum) + (340478558807/640000000000000000000000000 : ℝ)*base65 + (606102927530899901/64000000000000000000000000000000 : ℝ)*base68 + (373093374357100099/64000000000000000000000000000000 : ℝ)*base69 + (16266769813100099/64000000000000000000000000000000 : ℝ)*base71 + (3899170536873/640000000000000000000000000 : ℝ)*base74 + (364956474133100099/64000000000000000000000000000000 : ℝ)*base75 + (693934413354899901/64000000000000000000000000000000 : ℝ)*base78 + (1240415545002899901/64000000000000000000000000000000 : ℝ)*base80 + (1904184012073/640000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (15645503/2500000000000000000000 : ℝ)*base89 + (15645503/2500000000000000000000 : ℝ)*base91 + (15645503/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1206_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11291/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1206_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1206_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1206_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1206_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1206_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4199/1024 : ℝ) ≤ p) (hpb : p ≤ (8399/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37680987/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16319/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5703/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1206_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

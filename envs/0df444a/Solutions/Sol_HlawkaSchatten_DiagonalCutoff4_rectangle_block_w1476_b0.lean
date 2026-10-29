-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1476_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:46.835832+00:00
-- url     : https://prove2.me/submissions/0b2864e3-2ec0-4737-a4e9-7327867c0432

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
theorem support_rectangle_w1476_s0_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-431172839/2500000000 : ℝ)*x 0 + (2970545149/5000000000 : ℝ)*x 1 + (2419809633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431172839/2500000000 : ℝ)^4449 ≤ (5098880221809/50000000000000 : ℝ)^3425 := by
    have hnat : (431172839 : ℕ)^4449*50000000000000^3425 ≤ 5098880221809^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431172839 2500000000 5098880221809 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2970545149/5000000000 : ℝ)^4449 ≤ (25423017078543/50000000000000 : ℝ)^3425 := by
    have hnat : (2970545149 : ℕ)^4449*50000000000000^3425 ≤ 25423017078543^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2970545149 5000000000 25423017078543 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419809633/5000000000 : ℝ)^4449 ≤ (38956205377011/100000000000000 : ℝ)^3425 := by
    have hnat : (2419809633 : ℕ)^4449*100000000000000^3425 ≤ 38956205377011^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419809633 5000000000 38956205377011 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431172839/2500000000 : ℝ), (2970545149/5000000000 : ℝ), (2419809633/5000000000 : ℝ)] ![(5098880221809/50000000000000 : ℝ), (25423017078543/50000000000000 : ℝ), (38956205377011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431172839/2500000000 : ℝ)|^4449 ≤ (5098880221809/50000000000000 : ℝ)^3425
        have hw : |(-431172839/2500000000 : ℝ)|=(431172839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2970545149/5000000000 : ℝ)|^4449 ≤ (25423017078543/50000000000000 : ℝ)^3425
        have hw : |(2970545149/5000000000 : ℝ)|=(2970545149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2419809633/5000000000 : ℝ)|^4449 ≤ (38956205377011/100000000000000 : ℝ)^3425
        have hw : |(2419809633/5000000000 : ℝ)|=(2419809633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2742927231/5000000000 : ℝ)*x 0 + (-2345015731/10000000000 : ℝ)*x 1 + (302476199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2742927231/5000000000 : ℝ)^4449 ≤ (45844161304191/100000000000000 : ℝ)^3425 := by
    have hnat : (2742927231 : ℕ)^4449*100000000000000^3425 ≤ 45844161304191^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742927231 5000000000 45844161304191 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2345015731/10000000000 : ℝ)^4449 ≤ (189995427081/1250000000000 : ℝ)^3425 := by
    have hnat : (2345015731 : ℕ)^4449*1250000000000^3425 ≤ 189995427081^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345015731 10000000000 189995427081 1250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302476199/625000000 : ℝ)^4449 ≤ (608690695619/1562500000000 : ℝ)^3425 := by
    have hnat : (302476199 : ℕ)^4449*1562500000000^3425 ≤ 608690695619^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302476199 625000000 608690695619 1562500000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2742927231/5000000000 : ℝ), (-2345015731/10000000000 : ℝ), (302476199/625000000 : ℝ)] ![(45844161304191/100000000000000 : ℝ), (189995427081/1250000000000 : ℝ), (608690695619/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2742927231/5000000000 : ℝ)|^4449 ≤ (45844161304191/100000000000000 : ℝ)^3425
        have hw : |(2742927231/5000000000 : ℝ)|=(2742927231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2345015731/10000000000 : ℝ)|^4449 ≤ (189995427081/1250000000000 : ℝ)^3425
        have hw : |(-2345015731/10000000000 : ℝ)|=(2345015731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(302476199/625000000 : ℝ)|^4449 ≤ (608690695619/1562500000000 : ℝ)^3425
        have hw : |(302476199/625000000 : ℝ)|=(302476199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (171432959/312500000 : ℝ)*x 0 + (4839618999/10000000000 : ℝ)*x 1 + (-2345015669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (171432959/312500000 : ℝ)^4449 ≤ (45844163757487/100000000000000 : ℝ)^3425 := by
    have hnat : (171432959 : ℕ)^4449*100000000000000^3425 ≤ 45844163757487^3425*312500000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171432959 312500000 45844163757487 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4839618999/10000000000 : ℝ)^4449 ≤ (1217381330789/3125000000000 : ℝ)^3425 := by
    have hnat : (4839618999 : ℕ)^4449*3125000000000^3425 ≤ 1217381330789^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839618999 10000000000 1217381330789 3125000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2345015669/10000000000 : ℝ)^4449 ≤ (3799908411117/25000000000000 : ℝ)^3425 := by
    have hnat : (2345015669 : ℕ)^4449*25000000000000^3425 ≤ 3799908411117^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345015669 10000000000 3799908411117 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(171432959/312500000 : ℝ), (4839618999/10000000000 : ℝ), (-2345015669/10000000000 : ℝ)] ![(45844163757487/100000000000000 : ℝ), (1217381330789/3125000000000 : ℝ), (3799908411117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(171432959/312500000 : ℝ)|^4449 ≤ (45844163757487/100000000000000 : ℝ)^3425
        have hw : |(171432959/312500000 : ℝ)|=(171432959/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4839618999/10000000000 : ℝ)|^4449 ≤ (1217381330789/3125000000000 : ℝ)^3425
        have hw : |(4839618999/10000000000 : ℝ)|=(4839618999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2345015669/10000000000 : ℝ)|^4449 ≤ (3799908411117/25000000000000 : ℝ)^3425
        have hw : |(-2345015669/10000000000 : ℝ)|=(2345015669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (415499753/1000000000 : ℝ)*x 0 + (3091574367/10000000000 : ℝ)*x 1 + (690753373/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415499753/1000000000 : ℝ)^4449 ≤ (15977241030941/50000000000000 : ℝ)^3425 := by
    have hnat : (415499753 : ℕ)^4449*50000000000000^3425 ≤ 15977241030941^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415499753 1000000000 15977241030941 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091574367/10000000000 : ℝ)^4449 ≤ (2176479552341/10000000000000 : ℝ)^3425 := by
    have hnat : (3091574367 : ℕ)^4449*10000000000000^3425 ≤ 2176479552341^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091574367 10000000000 2176479552341 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (690753373/1250000000 : ℝ)^4449 ≤ (46280722397499/100000000000000 : ℝ)^3425 := by
    have hnat : (690753373 : ℕ)^4449*100000000000000^3425 ≤ 46280722397499^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690753373 1250000000 46280722397499 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415499753/1000000000 : ℝ), (3091574367/10000000000 : ℝ), (690753373/1250000000 : ℝ)] ![(15977241030941/50000000000000 : ℝ), (2176479552341/10000000000000 : ℝ), (46280722397499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415499753/1000000000 : ℝ)|^4449 ≤ (15977241030941/50000000000000 : ℝ)^3425
        have hw : |(415499753/1000000000 : ℝ)|=(415499753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091574367/10000000000 : ℝ)|^4449 ≤ (2176479552341/10000000000000 : ℝ)^3425
        have hw : |(3091574367/10000000000 : ℝ)|=(3091574367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(690753373/1250000000 : ℝ)|^4449 ≤ (46280722397499/100000000000000 : ℝ)^3425
        have hw : |(690753373/1250000000 : ℝ)|=(690753373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1728531759/10000000000 : ℝ)*x 0 + (973579167/2000000000 : ℝ)*x 1 + (5911796269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1728531759/10000000000 : ℝ)^4449 ≤ (1022726686319/10000000000000 : ℝ)^3425 := by
    have hnat : (1728531759 : ℕ)^4449*10000000000000^3425 ≤ 1022726686319^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1728531759 10000000000 1022726686319 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973579167/2000000000 : ℝ)^4449 ≤ (39252124228887/100000000000000 : ℝ)^3425 := by
    have hnat : (973579167 : ℕ)^4449*100000000000000^3425 ≤ 39252124228887^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973579167 2000000000 39252124228887 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911796269/10000000000 : ℝ)^4449 ≤ (25260304446727/50000000000000 : ℝ)^3425 := by
    have hnat : (5911796269 : ℕ)^4449*50000000000000^3425 ≤ 25260304446727^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911796269 10000000000 25260304446727 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1728531759/10000000000 : ℝ), (973579167/2000000000 : ℝ), (5911796269/10000000000 : ℝ)] ![(1022726686319/10000000000000 : ℝ), (39252124228887/100000000000000 : ℝ), (25260304446727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1728531759/10000000000 : ℝ)|^4449 ≤ (1022726686319/10000000000000 : ℝ)^3425
        have hw : |(-1728531759/10000000000 : ℝ)|=(1728531759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(973579167/2000000000 : ℝ)|^4449 ≤ (39252124228887/100000000000000 : ℝ)^3425
        have hw : |(973579167/2000000000 : ℝ)|=(973579167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5911796269/10000000000 : ℝ)|^4449 ≤ (25260304446727/50000000000000 : ℝ)^3425
        have hw : |(5911796269/10000000000 : ℝ)|=(5911796269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207405177/400000000 : ℝ)*x 0 + (-25456769/200000000 : ℝ)*x 1 + (5911796397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207405177/400000000 : ℝ)^4449 ≤ (2662925309809/6250000000000 : ℝ)^3425 := by
    have hnat : (207405177 : ℕ)^4449*6250000000000^3425 ≤ 2662925309809^3425*400000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207405177 400000000 2662925309809 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25456769/200000000 : ℝ)^4449 ≤ (1718146179471/25000000000000 : ℝ)^3425 := by
    have hnat : (25456769 : ℕ)^4449*25000000000000^3425 ≤ 1718146179471^3425*200000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25456769 200000000 1718146179471 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911796397/10000000000 : ℝ)^4449 ≤ (10104122062869/20000000000000 : ℝ)^3425 := by
    have hnat : (5911796397 : ℕ)^4449*20000000000000^3425 ≤ 10104122062869^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911796397 10000000000 10104122062869 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207405177/400000000 : ℝ), (-25456769/200000000 : ℝ), (5911796397/10000000000 : ℝ)] ![(2662925309809/6250000000000 : ℝ), (1718146179471/25000000000000 : ℝ), (10104122062869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207405177/400000000 : ℝ)|^4449 ≤ (2662925309809/6250000000000 : ℝ)^3425
        have hw : |(207405177/400000000 : ℝ)|=(207405177/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25456769/200000000 : ℝ)|^4449 ≤ (1718146179471/25000000000000 : ℝ)^3425
        have hw : |(-25456769/200000000 : ℝ)|=(25456769/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5911796397/10000000000 : ℝ)|^4449 ≤ (10104122062869/20000000000000 : ℝ)^3425
        have hw : |(5911796397/10000000000 : ℝ)|=(5911796397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2592564687/5000000000 : ℝ)*x 0 + (1477949061/2500000000 : ℝ)*x 1 + (-1272838769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2592564687/5000000000 : ℝ)^4449 ≤ (21303402206289/50000000000000 : ℝ)^3425 := by
    have hnat : (2592564687 : ℕ)^4449*50000000000000^3425 ≤ 21303402206289^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592564687 5000000000 21303402206289 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477949061/2500000000 : ℝ)^4449 ≤ (98673063703/195312500000 : ℝ)^3425 := by
    have hnat : (1477949061 : ℕ)^4449*195312500000^3425 ≤ 98673063703^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477949061 2500000000 98673063703 195312500000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272838769/10000000000 : ℝ)^4449 ≤ (3436293477631/50000000000000 : ℝ)^3425 := by
    have hnat : (1272838769 : ℕ)^4449*50000000000000^3425 ≤ 3436293477631^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272838769 10000000000 3436293477631 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2592564687/5000000000 : ℝ), (1477949061/2500000000 : ℝ), (-1272838769/10000000000 : ℝ)] ![(21303402206289/50000000000000 : ℝ), (98673063703/195312500000 : ℝ), (3436293477631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2592564687/5000000000 : ℝ)|^4449 ≤ (21303402206289/50000000000000 : ℝ)^3425
        have hw : |(2592564687/5000000000 : ℝ)|=(2592564687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477949061/2500000000 : ℝ)|^4449 ≤ (98673063703/195312500000 : ℝ)^3425
        have hw : |(1477949061/2500000000 : ℝ)|=(1477949061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1272838769/10000000000 : ℝ)|^4449 ≤ (3436293477631/50000000000000 : ℝ)^3425
        have hw : |(-1272838769/10000000000 : ℝ)|=(1272838769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s0_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (520435627/1250000000 : ℝ)*x 0 + (2731765299/5000000000 : ℝ)*x 1 + (1578159801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520435627/1250000000 : ℝ)^4449 ≤ (8009824352449/25000000000000 : ℝ)^3425 := by
    have hnat : (520435627 : ℕ)^4449*25000000000000^3425 ≤ 8009824352449^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520435627 1250000000 8009824352449 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731765299/5000000000 : ℝ)^4449 ≤ (45601976759557/100000000000000 : ℝ)^3425 := by
    have hnat : (2731765299 : ℕ)^4449*100000000000000^3425 ≤ 45601976759557^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731765299 5000000000 45601976759557 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1578159801/5000000000 : ℝ)^4449 ≤ (22358725807227/100000000000000 : ℝ)^3425 := by
    have hnat : (1578159801 : ℕ)^4449*100000000000000^3425 ≤ 22358725807227^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578159801 5000000000 22358725807227 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520435627/1250000000 : ℝ), (2731765299/5000000000 : ℝ), (1578159801/5000000000 : ℝ)] ![(8009824352449/25000000000000 : ℝ), (45601976759557/100000000000000 : ℝ), (22358725807227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520435627/1250000000 : ℝ)|^4449 ≤ (8009824352449/25000000000000 : ℝ)^3425
        have hw : |(520435627/1250000000 : ℝ)|=(520435627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731765299/5000000000 : ℝ)|^4449 ≤ (45601976759557/100000000000000 : ℝ)^3425
        have hw : |(2731765299/5000000000 : ℝ)|=(2731765299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1578159801/5000000000 : ℝ)|^4449 ≤ (22358725807227/100000000000000 : ℝ)^3425
        have hw : |(1578159801/5000000000 : ℝ)|=(1578159801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (147/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25959/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4447/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4447 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4447*1^1024 ≤ 0^1024*1^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4447/1024 : ℝ) ≤ (934989438029516291/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4447 ≤ (934989438029516291/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4447*50000000000000000000^1024 ≤ 934989438029516291^1024*5^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 934989438029516291 50000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (934989438029516291/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4447 := by
      have hnat : (1 : ℕ)^1024*1^4447 ≤ 1^4447*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50934989438029516291/50000000000000000000 : ℝ) ≤ (2510688258229001/2500000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50934989438029516291/50000000000000000000 : ℝ)^1024 ≤ (2510688258229001/2500000000000000 : ℝ)^4447 := by
      have hnat : (50934989438029516291 : ℕ)^1024*2500000000000000^4447 ≤ 2510688258229001^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50934989438029516291 50000000000000000000 2510688258229001 2500000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510688258229001/2500000000000000 : ℝ)) (X := (50934989438029516291/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25934989438029516291/25000000000000000000 : ℝ) ≤ (1260688258229001/1250000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (25934989438029516291/25000000000000000000 : ℝ)^1024 ≤ (1260688258229001/1250000000000000 : ℝ)^4447 := by
      have hnat : (25934989438029516291 : ℕ)^1024*1250000000000000^4447 ≤ 1260688258229001^4447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25934989438029516291 25000000000000000000 1260688258229001 1250000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260688258229001/1250000000000000 : ℝ)) (X := (25934989438029516291/25000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10688258229001/1000000000000000 : ℝ)*(0 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10688258229001/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(934989438029516291/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10688258229001/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10688258229001/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2510688258229001/2500000000000000 : ℝ) by norm_num, show 1+(934989438029516291/50000000000000000000 : ℝ)+(0 : ℝ)=(50934989438029516291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(934989438029516291/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10688258229001/1000000000000000 : ℝ)*(2/5 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10688258229001/1000000000000000 : ℝ)*(2/5 : ℝ)=(1260688258229001/1250000000000000 : ℝ) by norm_num, show 1+2*(934989438029516291/50000000000000000000 : ℝ)=(25934989438029516291/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10688258229001/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10688258229001/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10688258229001/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10688258229001/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10688258229001/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10688258229001/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-431172839/2500000000 : ℝ)*X 0 0+(2970545149/5000000000 : ℝ)*X 0 1+(2419809633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2742927231/5000000000 : ℝ)*X 1 0+(-2345015731/10000000000 : ℝ)*X 1 1+(302476199/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((171432959/312500000 : ℝ)*X 2 0+(4839618999/10000000000 : ℝ)*X 2 1+(-2345015669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((415499753/1000000000 : ℝ)*X 0 0+(3091574367/10000000000 : ℝ)*X 0 1+(690753373/1250000000 : ℝ)*X 0 2+(415499753/1000000000 : ℝ)*X 1 0+(3091574367/10000000000 : ℝ)*X 1 1+(690753373/1250000000 : ℝ)*X 1 2+(415499753/1000000000 : ℝ)*X 2 0+(3091574367/10000000000 : ℝ)*X 2 1+(690753373/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1728531759/10000000000 : ℝ)*X 0 0+(973579167/2000000000 : ℝ)*X 0 1+(5911796269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((207405177/400000000 : ℝ)*X 1 0+(-25456769/200000000 : ℝ)*X 1 1+(5911796397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2592564687/5000000000 : ℝ)*X 2 0+(1477949061/2500000000 : ℝ)*X 2 1+(-1272838769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((520435627/1250000000 : ℝ)*X 0 0+(2731765299/5000000000 : ℝ)*X 0 1+(1578159801/5000000000 : ℝ)*X 0 2+(520435627/1250000000 : ℝ)*X 1 0+(2731765299/5000000000 : ℝ)*X 1 1+(1578159801/5000000000 : ℝ)*X 1 2+(520435627/1250000000 : ℝ)*X 2 0+(2731765299/5000000000 : ℝ)*X 2 1+(1578159801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66374797730625215942847/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23898003/25000000000000 : ℝ)*(base1) + (311983107/50000000000000 : ℝ)*(base19) + (661368011/100000000000000 : ℝ)*(base23) + (26788707/50000000000000 : ℝ)*(upper3) + (40875883/50000000000000 : ℝ)*(upper5) + (329663013140051/50000000000000 : ℝ)*(major0) + (329663013140051/50000000000000 : ℝ)*(major1) + (329663013140051/50000000000000 : ℝ)*(major2) + (181575693719361/20000000000000 : ℝ)*(sp0) + (453939875778407/50000000000000 : ℝ)*(sp1) + (907879714155017/100000000000000 : ℝ)*(sp2) + (410770734088809/100000000000000 : ℝ)*(sp3) + (400503647/20000000000000 : ℝ)*(sp4) + (758856619/100000000000000 : ℝ)*(sp7) + (410771588537441/100000000000000 : ℝ)*(f.failure) + (226970093880757/25000000000000 : ℝ)*(f.sum) + (2700249594051/25000000000000000000000000000 : ℝ)*base65 + (18161433819051/50000000000000000000000000000 : ℝ)*base67 + (14360659130949/50000000000000000000000000000 : ℝ)*base70 + (96255094280949/50000000000000000000000000000 : ℝ)*base72 + (118967092044051/25000000000000000000000000000 : ℝ)*base73 + (372301130680949/50000000000000000000000000000 : ℝ)*base76 + (118243375680949/50000000000000000000000000000 : ℝ)*base78 + (380689509580949/50000000000000000000000000000 : ℝ)*base80 + (92803084794051/25000000000000000000000000000 : ℝ)*base81 + (2086489/250000000000000000000 : ℝ)*base89 + (2086489/250000000000000000000 : ℝ)*base91 + (2086489/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (238543943807009891737887/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (545310873/25000000000000 : ℝ)*(base19) + (2178321673/100000000000000 : ℝ)*(base23) + (18321777/10000000000000 : ℝ)*(base32) + (326565053/100000000000000 : ℝ)*(upper3) + (104271021/50000000000000 : ℝ)*(upper5) + (347842166478371/50000000000000 : ℝ)*(major0) + (347842166478371/50000000000000 : ℝ)*(major1) + (347842166478371/50000000000000 : ℝ)*(major2) + (5385615219/100000000000000 : ℝ)*(sp1) + (5497689521/100000000000000 : ℝ)*(sp2) + (957944901519023/100000000000000 : ℝ)*(sp4) + (119742166832539/12500000000000 : ℝ)*(sp5) + (95793722550783/10000000000000 : ℝ)*(sp6) + (433423263118091/100000000000000 : ℝ)*(sp7) + (433423446335861/100000000000000 : ℝ)*(f.failure) + (957944901519023/100000000000000 : ℝ)*(f.sum) + (16661606462371/25000000000000000000000000000 : ℝ)*base65 + (30407449712629/50000000000000000000000000000 : ℝ)*base68 + (541231182987371/50000000000000000000000000000 : ℝ)*base69 + (323925319737371/50000000000000000000000000000 : ℝ)*base71 + (80247616787629/25000000000000000000000000000 : ℝ)*base74 + (310664584337371/50000000000000000000000000000 : ℝ)*base75 + (48533934762629/50000000000000000000000000000 : ℝ)*base78 + (9728989412629/50000000000000000000000000000 : ℝ)*base80 + (172509582362371/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1825331/250000000000000000000 : ℝ)*base90 + (1825331/250000000000000000000 : ℝ)*base92 + (1825331/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1476_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (147/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25959/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1476_s1_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-944097963/5000000000 : ℝ)*x 0 + (5595662509/10000000000 : ℝ)*x 1 + (2540057097/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944097963/5000000000 : ℝ)^4449 ≤ (11470992057627/100000000000000 : ℝ)^3425 := by
    have hnat : (944097963 : ℕ)^4449*100000000000000^3425 ≤ 11470992057627^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944097963 5000000000 11470992057627 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595662509/10000000000 : ℝ)^4449 ≤ (1175992753427/2500000000000 : ℝ)^3425 := by
    have hnat : (5595662509 : ℕ)^4449*2500000000000^3425 ≤ 1175992753427^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595662509 10000000000 1175992753427 2500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2540057097/5000000000 : ℝ)^4449 ≤ (259308111183/625000000000 : ℝ)^3425 := by
    have hnat : (2540057097 : ℕ)^4449*625000000000^3425 ≤ 259308111183^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540057097 5000000000 259308111183 625000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944097963/5000000000 : ℝ), (5595662509/10000000000 : ℝ), (2540057097/5000000000 : ℝ)] ![(11470992057627/100000000000000 : ℝ), (1175992753427/2500000000000 : ℝ), (259308111183/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944097963/5000000000 : ℝ)|^4449 ≤ (11470992057627/100000000000000 : ℝ)^3425
        have hw : |(-944097963/5000000000 : ℝ)|=(944097963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595662509/10000000000 : ℝ)|^4449 ≤ (1175992753427/2500000000000 : ℝ)^3425
        have hw : |(5595662509/10000000000 : ℝ)|=(5595662509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2540057097/5000000000 : ℝ)|^4449 ≤ (259308111183/625000000000 : ℝ)^3425
        have hw : |(2540057097/5000000000 : ℝ)|=(2540057097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393324067/10000000000 : ℝ)*x 0 + (-2160950557/10000000000 : ℝ)*x 1 + (79376823/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393324067/10000000000 : ℝ)^4449 ≤ (22421129696109/50000000000000 : ℝ)^3425 := by
    have hnat : (5393324067 : ℕ)^4449*50000000000000^3425 ≤ 22421129696109^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393324067 10000000000 22421129696109 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2160950557/10000000000 : ℝ)^4449 ≤ (3417104127289/25000000000000 : ℝ)^3425 := by
    have hnat : (2160950557 : ℕ)^4449*25000000000000^3425 ≤ 3417104127289^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160950557 10000000000 3417104127289 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79376823/156250000 : ℝ)^4449 ≤ (20744662038889/50000000000000 : ℝ)^3425 := by
    have hnat : (79376823 : ℕ)^4449*50000000000000^3425 ≤ 20744662038889^3425*156250000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79376823 156250000 20744662038889 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393324067/10000000000 : ℝ), (-2160950557/10000000000 : ℝ), (79376823/156250000 : ℝ)] ![(22421129696109/50000000000000 : ℝ), (3417104127289/25000000000000 : ℝ), (20744662038889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393324067/10000000000 : ℝ)|^4449 ≤ (22421129696109/50000000000000 : ℝ)^3425
        have hw : |(5393324067/10000000000 : ℝ)|=(5393324067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2160950557/10000000000 : ℝ)|^4449 ≤ (3417104127289/25000000000000 : ℝ)^3425
        have hw : |(-2160950557/10000000000 : ℝ)|=(2160950557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79376823/156250000 : ℝ)|^4449 ≤ (20744662038889/50000000000000 : ℝ)^3425
        have hw : |(79376823/156250000 : ℝ)|=(79376823/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393325971/10000000000 : ℝ)*x 0 + (5080114577/10000000000 : ℝ)*x 1 + (-54023769/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393325971/10000000000 : ℝ)^4449 ≤ (44842279955847/100000000000000 : ℝ)^3425 := by
    have hnat : (5393325971 : ℕ)^4449*100000000000000^3425 ≤ 44842279955847^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393325971 10000000000 44842279955847 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080114577/10000000000 : ℝ)^4449 ≤ (41489301852433/100000000000000 : ℝ)^3425 := by
    have hnat : (5080114577 : ℕ)^4449*100000000000000^3425 ≤ 41489301852433^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080114577 10000000000 41489301852433 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54023769/250000000 : ℝ)^4449 ≤ (13668418177061/100000000000000 : ℝ)^3425 := by
    have hnat : (54023769 : ℕ)^4449*100000000000000^3425 ≤ 13668418177061^3425*250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54023769 250000000 13668418177061 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393325971/10000000000 : ℝ), (5080114577/10000000000 : ℝ), (-54023769/250000000 : ℝ)] ![(44842279955847/100000000000000 : ℝ), (41489301852433/100000000000000 : ℝ), (13668418177061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393325971/10000000000 : ℝ)|^4449 ≤ (44842279955847/100000000000000 : ℝ)^3425
        have hw : |(5393325971/10000000000 : ℝ)|=(5393325971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080114577/10000000000 : ℝ)|^4449 ≤ (41489301852433/100000000000000 : ℝ)^3425
        have hw : |(5080114577/10000000000 : ℝ)|=(5080114577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54023769/250000000 : ℝ)|^4449 ≤ (13668418177061/100000000000000 : ℝ)^3425
        have hw : |(-54023769/250000000 : ℝ)|=(54023769/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426271509/1000000000 : ℝ)*x 0 + (465763197/1250000000 : ℝ)*x 1 + (1216389041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426271509/1000000000 : ℝ)^4449 ≤ (4129339913827/12500000000000 : ℝ)^3425 := by
    have hnat : (426271509 : ℕ)^4449*12500000000000^3425 ≤ 4129339913827^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426271509 1000000000 4129339913827 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465763197/1250000000 : ℝ)^4449 ≤ (27737661018049/100000000000000 : ℝ)^3425 := by
    have hnat : (465763197 : ℕ)^4449*100000000000000^3425 ≤ 27737661018049^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465763197 1250000000 27737661018049 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216389041/2500000000 : ℝ)^4449 ≤ (19613809823357/50000000000000 : ℝ)^3425 := by
    have hnat : (1216389041 : ℕ)^4449*50000000000000^3425 ≤ 19613809823357^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216389041 2500000000 19613809823357 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426271509/1000000000 : ℝ), (465763197/1250000000 : ℝ), (1216389041/2500000000 : ℝ)] ![(4129339913827/12500000000000 : ℝ), (27737661018049/100000000000000 : ℝ), (19613809823357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426271509/1000000000 : ℝ)|^4449 ≤ (4129339913827/12500000000000 : ℝ)^3425
        have hw : |(426271509/1000000000 : ℝ)|=(426271509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(465763197/1250000000 : ℝ)|^4449 ≤ (27737661018049/100000000000000 : ℝ)^3425
        have hw : |(465763197/1250000000 : ℝ)|=(465763197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216389041/2500000000 : ℝ)|^4449 ≤ (19613809823357/50000000000000 : ℝ)^3425
        have hw : |(1216389041/2500000000 : ℝ)|=(1216389041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-472143741/2500000000 : ℝ)*x 0 + (5086182189/10000000000 : ℝ)*x 1 + (5589491363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (472143741/2500000000 : ℝ)^4449 ≤ (2868495824883/25000000000000 : ℝ)^3425 := by
    have hnat : (472143741 : ℕ)^4449*25000000000000^3425 ≤ 2868495824883^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472143741 2500000000 2868495824883 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5086182189/10000000000 : ℝ)^4449 ≤ (41553683155811/100000000000000 : ℝ)^3425 := by
    have hnat : (5086182189 : ℕ)^4449*100000000000000^3425 ≤ 41553683155811^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086182189 10000000000 41553683155811 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5589491363/10000000000 : ℝ)^4449 ≤ (46972333527771/100000000000000 : ℝ)^3425 := by
    have hnat : (5589491363 : ℕ)^4449*100000000000000^3425 ≤ 46972333527771^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5589491363 10000000000 46972333527771 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-472143741/2500000000 : ℝ), (5086182189/10000000000 : ℝ), (5589491363/10000000000 : ℝ)] ![(2868495824883/25000000000000 : ℝ), (41553683155811/100000000000000 : ℝ), (46972333527771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-472143741/2500000000 : ℝ)|^4449 ≤ (2868495824883/25000000000000 : ℝ)^3425
        have hw : |(-472143741/2500000000 : ℝ)|=(472143741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5086182189/10000000000 : ℝ)|^4449 ≤ (41553683155811/100000000000000 : ℝ)^3425
        have hw : |(5086182189/10000000000 : ℝ)|=(5086182189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5589491363/10000000000 : ℝ)|^4449 ≤ (46972333527771/100000000000000 : ℝ)^3425
        have hw : |(5589491363/10000000000 : ℝ)|=(5589491363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52581533/100000000 : ℝ)*x 0 + (-41289381/250000000 : ℝ)*x 1 + (87335803/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52581533/100000000 : ℝ)^4449 ≤ (4338788662937/10000000000000 : ℝ)^3425 := by
    have hnat : (52581533 : ℕ)^4449*10000000000000^3425 ≤ 4338788662937^3425*100000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52581533 100000000 4338788662937 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41289381/250000000 : ℝ)^4449 ≤ (24099448773/250000000000 : ℝ)^3425 := by
    have hnat : (41289381 : ℕ)^4449*250000000000^3425 ≤ 24099448773^3425*250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41289381 250000000 24099448773 250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87335803/156250000 : ℝ)^4449 ≤ (46972333844341/100000000000000 : ℝ)^3425 := by
    have hnat : (87335803 : ℕ)^4449*100000000000000^3425 ≤ 46972333844341^3425*156250000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87335803 156250000 46972333844341 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52581533/100000000 : ℝ), (-41289381/250000000 : ℝ), (87335803/156250000 : ℝ)] ![(4338788662937/10000000000000 : ℝ), (24099448773/250000000000 : ℝ), (46972333844341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52581533/100000000 : ℝ)|^4449 ≤ (4338788662937/10000000000000 : ℝ)^3425
        have hw : |(52581533/100000000 : ℝ)|=(52581533/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41289381/250000000 : ℝ)|^4449 ≤ (24099448773/250000000000 : ℝ)^3425
        have hw : |(-41289381/250000000 : ℝ)|=(41289381/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87335803/156250000 : ℝ)|^4449 ≤ (46972333844341/100000000000000 : ℝ)^3425
        have hw : |(87335803/156250000 : ℝ)|=(87335803/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258153339/10000000000 : ℝ)*x 0 + (2794745679/5000000000 : ℝ)*x 1 + (-330315047/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258153339/10000000000 : ℝ)^4449 ≤ (8677577409479/20000000000000 : ℝ)^3425 := by
    have hnat : (5258153339 : ℕ)^4449*20000000000000^3425 ≤ 8677577409479^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258153339 10000000000 8677577409479 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794745679/5000000000 : ℝ)^4449 ≤ (4697233347319/10000000000000 : ℝ)^3425 := by
    have hnat : (2794745679 : ℕ)^4449*10000000000000^3425 ≤ 4697233347319^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794745679 5000000000 4697233347319 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330315047/2000000000 : ℝ)^4449 ≤ (9639779471291/100000000000000 : ℝ)^3425 := by
    have hnat : (330315047 : ℕ)^4449*100000000000000^3425 ≤ 9639779471291^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330315047 2000000000 9639779471291 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258153339/10000000000 : ℝ), (2794745679/5000000000 : ℝ), (-330315047/2000000000 : ℝ)] ![(8677577409479/20000000000000 : ℝ), (4697233347319/10000000000000 : ℝ), (9639779471291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258153339/10000000000 : ℝ)|^4449 ≤ (8677577409479/20000000000000 : ℝ)^3425
        have hw : |(5258153339/10000000000 : ℝ)|=(5258153339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794745679/5000000000 : ℝ)|^4449 ≤ (4697233347319/10000000000000 : ℝ)^3425
        have hw : |(2794745679/5000000000 : ℝ)|=(2794745679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-330315047/2000000000 : ℝ)|^4449 ≤ (9639779471291/100000000000000 : ℝ)^3425
        have hw : |(-330315047/2000000000 : ℝ)|=(330315047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s1_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2131777031/5000000000 : ℝ)*x 0 + (1213036779/2500000000 : ℝ)*x 1 + (58433457/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131777031/5000000000 : ℝ)^4449 ≤ (33043165219433/100000000000000 : ℝ)^3425 := by
    have hnat : (2131777031 : ℕ)^4449*100000000000000^3425 ≤ 33043165219433^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131777031 5000000000 33043165219433 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213036779/2500000000 : ℝ)^4449 ≤ (39087247749861/100000000000000 : ℝ)^3425 := by
    have hnat : (1213036779 : ℕ)^4449*100000000000000^3425 ≤ 39087247749861^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213036779 2500000000 39087247749861 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58433457/156250000 : ℝ)^4449 ≤ (13934793505443/50000000000000 : ℝ)^3425 := by
    have hnat : (58433457 : ℕ)^4449*50000000000000^3425 ≤ 13934793505443^3425*156250000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58433457 156250000 13934793505443 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131777031/5000000000 : ℝ), (1213036779/2500000000 : ℝ), (58433457/156250000 : ℝ)] ![(33043165219433/100000000000000 : ℝ), (39087247749861/100000000000000 : ℝ), (13934793505443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131777031/5000000000 : ℝ)|^4449 ≤ (33043165219433/100000000000000 : ℝ)^3425
        have hw : |(2131777031/5000000000 : ℝ)|=(2131777031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1213036779/2500000000 : ℝ)|^4449 ≤ (39087247749861/100000000000000 : ℝ)^3425
        have hw : |(1213036779/2500000000 : ℝ)|=(1213036779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58433457/156250000 : ℝ)|^4449 ≤ (13934793505443/50000000000000 : ℝ)^3425
        have hw : |(58433457/156250000 : ℝ)|=(58433457/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25959/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (147/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (3923/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2343/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25959/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (147/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25959/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (147/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25959/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (147/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25959/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (147/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25959/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (147/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25959/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (147/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (147/6250 : ℝ) ^ (4447/1024 : ℝ) ≤ (8462939588161/100000000000000000000 : ℝ) := by
    have hpowers : (147/6250 : ℝ)^4447 ≤ (8462939588161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (147 : ℕ)^4447*100000000000000000000^1024 ≤ 8462939588161^1024*6250^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 6250 8462939588161 100000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/6250 : ℝ)) (X := (8462939588161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25959/100000 : ℝ) ^ (4447/1024 : ℝ) ≤ (143006345410043669/50000000000000000000 : ℝ) := by
    have hpowers : (25959/100000 : ℝ)^4447 ≤ (143006345410043669/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25959 : ℕ)^4447*50000000000000000000^1024 ≤ 143006345410043669^1024*100000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25959 100000 143006345410043669 50000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25959/100000 : ℝ)) (X := (143006345410043669/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000008462939588161/50000000000000000000 : ℝ) ≤ (5000000194874063/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50000008462939588161/50000000000000000000 : ℝ)^1024 ≤ (5000000194874063/5000000000000000 : ℝ)^4447 := by
      have hnat : (50000008462939588161 : ℕ)^1024*5000000000000000^4447 ≤ 5000000194874063^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000008462939588161 50000000000000000000 5000000194874063 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000194874063/5000000000000000 : ℝ)) (X := (50000008462939588161/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100286021153759675499/100000000000000000000 : ℝ) ≤ (5003289451272701/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (100286021153759675499/100000000000000000000 : ℝ)^1024 ≤ (5003289451272701/5000000000000000 : ℝ)^4447 := by
      have hnat : (100286021153759675499 : ℕ)^1024*5000000000000000^4447 ≤ 5003289451272701^4447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100286021153759675499 100000000000000000000 5003289451272701 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003289451272701/5000000000000000 : ℝ)) (X := (100286021153759675499/100000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25143006345410043669/25000000000000000000 : ℝ) ≤ (5006578707671339/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (25143006345410043669/25000000000000000000 : ℝ)^1024 ≤ (5006578707671339/5000000000000000 : ℝ)^4447 := by
      have hnat : (25143006345410043669 : ℕ)^1024*5000000000000000^4447 ≤ 5006578707671339^4447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25143006345410043669 25000000000000000000 5006578707671339 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006578707671339/5000000000000000 : ℝ)) (X := (25143006345410043669/25000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8462939588161/100000000000000000000 : ℝ) ≤ ((13113281326476979121/13115000000000000000 : ℝ)+2*(182736466591/65575000000000 : ℝ)*(147/6250 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (13113281326476979121/13115000000000000000 : ℝ)+2*(182736466591/65575000000000 : ℝ)*(147/6250 : ℝ)=(5000000194874063/5000000000000000 : ℝ) by norm_num, show 1+2*(8462939588161/100000000000000000000 : ℝ)=(50000008462939588161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(143006345410043669/50000000000000000000 : ℝ)+(8462939588161/100000000000000000000 : ℝ) ≤ ((13113281326476979121/13115000000000000000 : ℝ)+(182736466591/65575000000000 : ℝ)*((25959/100000 : ℝ)+(147/6250 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (13113281326476979121/13115000000000000000 : ℝ)+(182736466591/65575000000000 : ℝ)*((25959/100000 : ℝ)+(147/6250 : ℝ))=(5003289451272701/5000000000000000 : ℝ) by norm_num, show 1+(143006345410043669/50000000000000000000 : ℝ)+(8462939588161/100000000000000000000 : ℝ)=(100286021153759675499/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(143006345410043669/50000000000000000000 : ℝ) ≤ ((13113281326476979121/13115000000000000000 : ℝ)+2*(182736466591/65575000000000 : ℝ)*(25959/100000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (13113281326476979121/13115000000000000000 : ℝ)+2*(182736466591/65575000000000 : ℝ)*(25959/100000 : ℝ)=(5006578707671339/5000000000000000 : ℝ) by norm_num, show 1+2*(143006345410043669/50000000000000000000 : ℝ)=(25143006345410043669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13113281326476979121/13115000000000000000 : ℝ)*(X 1 0+X 2 0)+(182736466591/65575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (147/6250 : ℝ)) (hi := (25959/100000 : ℝ)) (c := (13113281326476979121/13115000000000000000 : ℝ)) (alpha := (182736466591/65575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13113281326476979121/13115000000000000000 : ℝ)*(X 0 1+X 2 1)+(182736466591/65575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (147/6250 : ℝ)) (hi := (25959/100000 : ℝ)) (c := (13113281326476979121/13115000000000000000 : ℝ)) (alpha := (182736466591/65575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13113281326476979121/13115000000000000000 : ℝ)*(X 0 2+X 1 2)+(182736466591/65575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (147/6250 : ℝ)) (hi := (25959/100000 : ℝ)) (c := (13113281326476979121/13115000000000000000 : ℝ)) (alpha := (182736466591/65575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-944097963/5000000000 : ℝ)*X 0 0+(5595662509/10000000000 : ℝ)*X 0 1+(2540057097/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5393324067/10000000000 : ℝ)*X 1 0+(-2160950557/10000000000 : ℝ)*X 1 1+(79376823/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5393325971/10000000000 : ℝ)*X 2 0+(5080114577/10000000000 : ℝ)*X 2 1+(-54023769/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((426271509/1000000000 : ℝ)*X 0 0+(465763197/1250000000 : ℝ)*X 0 1+(1216389041/2500000000 : ℝ)*X 0 2+(426271509/1000000000 : ℝ)*X 1 0+(465763197/1250000000 : ℝ)*X 1 1+(1216389041/2500000000 : ℝ)*X 1 2+(426271509/1000000000 : ℝ)*X 2 0+(465763197/1250000000 : ℝ)*X 2 1+(1216389041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-472143741/2500000000 : ℝ)*X 0 0+(5086182189/10000000000 : ℝ)*X 0 1+(5589491363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52581533/100000000 : ℝ)*X 1 0+(-41289381/250000000 : ℝ)*X 1 1+(87335803/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258153339/10000000000 : ℝ)*X 2 0+(2794745679/5000000000 : ℝ)*X 2 1+(-330315047/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2131777031/5000000000 : ℝ)*X 0 0+(1213036779/2500000000 : ℝ)*X 0 1+(58433457/156250000 : ℝ)*X 0 2+(2131777031/5000000000 : ℝ)*X 1 0+(1213036779/2500000000 : ℝ)*X 1 1+(58433457/156250000 : ℝ)*X 1 2+(2131777031/5000000000 : ℝ)*X 2 0+(1213036779/2500000000 : ℝ)*X 2 1+(58433457/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20055160571325365428104561/2687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57809339/5000000000000 : ℝ)*(base19) + (856414833/50000000000000 : ℝ)*(base23) + (65952617/50000000000000 : ℝ)*(upper3) + (34553057/50000000000000 : ℝ)*(upper4) + (21611801/25000000000000 : ℝ)*(upper5) + (352167953701711/25000000000000 : ℝ)*(major0) + (352167953701711/25000000000000 : ℝ)*(major1) + (352167953701711/25000000000000 : ℝ)*(major2) + (1939698311411959/100000000000000 : ℝ)*(sp0) + (484928792280997/25000000000000 : ℝ)*(sp1) + (1939714612481103/100000000000000 : ℝ)*(sp2) + (219405217587821/25000000000000 : ℝ)*(sp3) + (1801389881/10000000000000 : ℝ)*(sp4) + (6185205447/100000000000000 : ℝ)*(sp7) + (219406763889183/25000000000000 : ℝ)*(f.failure) + (1939716325310769/100000000000000 : ℝ)*(f.sum) + (205022774107/26875000000000000000000000 : ℝ)*base65 + (12422138710414771/5375000000000000000000000000000 : ℝ)*base67 + (29171843511289771/5375000000000000000000000000000 : ℝ)*base69 + (93710790965539771/5375000000000000000000000000000 : ℝ)*base71 + (15709145217/6718750000000000000000000 : ℝ)*base74 + (63971185263789771/5375000000000000000000000000000 : ℝ)*base75 + (19701304324164771/5375000000000000000000000000000 : ℝ)*base77 + (67319710831664771/5375000000000000000000000000000 : ℝ)*base79 + (89029608897/26875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (89593/62500000000000000000 : ℝ)*base90 + (89593/62500000000000000000 : ℝ)*base92 + (89593/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26480356785237642405637803/7625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (667887219/100000000000000 : ℝ)*(base19) + (360511731/50000000000000 : ℝ)*(base23) + (97420731/100000000000000 : ℝ)*(upper3) + (1697373/12500000000000 : ℝ)*(lower4) + (65413357/100000000000000 : ℝ)*(upper5) + (721450648918883/50000000000000 : ℝ)*(major0) + (721450648918883/50000000000000 : ℝ)*(major1) + (721450648918883/50000000000000 : ℝ)*(major2) + (199178873/5000000000000 : ℝ)*(sp1) + (4472686269/100000000000000 : ℝ)*(sp2) + (79473994429527/4000000000000 : ℝ)*(sp4) + (248355651159187/12500000000000 : ℝ)*(sp5) + (496711166757111/25000000000000 : ℝ)*(sp6) + (89895261917623/10000000000000 : ℝ)*(sp7) + (89895261917623/10000000000000 : ℝ)*(f.failure) + (79473994429527/4000000000000 : ℝ)*(f.sum) + (52699677277/19062500000000000000000000 : ℝ)*base66 + (40046537352162601/15250000000000000000000000000000 : ℝ)*base67 + (77945840249662601/15250000000000000000000000000000 : ℝ)*base69 + (31892213304087399/15250000000000000000000000000000 : ℝ)*base72 + (199237735317/76250000000000000000000000 : ℝ)*base73 + (93590384412087399/15250000000000000000000000000000 : ℝ)*base76 + (22554639752837399/15250000000000000000000000000000 : ℝ)*base78 + (1059305270337399/15250000000000000000000000000000 : ℝ)*base80 + (469523562517/76250000000000000000000000 : ℝ)*base81 + (76833/25000000000000000000 : ℝ)*base90 + (76833/25000000000000000000 : ℝ)*base92 + (76833/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1476_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25959/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (147/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3923/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2343/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1476_s2_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917171111/10000000000 : ℝ)*x 0 + (5470406389/10000000000 : ℝ)*x 1 + (1037334777/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917171111/10000000000 : ℝ)^4449 ≤ (11700170386591/100000000000000 : ℝ)^3425 := by
    have hnat : (1917171111 : ℕ)^4449*100000000000000^3425 ≤ 11700170386591^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917171111 10000000000 11700170386591 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470406389/10000000000 : ℝ)^4449 ≤ (45676538572403/100000000000000 : ℝ)^3425 := by
    have hnat : (5470406389 : ℕ)^4449*100000000000000^3425 ≤ 45676538572403^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470406389 10000000000 45676538572403 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037334777/2000000000 : ℝ)^4449 ≤ (10655822757291/25000000000000 : ℝ)^3425 := by
    have hnat : (1037334777 : ℕ)^4449*25000000000000^3425 ≤ 10655822757291^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037334777 2000000000 10655822757291 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917171111/10000000000 : ℝ), (5470406389/10000000000 : ℝ), (1037334777/2000000000 : ℝ)] ![(11700170386591/100000000000000 : ℝ), (45676538572403/100000000000000 : ℝ), (10655822757291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917171111/10000000000 : ℝ)|^4449 ≤ (11700170386591/100000000000000 : ℝ)^3425
        have hw : |(-1917171111/10000000000 : ℝ)|=(1917171111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470406389/10000000000 : ℝ)|^4449 ≤ (45676538572403/100000000000000 : ℝ)^3425
        have hw : |(5470406389/10000000000 : ℝ)|=(5470406389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037334777/2000000000 : ℝ)|^4449 ≤ (10655822757291/25000000000000 : ℝ)^3425
        have hw : |(1037334777/2000000000 : ℝ)|=(1037334777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680937897/5000000000 : ℝ)*x 0 + (-1031787641/5000000000 : ℝ)*x 1 + (518667391/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680937897/5000000000 : ℝ)^4449 ≤ (44502907434477/100000000000000 : ℝ)^3425 := by
    have hnat : (2680937897 : ℕ)^4449*100000000000000^3425 ≤ 44502907434477^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680937897 5000000000 44502907434477 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031787641/5000000000 : ℝ)^4449 ≤ (12873801256751/100000000000000 : ℝ)^3425 := by
    have hnat : (1031787641 : ℕ)^4449*100000000000000^3425 ≤ 12873801256751^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031787641 5000000000 12873801256751 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518667391/1000000000 : ℝ)^4449 ≤ (21311645648017/50000000000000 : ℝ)^3425 := by
    have hnat : (518667391 : ℕ)^4449*50000000000000^3425 ≤ 21311645648017^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518667391 1000000000 21311645648017 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680937897/5000000000 : ℝ), (-1031787641/5000000000 : ℝ), (518667391/1000000000 : ℝ)] ![(44502907434477/100000000000000 : ℝ), (12873801256751/100000000000000 : ℝ), (21311645648017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680937897/5000000000 : ℝ)|^4449 ≤ (44502907434477/100000000000000 : ℝ)^3425
        have hw : |(2680937897/5000000000 : ℝ)|=(2680937897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031787641/5000000000 : ℝ)|^4449 ≤ (12873801256751/100000000000000 : ℝ)^3425
        have hw : |(-1031787641/5000000000 : ℝ)|=(1031787641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518667391/1000000000 : ℝ)|^4449 ≤ (21311645648017/50000000000000 : ℝ)^3425
        have hw : |(518667391/1000000000 : ℝ)|=(518667391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361875807/10000000000 : ℝ)*x 0 + (1037334779/2000000000 : ℝ)*x 1 + (-515893821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361875807/10000000000 : ℝ)^4449 ≤ (8900581514927/20000000000000 : ℝ)^3425 := by
    have hnat : (5361875807 : ℕ)^4449*20000000000000^3425 ≤ 8900581514927^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361875807 10000000000 8900581514927 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037334779/2000000000 : ℝ)^4449 ≤ (5327911391989/12500000000000 : ℝ)^3425 := by
    have hnat : (1037334779 : ℕ)^4449*12500000000000^3425 ≤ 5327911391989^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037334779 2000000000 5327911391989 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515893821/2500000000 : ℝ)^4449 ≤ (6436900636479/50000000000000 : ℝ)^3425 := by
    have hnat : (515893821 : ℕ)^4449*50000000000000^3425 ≤ 6436900636479^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515893821 2500000000 6436900636479 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361875807/10000000000 : ℝ), (1037334779/2000000000 : ℝ), (-515893821/2500000000 : ℝ)] ![(8900581514927/20000000000000 : ℝ), (5327911391989/12500000000000 : ℝ), (6436900636479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361875807/10000000000 : ℝ)|^4449 ≤ (8900581514927/20000000000000 : ℝ)^3425
        have hw : |(5361875807/10000000000 : ℝ)|=(5361875807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037334779/2000000000 : ℝ)|^4449 ≤ (5327911391989/12500000000000 : ℝ)^3425
        have hw : |(1037334779/2000000000 : ℝ)|=(1037334779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515893821/2500000000 : ℝ)|^4449 ≤ (6436900636479/50000000000000 : ℝ)^3425
        have hw : |(-515893821/2500000000 : ℝ)|=(515893821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535422131/1250000000 : ℝ)*x 0 + (795971283/2000000000 : ℝ)*x 1 + (4606957153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535422131/1250000000 : ℝ)^4449 ≤ (33242867116193/100000000000000 : ℝ)^3425 := by
    have hnat : (535422131 : ℕ)^4449*100000000000000^3425 ≤ 33242867116193^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535422131 1250000000 33242867116193 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795971283/2000000000 : ℝ)^4449 ≤ (6043193708833/20000000000000 : ℝ)^3425 := by
    have hnat : (795971283 : ℕ)^4449*20000000000000^3425 ≤ 6043193708833^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795971283 2000000000 6043193708833 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4606957153/10000000000 : ℝ)^4449 ≤ (36541164328647/100000000000000 : ℝ)^3425 := by
    have hnat : (4606957153 : ℕ)^4449*100000000000000^3425 ≤ 36541164328647^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606957153 10000000000 36541164328647 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535422131/1250000000 : ℝ), (795971283/2000000000 : ℝ), (4606957153/10000000000 : ℝ)] ![(33242867116193/100000000000000 : ℝ), (6043193708833/20000000000000 : ℝ), (36541164328647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535422131/1250000000 : ℝ)|^4449 ≤ (33242867116193/100000000000000 : ℝ)^3425
        have hw : |(535422131/1250000000 : ℝ)|=(535422131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795971283/2000000000 : ℝ)|^4449 ≤ (6043193708833/20000000000000 : ℝ)^3425
        have hw : |(795971283/2000000000 : ℝ)|=(795971283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4606957153/10000000000 : ℝ)|^4449 ≤ (36541164328647/100000000000000 : ℝ)^3425
        have hw : |(4606957153/10000000000 : ℝ)|=(4606957153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917234447/10000000000 : ℝ)*x 0 + (5188520831/10000000000 : ℝ)*x 1 + (1093708427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917234447/10000000000 : ℝ)^4449 ≤ (5850336240807/50000000000000 : ℝ)^3425 := by
    have hnat : (1917234447 : ℕ)^4449*50000000000000^3425 ≤ 5850336240807^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917234447 10000000000 5850336240807 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5188520831/10000000000 : ℝ)^4449 ≤ (42643007863201/100000000000000 : ℝ)^3425 := by
    have hnat : (5188520831 : ℕ)^4449*100000000000000^3425 ≤ 42643007863201^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188520831 10000000000 42643007863201 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093708427/2000000000 : ℝ)^4449 ≤ (2853519977033/6250000000000 : ℝ)^3425 := by
    have hnat : (1093708427 : ℕ)^4449*6250000000000^3425 ≤ 2853519977033^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093708427 2000000000 2853519977033 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917234447/10000000000 : ℝ), (5188520831/10000000000 : ℝ), (1093708427/2000000000 : ℝ)] ![(5850336240807/50000000000000 : ℝ), (42643007863201/100000000000000 : ℝ), (2853519977033/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917234447/10000000000 : ℝ)|^4449 ≤ (5850336240807/50000000000000 : ℝ)^3425
        have hw : |(-1917234447/10000000000 : ℝ)|=(1917234447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5188520831/10000000000 : ℝ)|^4449 ≤ (42643007863201/100000000000000 : ℝ)^3425
        have hw : |(5188520831/10000000000 : ℝ)|=(5188520831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093708427/2000000000 : ℝ)|^4449 ≤ (2853519977033/6250000000000 : ℝ)^3425
        have hw : |(1093708427/2000000000 : ℝ)|=(1093708427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287793309/10000000000 : ℝ)*x 0 + (-890853799/5000000000 : ℝ)*x 1 + (2734271091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287793309/10000000000 : ℝ)^4449 ≤ (10926463168389/25000000000000 : ℝ)^3425 := by
    have hnat : (5287793309 : ℕ)^4449*25000000000000^3425 ≤ 10926463168389^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287793309 10000000000 10926463168389 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890853799/5000000000 : ℝ)^4449 ≤ (10637827171761/100000000000000 : ℝ)^3425 := by
    have hnat : (890853799 : ℕ)^4449*100000000000000^3425 ≤ 10637827171761^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890853799 5000000000 10637827171761 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2734271091/5000000000 : ℝ)^4449 ≤ (11414080035561/25000000000000 : ℝ)^3425 := by
    have hnat : (2734271091 : ℕ)^4449*25000000000000^3425 ≤ 11414080035561^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734271091 5000000000 11414080035561 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287793309/10000000000 : ℝ), (-890853799/5000000000 : ℝ), (2734271091/5000000000 : ℝ)] ![(10926463168389/25000000000000 : ℝ), (10637827171761/100000000000000 : ℝ), (11414080035561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287793309/10000000000 : ℝ)|^4449 ≤ (10926463168389/25000000000000 : ℝ)^3425
        have hw : |(5287793309/10000000000 : ℝ)|=(5287793309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890853799/5000000000 : ℝ)|^4449 ≤ (10637827171761/100000000000000 : ℝ)^3425
        have hw : |(-890853799/5000000000 : ℝ)|=(890853799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2734271091/5000000000 : ℝ)|^4449 ≤ (11414080035561/25000000000000 : ℝ)^3425
        have hw : |(2734271091/5000000000 : ℝ)|=(2734271091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057558733/2000000000 : ℝ)*x 0 + (273427111/500000000 : ℝ)*x 1 + (-1781707053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057558733/2000000000 : ℝ)^4449 ≤ (43705856495787/100000000000000 : ℝ)^3425 := by
    have hnat : (1057558733 : ℕ)^4449*100000000000000^3425 ≤ 43705856495787^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057558733 2000000000 43705856495787 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273427111/500000000 : ℝ)^4449 ≤ (11414080138589/25000000000000 : ℝ)^3425 := by
    have hnat : (273427111 : ℕ)^4449*25000000000000^3425 ≤ 11414080138589^3425*500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273427111 500000000 11414080138589 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1781707053/10000000000 : ℝ)^4449 ≤ (10637822944931/100000000000000 : ℝ)^3425 := by
    have hnat : (1781707053 : ℕ)^4449*100000000000000^3425 ≤ 10637822944931^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781707053 10000000000 10637822944931 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057558733/2000000000 : ℝ), (273427111/500000000 : ℝ), (-1781707053/10000000000 : ℝ)] ![(43705856495787/100000000000000 : ℝ), (11414080138589/25000000000000 : ℝ), (10637822944931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057558733/2000000000 : ℝ)|^4449 ≤ (43705856495787/100000000000000 : ℝ)^3425
        have hw : |(1057558733/2000000000 : ℝ)|=(1057558733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273427111/500000000 : ℝ)|^4449 ≤ (11414080138589/25000000000000 : ℝ)^3425
        have hw : |(273427111/500000000 : ℝ)|=(273427111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1781707053/10000000000 : ℝ)|^4449 ≤ (10637822944931/100000000000000 : ℝ)^3425
        have hw : |(-1781707053/10000000000 : ℝ)|=(1781707053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s2_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283517043/10000000000 : ℝ)*x 0 + (4602874807/10000000000 : ℝ)*x 1 + (3983977007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283517043/10000000000 : ℝ)^4449 ≤ (16622139223213/50000000000000 : ℝ)^3425 := by
    have hnat : (4283517043 : ℕ)^4449*50000000000000^3425 ≤ 16622139223213^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283517043 10000000000 16622139223213 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4602874807/10000000000 : ℝ)^4449 ≤ (1140597152399/3125000000000 : ℝ)^3425 := by
    have hnat : (4602874807 : ℕ)^4449*3125000000000^3425 ≤ 1140597152399^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4602874807 10000000000 1140597152399 3125000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3983977007/10000000000 : ℝ)^4449 ≤ (15128306333599/50000000000000 : ℝ)^3425 := by
    have hnat : (3983977007 : ℕ)^4449*50000000000000^3425 ≤ 15128306333599^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3983977007 10000000000 15128306333599 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283517043/10000000000 : ℝ), (4602874807/10000000000 : ℝ), (3983977007/10000000000 : ℝ)] ![(16622139223213/50000000000000 : ℝ), (1140597152399/3125000000000 : ℝ), (15128306333599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283517043/10000000000 : ℝ)|^4449 ≤ (16622139223213/50000000000000 : ℝ)^3425
        have hw : |(4283517043/10000000000 : ℝ)|=(4283517043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4602874807/10000000000 : ℝ)|^4449 ≤ (1140597152399/3125000000000 : ℝ)^3425
        have hw : |(4602874807/10000000000 : ℝ)|=(4602874807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3983977007/10000000000 : ℝ)|^4449 ≤ (15128306333599/50000000000000 : ℝ)^3425
        have hw : |(3983977007/10000000000 : ℝ)|=(3983977007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2343/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3923/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (323/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2343/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3923/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2343/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3923/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2343/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3923/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2343/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3923/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2343/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3923/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2343/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3923/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3923/50000 : ℝ) ^ (4447/1024 : ℝ) ≤ (24747312395447/1562500000000000000 : ℝ) := by
    have hpowers : (3923/50000 : ℝ)^4447 ≤ (24747312395447/1562500000000000000 : ℝ)^1024 := by
      have hnat : (3923 : ℕ)^4447*1562500000000000000^1024 ≤ 24747312395447^1024*50000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3923 50000 24747312395447 1562500000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3923/50000 : ℝ)) (X := (24747312395447/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2343/12500 : ℝ) ^ (4447/1024 : ℝ) ≤ (34767671801458829/50000000000000000000 : ℝ) := by
    have hpowers : (2343/12500 : ℝ)^4447 ≤ (34767671801458829/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2343 : ℕ)^4447*50000000000000000000^1024 ≤ 34767671801458829^1024*12500^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2343 12500 34767671801458829 50000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2343/12500 : ℝ)) (X := (34767671801458829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781274747312395447/781250000000000000 : ℝ) ≤ (10000072939963719/10000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (781274747312395447/781250000000000000 : ℝ)^1024 ≤ (10000072939963719/10000000000000000 : ℝ)^4447 := by
      have hnat : (781274747312395447 : ℕ)^1024*10000000000000000^4447 ≤ 10000072939963719^4447*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781274747312395447 781250000000000000 10000072939963719 10000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000072939963719/10000000000000000 : ℝ)) (X := (781274747312395447/781250000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50035559585798113133/50000000000000000000 : ℝ) ≤ (500081859800533/500000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50035559585798113133/50000000000000000000 : ℝ)^1024 ≤ (500081859800533/500000000000000 : ℝ)^4447 := by
      have hnat : (50035559585798113133 : ℕ)^1024*500000000000000^4447 ≤ 500081859800533^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035559585798113133 50000000000000000000 500081859800533 500000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500081859800533/500000000000000 : ℝ)) (X := (50035559585798113133/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25034767671801458829/25000000000000000000 : ℝ) ≤ (10003201452057601/10000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (25034767671801458829/25000000000000000000 : ℝ)^1024 ≤ (10003201452057601/10000000000000000 : ℝ)^4447 := by
      have hnat : (25034767671801458829 : ℕ)^1024*10000000000000000^4447 ≤ 10003201452057601^4447*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034767671801458829 25000000000000000000 10003201452057601 10000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003201452057601/10000000000000000 : ℝ)) (X := (25034767671801458829/25000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24747312395447/1562500000000000000 : ℝ) ≤ ((10895624859383601149/10898000000000000000 : ℝ)+2*(1564256046941/1089800000000000 : ℝ)*(3923/50000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (10895624859383601149/10898000000000000000 : ℝ)+2*(1564256046941/1089800000000000 : ℝ)*(3923/50000 : ℝ)=(10000072939963719/10000000000000000 : ℝ) by norm_num, show 1+2*(24747312395447/1562500000000000000 : ℝ)=(781274747312395447/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34767671801458829/50000000000000000000 : ℝ)+(24747312395447/1562500000000000000 : ℝ) ≤ ((10895624859383601149/10898000000000000000 : ℝ)+(1564256046941/1089800000000000 : ℝ)*((2343/12500 : ℝ)+(3923/50000 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (10895624859383601149/10898000000000000000 : ℝ)+(1564256046941/1089800000000000 : ℝ)*((2343/12500 : ℝ)+(3923/50000 : ℝ))=(500081859800533/500000000000000 : ℝ) by norm_num, show 1+(34767671801458829/50000000000000000000 : ℝ)+(24747312395447/1562500000000000000 : ℝ)=(50035559585798113133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34767671801458829/50000000000000000000 : ℝ) ≤ ((10895624859383601149/10898000000000000000 : ℝ)+2*(1564256046941/1089800000000000 : ℝ)*(2343/12500 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (10895624859383601149/10898000000000000000 : ℝ)+2*(1564256046941/1089800000000000 : ℝ)*(2343/12500 : ℝ)=(10003201452057601/10000000000000000 : ℝ) by norm_num, show 1+2*(34767671801458829/50000000000000000000 : ℝ)=(25034767671801458829/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10895624859383601149/10898000000000000000 : ℝ)*(X 1 0+X 2 0)+(1564256046941/1089800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (3923/50000 : ℝ)) (hi := (2343/12500 : ℝ)) (c := (10895624859383601149/10898000000000000000 : ℝ)) (alpha := (1564256046941/1089800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10895624859383601149/10898000000000000000 : ℝ)*(X 0 1+X 2 1)+(1564256046941/1089800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (3923/50000 : ℝ)) (hi := (2343/12500 : ℝ)) (c := (10895624859383601149/10898000000000000000 : ℝ)) (alpha := (1564256046941/1089800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10895624859383601149/10898000000000000000 : ℝ)*(X 0 2+X 1 2)+(1564256046941/1089800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (3923/50000 : ℝ)) (hi := (2343/12500 : ℝ)) (c := (10895624859383601149/10898000000000000000 : ℝ)) (alpha := (1564256046941/1089800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1917171111/10000000000 : ℝ)*X 0 0+(5470406389/10000000000 : ℝ)*X 0 1+(1037334777/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680937897/5000000000 : ℝ)*X 1 0+(-1031787641/5000000000 : ℝ)*X 1 1+(518667391/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361875807/10000000000 : ℝ)*X 2 0+(1037334779/2000000000 : ℝ)*X 2 1+(-515893821/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535422131/1250000000 : ℝ)*X 0 0+(795971283/2000000000 : ℝ)*X 0 1+(4606957153/10000000000 : ℝ)*X 0 2+(535422131/1250000000 : ℝ)*X 1 0+(795971283/2000000000 : ℝ)*X 1 1+(4606957153/10000000000 : ℝ)*X 1 2+(535422131/1250000000 : ℝ)*X 2 0+(795971283/2000000000 : ℝ)*X 2 1+(4606957153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1917234447/10000000000 : ℝ)*X 0 0+(5188520831/10000000000 : ℝ)*X 0 1+(1093708427/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287793309/10000000000 : ℝ)*X 1 0+(-890853799/5000000000 : ℝ)*X 1 1+(2734271091/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057558733/2000000000 : ℝ)*X 2 0+(273427111/500000000 : ℝ)*X 2 1+(-1781707053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4283517043/10000000000 : ℝ)*X 0 0+(4602874807/10000000000 : ℝ)*X 0 1+(3983977007/10000000000 : ℝ)*X 0 2+(4283517043/10000000000 : ℝ)*X 1 0+(4602874807/10000000000 : ℝ)*X 1 1+(3983977007/10000000000 : ℝ)*X 1 2+(4283517043/10000000000 : ℝ)*X 2 0+(4602874807/10000000000 : ℝ)*X 2 1+(3983977007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (776745943557401702686895793/136225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106092463/10000000000000 : ℝ)*(base19) + (1013342947/100000000000000 : ℝ)*(base23) + (15047261/50000000000000 : ℝ)*(lower2) + (1810853/1250000000000 : ℝ)*(upper3) + (100130817/100000000000000 : ℝ)*(upper5) + (1279781450609919/50000000000000 : ℝ)*(major0) + (1279781450609919/50000000000000 : ℝ)*(major1) + (1279781450609919/50000000000000 : ℝ)*(major2) + (3524460091258601/100000000000000 : ℝ)*(sp0) + (881118080062729/25000000000000 : ℝ)*(sp1) + (3524472367832599/100000000000000 : ℝ)*(sp2) + (797322932138809/50000000000000 : ℝ)*(sp3) + (2657983389/20000000000000 : ℝ)*(sp4) + (3183461023/50000000000000 : ℝ)*(sp7) + (99665764449979/6250000000000 : ℝ)*(f.failure) + (1762236690587773/50000000000000 : ℝ)*(f.sum) + (30256060795641/27245000000000000000000000000 : ℝ)*base66 + (3503206148895413069/544900000000000000000000000000000 : ℝ)*base68 + (1743574562670586931/544900000000000000000000000000000 : ℝ)*base69 + (3927013713918413069/544900000000000000000000000000000 : ℝ)*base72 + (121929894140821/27245000000000000000000000000 : ℝ)*base74 + (272277047919413069/544900000000000000000000000000000 : ℝ)*base76 + (1255535256914513069/544900000000000000000000000000000 : ℝ)*base78 + (20924628338313069/544900000000000000000000000000000 : ℝ)*base80 + (3578054071579/27245000000000000000000000000 : ℝ)*base81 + (95191/15625000000000000000 : ℝ)*base89 + (95191/15625000000000000000 : ℝ)*base91 + (95191/15625000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (324356188695814834549247721/34056250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42348703/4000000000000 : ℝ)*(base19) + (755963543/50000000000000 : ℝ)*(base23) + (8393457/5000000000000 : ℝ)*(upper3) + (14046121/25000000000000 : ℝ)*(lower4) + (48650793/20000000000000 : ℝ)*(upper5) + (162091722767431/6250000000000 : ℝ)*(major0) + (162091722767431/6250000000000 : ℝ)*(major1) + (162091722767431/6250000000000 : ℝ)*(major2) + (466414627/4000000000000 : ℝ)*(sp1) + (2408019677/12500000000000 : ℝ)*(sp2) + (3571159384762853/100000000000000 : ℝ)*(sp4) + (892786666419901/25000000000000 : ℝ)*(sp5) + (71422772173567/2000000000000 : ℝ)*(sp6) + (403943856580973/25000000000000 : ℝ)*(sp7) + (403943856580973/25000000000000 : ℝ)*(f.failure) + (3571159384762853/100000000000000 : ℝ)*(f.sum) + (48717745027643/27245000000000000000000000000 : ℝ)*base65 + (882061122903699281/68112500000000000000000000000000 : ℝ)*base68 + (415353095374799281/68112500000000000000000000000000 : ℝ)*base70 + (1309913350872386781/68112500000000000000000000000000 : ℝ)*base72 + (6720211080289/13622500000000000000000000000 : ℝ)*base73 + (765436634641386781/68112500000000000000000000000000 : ℝ)*base76 + (785634197463936781/68112500000000000000000000000000 : ℝ)*base78 + (700016944755861781/68112500000000000000000000000000 : ℝ)*base80 + (13543309276909/13622500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1205317/62500000000000000000 : ℝ)*base89 + (1205317/62500000000000000000 : ℝ)*base91 + (1205317/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1476_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2343/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3923/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (323/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1476_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (323/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1476_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1476_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1476_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (323/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1476_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1300_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:08.309195+00:00
-- url     : https://prove2.me/submissions/b26cca83-ab40-4304-8fc9-75bdce8df458

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
theorem support_rectangle_w1300_s6_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1040405073/5000000000 : ℝ)*x 0 + (1353725643/2500000000 : ℝ)*x 1 + (2621600077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040405073/5000000000 : ℝ)^1065 ≤ (12661754880193/100000000000000 : ℝ)^809 := by
    have hnat : (1040405073 : ℕ)^1065*100000000000000^809 ≤ 12661754880193^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040405073 5000000000 12661754880193 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353725643/2500000000 : ℝ)^1065 ≤ (4459519405733/10000000000000 : ℝ)^809 := by
    have hnat : (1353725643 : ℕ)^1065*10000000000000^809 ≤ 4459519405733^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353725643 2500000000 4459519405733 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621600077/5000000000 : ℝ)^1065 ≤ (10685762762403/25000000000000 : ℝ)^809 := by
    have hnat : (2621600077 : ℕ)^1065*25000000000000^809 ≤ 10685762762403^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621600077 5000000000 10685762762403 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1040405073/5000000000 : ℝ), (1353725643/2500000000 : ℝ), (2621600077/5000000000 : ℝ)] ![(12661754880193/100000000000000 : ℝ), (4459519405733/10000000000000 : ℝ), (10685762762403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1040405073/5000000000 : ℝ)|^1065 ≤ (12661754880193/100000000000000 : ℝ)^809
        have hw : |(-1040405073/5000000000 : ℝ)|=(1040405073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353725643/2500000000 : ℝ)|^1065 ≤ (4459519405733/10000000000000 : ℝ)^809
        have hw : |(1353725643/2500000000 : ℝ)|=(1353725643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621600077/5000000000 : ℝ)|^1065 ≤ (10685762762403/25000000000000 : ℝ)^809
        have hw : |(2621600077/5000000000 : ℝ)|=(2621600077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674843661/5000000000 : ℝ)*x 0 + (-2168329459/10000000000 : ℝ)*x 1 + (524319971/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674843661/5000000000 : ℝ)^1065 ≤ (43889499098207/100000000000000 : ℝ)^809 := by
    have hnat : (2674843661 : ℕ)^1065*100000000000000^809 ≤ 43889499098207^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674843661 5000000000 43889499098207 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168329459/10000000000 : ℝ)^1065 ≤ (267349092053/2000000000000 : ℝ)^809 := by
    have hnat : (2168329459 : ℕ)^1065*2000000000000^809 ≤ 267349092053^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168329459 10000000000 267349092053 2000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524319971/1000000000 : ℝ)^1065 ≤ (42743046284719/100000000000000 : ℝ)^809 := by
    have hnat : (524319971 : ℕ)^1065*100000000000000^809 ≤ 42743046284719^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524319971 1000000000 42743046284719 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674843661/5000000000 : ℝ), (-2168329459/10000000000 : ℝ), (524319971/1000000000 : ℝ)] ![(43889499098207/100000000000000 : ℝ), (267349092053/2000000000000 : ℝ), (42743046284719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674843661/5000000000 : ℝ)|^1065 ≤ (43889499098207/100000000000000 : ℝ)^809
        have hw : |(2674843661/5000000000 : ℝ)|=(2674843661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168329459/10000000000 : ℝ)|^1065 ≤ (267349092053/2000000000000 : ℝ)^809
        have hw : |(-2168329459/10000000000 : ℝ)|=(2168329459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524319971/1000000000 : ℝ)|^1065 ≤ (42743046284719/100000000000000 : ℝ)^809
        have hw : |(524319971/1000000000 : ℝ)|=(524319971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (213987453/400000000 : ℝ)*x 0 + (1048640011/2000000000 : ℝ)*x 1 + (-2168330329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213987453/400000000 : ℝ)^1065 ≤ (43889488330371/100000000000000 : ℝ)^809 := by
    have hnat : (213987453 : ℕ)^1065*100000000000000^809 ≤ 43889488330371^809*400000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213987453 400000000 43889488330371 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048640011/2000000000 : ℝ)^1065 ≤ (4274304998717/10000000000000 : ℝ)^809 := by
    have hnat : (1048640011 : ℕ)^1065*10000000000000^809 ≤ 4274304998717^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048640011 2000000000 4274304998717 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168330329/10000000000 : ℝ)^1065 ≤ (6683730831643/50000000000000 : ℝ)^809 := by
    have hnat : (2168330329 : ℕ)^1065*50000000000000^809 ≤ 6683730831643^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168330329 10000000000 6683730831643 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213987453/400000000 : ℝ), (1048640011/2000000000 : ℝ), (-2168330329/10000000000 : ℝ)] ![(43889488330371/100000000000000 : ℝ), (4274304998717/10000000000000 : ℝ), (6683730831643/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213987453/400000000 : ℝ)|^1065 ≤ (43889488330371/100000000000000 : ℝ)^809
        have hw : |(213987453/400000000 : ℝ)|=(213987453/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048640011/2000000000 : ℝ)|^1065 ≤ (4274304998717/10000000000000 : ℝ)^809
        have hw : |(1048640011/2000000000 : ℝ)|=(1048640011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168330329/10000000000 : ℝ)|^1065 ≤ (6683730831643/50000000000000 : ℝ)^809
        have hw : |(-2168330329/10000000000 : ℝ)|=(2168330329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (867543631/2000000000 : ℝ)*x 0 + (4164173489/10000000000 : ℝ)*x 1 + (2259071233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867543631/2000000000 : ℝ)^1065 ≤ (33302457865939/100000000000000 : ℝ)^809 := by
    have hnat : (867543631 : ℕ)^1065*100000000000000^809 ≤ 33302457865939^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867543631 2000000000 33302457865939 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4164173489/10000000000 : ℝ)^1065 ≤ (31559672971189/100000000000000 : ℝ)^809 := by
    have hnat : (4164173489 : ℕ)^1065*100000000000000^809 ≤ 31559672971189^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164173489 10000000000 31559672971189 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259071233/5000000000 : ℝ)^1065 ≤ (8784467288821/25000000000000 : ℝ)^809 := by
    have hnat : (2259071233 : ℕ)^1065*25000000000000^809 ≤ 8784467288821^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259071233 5000000000 8784467288821 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867543631/2000000000 : ℝ), (4164173489/10000000000 : ℝ), (2259071233/5000000000 : ℝ)] ![(33302457865939/100000000000000 : ℝ), (31559672971189/100000000000000 : ℝ), (8784467288821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867543631/2000000000 : ℝ)|^1065 ≤ (33302457865939/100000000000000 : ℝ)^809
        have hw : |(867543631/2000000000 : ℝ)|=(867543631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4164173489/10000000000 : ℝ)|^1065 ≤ (31559672971189/100000000000000 : ℝ)^809
        have hw : |(4164173489/10000000000 : ℝ)|=(4164173489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259071233/5000000000 : ℝ)|^1065 ≤ (8784467288821/25000000000000 : ℝ)^809
        have hw : |(2259071233/5000000000 : ℝ)|=(2259071233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080823487/10000000000 : ℝ)*x 0 + (52438127/100000000 : ℝ)*x 1 + (5414286361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080823487/10000000000 : ℝ)^1065 ≤ (12661861749097/100000000000000 : ℝ)^809 := by
    have hnat : (2080823487 : ℕ)^1065*100000000000000^809 ≤ 12661861749097^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080823487 10000000000 12661861749097 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52438127/100000000 : ℝ)^1065 ≤ (5343703106991/12500000000000 : ℝ)^809 := by
    have hnat : (52438127 : ℕ)^1065*12500000000000^809 ≤ 5343703106991^809*100000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52438127 100000000 5343703106991 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414286361/10000000000 : ℝ)^1065 ≤ (1783540535429/4000000000000 : ℝ)^809 := by
    have hnat : (5414286361 : ℕ)^1065*4000000000000^809 ≤ 1783540535429^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414286361 10000000000 1783540535429 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080823487/10000000000 : ℝ), (52438127/100000000 : ℝ), (5414286361/10000000000 : ℝ)] ![(12661861749097/100000000000000 : ℝ), (5343703106991/12500000000000 : ℝ), (1783540535429/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080823487/10000000000 : ℝ)|^1065 ≤ (12661861749097/100000000000000 : ℝ)^809
        have hw : |(-2080823487/10000000000 : ℝ)|=(2080823487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52438127/100000000 : ℝ)|^1065 ≤ (5343703106991/12500000000000 : ℝ)^809
        have hw : |(52438127/100000000 : ℝ)|=(52438127/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414286361/10000000000 : ℝ)|^1065 ≤ (1783540535429/4000000000000 : ℝ)^809
        have hw : |(5414286361/10000000000 : ℝ)|=(5414286361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326420531/2500000000 : ℝ)*x 0 + (-1997243651/10000000000 : ℝ)*x 1 + (270714319/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326420531/2500000000 : ℝ)^1065 ≤ (21707426107593/50000000000000 : ℝ)^809 := by
    have hnat : (1326420531 : ℕ)^1065*50000000000000^809 ≤ 21707426107593^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326420531 2500000000 21707426107593 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997243651/10000000000 : ℝ)^1065 ≤ (5998317090391/50000000000000 : ℝ)^809 := by
    have hnat : (1997243651 : ℕ)^1065*50000000000000^809 ≤ 5998317090391^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997243651 10000000000 5998317090391 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270714319/500000000 : ℝ)^1065 ≤ (4458851359171/10000000000000 : ℝ)^809 := by
    have hnat : (270714319 : ℕ)^1065*10000000000000^809 ≤ 4458851359171^809*500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270714319 500000000 4458851359171 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326420531/2500000000 : ℝ), (-1997243651/10000000000 : ℝ), (270714319/500000000 : ℝ)] ![(21707426107593/50000000000000 : ℝ), (5998317090391/50000000000000 : ℝ), (4458851359171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326420531/2500000000 : ℝ)|^1065 ≤ (21707426107593/50000000000000 : ℝ)^809
        have hw : |(1326420531/2500000000 : ℝ)|=(1326420531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997243651/10000000000 : ℝ)|^1065 ≤ (5998317090391/50000000000000 : ℝ)^809
        have hw : |(-1997243651/10000000000 : ℝ)|=(1997243651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270714319/500000000 : ℝ)|^1065 ≤ (4458851359171/10000000000000 : ℝ)^809
        have hw : |(270714319/500000000 : ℝ)|=(270714319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305682207/10000000000 : ℝ)*x 0 + (1353571577/2500000000 : ℝ)*x 1 + (-499310909/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305682207/10000000000 : ℝ)^1065 ≤ (21707426554633/50000000000000 : ℝ)^809 := by
    have hnat : (5305682207 : ℕ)^1065*50000000000000^809 ≤ 21707426554633^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305682207 10000000000 21707426554633 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353571577/2500000000 : ℝ)^1065 ≤ (22294256405567/50000000000000 : ℝ)^809 := by
    have hnat : (1353571577 : ℕ)^1065*50000000000000^809 ≤ 22294256405567^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353571577 2500000000 22294256405567 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499310909/2500000000 : ℝ)^1065 ≤ (2999158515543/25000000000000 : ℝ)^809 := by
    have hnat : (499310909 : ℕ)^1065*25000000000000^809 ≤ 2999158515543^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499310909 2500000000 2999158515543 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305682207/10000000000 : ℝ), (1353571577/2500000000 : ℝ), (-499310909/2500000000 : ℝ)] ![(21707426554633/50000000000000 : ℝ), (22294256405567/50000000000000 : ℝ), (2999158515543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305682207/10000000000 : ℝ)|^1065 ≤ (21707426554633/50000000000000 : ℝ)^809
        have hw : |(5305682207/10000000000 : ℝ)|=(5305682207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353571577/2500000000 : ℝ)|^1065 ≤ (22294256405567/50000000000000 : ℝ)^809
        have hw : |(1353571577/2500000000 : ℝ)|=(1353571577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499310909/2500000000 : ℝ)|^1065 ≤ (2999158515543/25000000000000 : ℝ)^809
        have hw : |(-499310909/2500000000 : ℝ)|=(499310909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s6_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4337744917/10000000000 : ℝ)*x 0 + (2258439201/5000000000 : ℝ)*x 1 + (4165443381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337744917/10000000000 : ℝ)^1065 ≤ (16651364172931/50000000000000 : ℝ)^809 := by
    have hnat : (4337744917 : ℕ)^1065*50000000000000^809 ≤ 16651364172931^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337744917 10000000000 16651364172931 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258439201/5000000000 : ℝ)^1065 ≤ (17562464098707/50000000000000 : ℝ)^809 := by
    have hnat : (2258439201 : ℕ)^1065*50000000000000^809 ≤ 17562464098707^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258439201 5000000000 17562464098707 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165443381/10000000000 : ℝ)^1065 ≤ (31572343434791/100000000000000 : ℝ)^809 := by
    have hnat : (4165443381 : ℕ)^1065*100000000000000^809 ≤ 31572343434791^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165443381 10000000000 31572343434791 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337744917/10000000000 : ℝ), (2258439201/5000000000 : ℝ), (4165443381/10000000000 : ℝ)] ![(16651364172931/50000000000000 : ℝ), (17562464098707/50000000000000 : ℝ), (31572343434791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337744917/10000000000 : ℝ)|^1065 ≤ (16651364172931/50000000000000 : ℝ)^809
        have hw : |(4337744917/10000000000 : ℝ)|=(4337744917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258439201/5000000000 : ℝ)|^1065 ≤ (17562464098707/50000000000000 : ℝ)^809
        have hw : |(2258439201/5000000000 : ℝ)|=(2258439201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165443381/10000000000 : ℝ)|^1065 ≤ (31572343434791/100000000000000 : ℝ)^809
        have hw : |(4165443381/10000000000 : ℝ)|=(4165443381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5523/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (367/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14691/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2759/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14691/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2759/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14691/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2759/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2759/25000 : ℝ) ^ (4259/1024 : ℝ) ≤ (10444359966877473/100000000000000000000 : ℝ) := by
    have hpowers : (2759/25000 : ℝ)^4259 ≤ (10444359966877473/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2759 : ℕ)^4259*100000000000000000000^1024 ≤ 10444359966877473^1024*25000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2759 25000 10444359966877473 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2759/25000 : ℝ)) (X := (10444359966877473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14691/100000 : ℝ) ^ (4259/1024 : ℝ) ≤ (8581376155067071/25000000000000000000 : ℝ) := by
    have hpowers : (14691/100000 : ℝ)^4259 ≤ (8581376155067071/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14691 : ℕ)^4259*25000000000000000000^1024 ≤ 8581376155067071^1024*100000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14691 100000 8581376155067071 25000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14691/100000 : ℝ)) (X := (8581376155067071/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010444359966877473/50000000000000000000 : ℝ) ≤ (1000050219188787/1000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50010444359966877473/50000000000000000000 : ℝ)^1024 ≤ (1000050219188787/1000000000000000 : ℝ)^4259 := by
      have hnat : (50010444359966877473 : ℕ)^1024*1000000000000000^4259 ≤ 1000050219188787^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010444359966877473 50000000000000000000 1000050219188787 1000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000050219188787/1000000000000000 : ℝ)) (X := (50010444359966877473/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044769864587145757/100000000000000000000 : ℝ) ≤ (2000215245590637/2000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (100044769864587145757/100000000000000000000 : ℝ)^1024 ≤ (2000215245590637/2000000000000000 : ℝ)^4259 := by
      have hnat : (100044769864587145757 : ℕ)^1024*2000000000000000^4259 ≤ 2000215245590637^4259*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044769864587145757 100000000000000000000 2000215245590637 2000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000215245590637/2000000000000000 : ℝ)) (X := (100044769864587145757/100000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508581376155067071/12500000000000000000 : ℝ) ≤ (20003300528037/20000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (12508581376155067071/12500000000000000000 : ℝ)^1024 ≤ (20003300528037/20000000000000 : ℝ)^4259 := by
      have hnat : (12508581376155067071 : ℕ)^1024*20000000000000^4259 ≤ 20003300528037^4259*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508581376155067071 12500000000000000000 20003300528037 20000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20003300528037/20000000000000 : ℝ)) (X := (12508581376155067071/12500000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10444359966877473/100000000000000000000 : ℝ) ≤ ((3653916538731653217/3655000000000000000 : ℝ)+2*(114807213063/73100000000000 : ℝ)*(2759/25000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (3653916538731653217/3655000000000000000 : ℝ)+2*(114807213063/73100000000000 : ℝ)*(2759/25000 : ℝ)=(1000050219188787/1000000000000000 : ℝ) by norm_num, show 1+2*(10444359966877473/100000000000000000000 : ℝ)=(50010444359966877473/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8581376155067071/25000000000000000000 : ℝ)+(10444359966877473/100000000000000000000 : ℝ) ≤ ((3653916538731653217/3655000000000000000 : ℝ)+(114807213063/73100000000000 : ℝ)*((14691/100000 : ℝ)+(2759/25000 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (3653916538731653217/3655000000000000000 : ℝ)+(114807213063/73100000000000 : ℝ)*((14691/100000 : ℝ)+(2759/25000 : ℝ))=(2000215245590637/2000000000000000 : ℝ) by norm_num, show 1+(8581376155067071/25000000000000000000 : ℝ)+(10444359966877473/100000000000000000000 : ℝ)=(100044769864587145757/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8581376155067071/25000000000000000000 : ℝ) ≤ ((3653916538731653217/3655000000000000000 : ℝ)+2*(114807213063/73100000000000 : ℝ)*(14691/100000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (3653916538731653217/3655000000000000000 : ℝ)+2*(114807213063/73100000000000 : ℝ)*(14691/100000 : ℝ)=(20003300528037/20000000000000 : ℝ) by norm_num, show 1+2*(8581376155067071/25000000000000000000 : ℝ)=(12508581376155067071/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3653916538731653217/3655000000000000000 : ℝ)*(X 1 0+X 2 0)+(114807213063/73100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (3653916538731653217/3655000000000000000 : ℝ)) (alpha := (114807213063/73100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3653916538731653217/3655000000000000000 : ℝ)*(X 0 1+X 2 1)+(114807213063/73100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (3653916538731653217/3655000000000000000 : ℝ)) (alpha := (114807213063/73100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3653916538731653217/3655000000000000000 : ℝ)*(X 0 2+X 1 2)+(114807213063/73100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (2759/25000 : ℝ)) (hi := (14691/100000 : ℝ)) (c := (3653916538731653217/3655000000000000000 : ℝ)) (alpha := (114807213063/73100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1040405073/5000000000 : ℝ)*X 0 0+(1353725643/2500000000 : ℝ)*X 0 1+(2621600077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674843661/5000000000 : ℝ)*X 1 0+(-2168329459/10000000000 : ℝ)*X 1 1+(524319971/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213987453/400000000 : ℝ)*X 2 0+(1048640011/2000000000 : ℝ)*X 2 1+(-2168330329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867543631/2000000000 : ℝ)*X 0 0+(4164173489/10000000000 : ℝ)*X 0 1+(2259071233/5000000000 : ℝ)*X 0 2+(867543631/2000000000 : ℝ)*X 1 0+(4164173489/10000000000 : ℝ)*X 1 1+(2259071233/5000000000 : ℝ)*X 1 2+(867543631/2000000000 : ℝ)*X 2 0+(4164173489/10000000000 : ℝ)*X 2 1+(2259071233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2080823487/10000000000 : ℝ)*X 0 0+(52438127/100000000 : ℝ)*X 0 1+(5414286361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326420531/2500000000 : ℝ)*X 1 0+(-1997243651/10000000000 : ℝ)*X 1 1+(270714319/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305682207/10000000000 : ℝ)*X 2 0+(1353571577/2500000000 : ℝ)*X 2 1+(-499310909/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337744917/10000000000 : ℝ)*X 0 0+(2258439201/5000000000 : ℝ)*X 0 1+(4165443381/10000000000 : ℝ)*X 0 2+(4337744917/10000000000 : ℝ)*X 1 0+(2258439201/5000000000 : ℝ)*X 1 1+(4165443381/10000000000 : ℝ)*X 1 2+(4337744917/10000000000 : ℝ)*X 2 0+(2258439201/5000000000 : ℝ)*X 2 1+(4165443381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (732879423811422103260451539/91375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149896763/12500000000000 : ℝ)*(base19) + (142325793/50000000000000 : ℝ)*(base23) + (24205027/12500000000000 : ℝ)*(lower4) + (363559/195312500000 : ℝ)*(lower5) + (2162306661227689/50000000000000 : ℝ)*(major0) + (2162306661227689/50000000000000 : ℝ)*(major1) + (2162306661227689/50000000000000 : ℝ)*(major2) + (5824068254923763/100000000000000 : ℝ)*(sp0) + (2912042641225927/50000000000000 : ℝ)*(sp1) + (5824062967381669/100000000000000 : ℝ)*(sp2) + (70628119437587/2500000000000 : ℝ)*(sp3) + (4556675549/25000000000000 : ℝ)*(sp4) + (181481193/781250000000 : ℝ)*(sp6) + (3779607259/25000000000000 : ℝ)*(sp7) + (706284973983129/25000000000000 : ℝ)*(f.failure) + (2912043240812979/50000000000000 : ℝ)*(f.sum) + (169536462147/114218750000000000000000000 : ℝ)*base65 + (74740955657077911/10750000000000000000000000000000 : ℝ)*base68 + (48923442036577911/10750000000000000000000000000000 : ℝ)*base70 + (67261657693922089/10750000000000000000000000000000 : ℝ)*base71 + (3134097518779/913750000000000000000000000 : ℝ)*base74 + (190260251581922089/10750000000000000000000000000000 : ℝ)*base75 + (26861033329827911/10750000000000000000000000000000 : ℝ)*base78 + (46311301310327911/10750000000000000000000000000000 : ℝ)*base80 + (8537331566091/3655000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1504933/2500000000000000000000 : ℝ)*base89 + (1504933/2500000000000000000000 : ℝ)*base91 + (1504933/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (546140901835290587015909919/91375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1157914433/100000000000000 : ℝ)*(base19) + (329420097/25000000000000 : ℝ)*(base23) + (30338333/100000000000000 : ℝ)*(upper2) + (37138993/25000000000000 : ℝ)*(upper3) + (43768309/25000000000000 : ℝ)*(upper5) + (2177871518101977/50000000000000 : ℝ)*(major0) + (2177871518101977/50000000000000 : ℝ)*(major1) + (2177871518101977/50000000000000 : ℝ)*(major2) + (23004471707/100000000000000 : ℝ)*(sp1) + (24309580791/100000000000000 : ℝ)*(sp2) + (733251233867281/12500000000000 : ℝ)*(sp4) + (1466496427138027/25000000000000 : ℝ)*(sp5) + (586598424367707/10000000000000 : ℝ)*(sp6) + (2845476002239039/100000000000000 : ℝ)*(sp7) + (2845476002239039/100000000000000 : ℝ)*(f.failure) + (733251233867281/12500000000000 : ℝ)*(f.sum) + (7012851421383/3655000000000000000000000000 : ℝ)*base66 + (163830710466421177/10750000000000000000000000000000 : ℝ)*base67 + (159623148544671177/10750000000000000000000000000000 : ℝ)*base69 + (116294796008171177/10750000000000000000000000000000 : ℝ)*base71 + (4323610358767/3655000000000000000000000000 : ℝ)*base73 + (220998569863171177/10750000000000000000000000000000 : ℝ)*base75 + (83350770428921177/10750000000000000000000000000000 : ℝ)*base77 + (53164282217671177/10750000000000000000000000000000 : ℝ)*base79 + (8174168257801/1827500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (93629997/10000000000000000000000 : ℝ)*base90 + (93629997/10000000000000000000000 : ℝ)*base92 + (93629997/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1300_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1300_s7_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1040411497/5000000000 : ℝ)*x 0 + (1353702091/2500000000 : ℝ)*x 1 + (655410717/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040411497/5000000000 : ℝ)^1065 ≤ (6330928899943/50000000000000 : ℝ)^809 := by
    have hnat : (1040411497 : ℕ)^1065*50000000000000^809 ≤ 6330928899943^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040411497 5000000000 6330928899943 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353702091/2500000000 : ℝ)^1065 ≤ (44594172682653/100000000000000 : ℝ)^809 := by
    have hnat : (1353702091 : ℕ)^1065*100000000000000^809 ≤ 44594172682653^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353702091 2500000000 44594172682653 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655410717/1250000000 : ℝ)^1065 ≤ (42743969495813/100000000000000 : ℝ)^809 := by
    have hnat : (655410717 : ℕ)^1065*100000000000000^809 ≤ 42743969495813^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655410717 1250000000 42743969495813 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1040411497/5000000000 : ℝ), (1353702091/2500000000 : ℝ), (655410717/1250000000 : ℝ)] ![(6330928899943/50000000000000 : ℝ), (44594172682653/100000000000000 : ℝ), (42743969495813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1040411497/5000000000 : ℝ)|^1065 ≤ (6330928899943/50000000000000 : ℝ)^809
        have hw : |(-1040411497/5000000000 : ℝ)|=(1040411497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353702091/2500000000 : ℝ)|^1065 ≤ (44594172682653/100000000000000 : ℝ)^809
        have hw : |(1353702091/2500000000 : ℝ)|=(1353702091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655410717/1250000000 : ℝ)|^1065 ≤ (42743969495813/100000000000000 : ℝ)^809
        have hw : |(655410717/1250000000 : ℝ)|=(655410717/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349662631/10000000000 : ℝ)*x 0 + (-2168248007/10000000000 : ℝ)*x 1 + (2621643077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349662631/10000000000 : ℝ)^1065 ≤ (8777846485947/20000000000000 : ℝ)^809 := by
    have hnat : (5349662631 : ℕ)^1065*20000000000000^809 ≤ 8777846485947^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349662631 10000000000 8777846485947 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168248007/10000000000 : ℝ)^1065 ≤ (13366793568791/100000000000000 : ℝ)^809 := by
    have hnat : (2168248007 : ℕ)^1065*100000000000000^809 ≤ 13366793568791^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168248007 10000000000 13366793568791 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621643077/5000000000 : ℝ)^1065 ≤ (42743973981703/100000000000000 : ℝ)^809 := by
    have hnat : (2621643077 : ℕ)^1065*100000000000000^809 ≤ 42743973981703^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621643077 5000000000 42743973981703 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349662631/10000000000 : ℝ), (-2168248007/10000000000 : ℝ), (2621643077/5000000000 : ℝ)] ![(8777846485947/20000000000000 : ℝ), (13366793568791/100000000000000 : ℝ), (42743973981703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349662631/10000000000 : ℝ)|^1065 ≤ (8777846485947/20000000000000 : ℝ)^809
        have hw : |(5349662631/10000000000 : ℝ)|=(5349662631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168248007/10000000000 : ℝ)|^1065 ≤ (13366793568791/100000000000000 : ℝ)^809
        have hw : |(-2168248007/10000000000 : ℝ)|=(2168248007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621643077/5000000000 : ℝ)|^1065 ≤ (42743973981703/100000000000000 : ℝ)^809
        have hw : |(2621643077/5000000000 : ℝ)|=(2621643077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349661899/10000000000 : ℝ)*x 0 + (2621643609/5000000000 : ℝ)*x 1 + (-86729903/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349661899/10000000000 : ℝ)^1065 ≤ (10972306130993/25000000000000 : ℝ)^809 := by
    have hnat : (5349661899 : ℕ)^1065*25000000000000^809 ≤ 10972306130993^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349661899 10000000000 10972306130993 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621643609/5000000000 : ℝ)^1065 ≤ (8548797080067/20000000000000 : ℝ)^809 := by
    have hnat : (2621643609 : ℕ)^1065*20000000000000^809 ≤ 8548797080067^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621643609 5000000000 8548797080067 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86729903/400000000 : ℝ)^1065 ≤ (6683395031431/50000000000000 : ℝ)^809 := by
    have hnat : (86729903 : ℕ)^1065*50000000000000^809 ≤ 6683395031431^809*400000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86729903 400000000 6683395031431 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349661899/10000000000 : ℝ), (2621643609/5000000000 : ℝ), (-86729903/400000000 : ℝ)] ![(10972306130993/25000000000000 : ℝ), (8548797080067/20000000000000 : ℝ), (6683395031431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349661899/10000000000 : ℝ)|^1065 ≤ (10972306130993/25000000000000 : ℝ)^809
        have hw : |(5349661899/10000000000 : ℝ)|=(5349661899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621643609/5000000000 : ℝ)|^1065 ≤ (8548797080067/20000000000000 : ℝ)^809
        have hw : |(2621643609/5000000000 : ℝ)|=(2621643609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86729903/400000000 : ℝ)|^1065 ≤ (6683395031431/50000000000000 : ℝ)^809
        have hw : |(-86729903/400000000 : ℝ)|=(86729903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4337726899/10000000000 : ℝ)*x 0 + (520544613/1250000000 : ℝ)*x 1 + (451795509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337726899/10000000000 : ℝ)^1065 ≤ (33302546240309/100000000000000 : ℝ)^809 := by
    have hnat : (4337726899 : ℕ)^1065*100000000000000^809 ≤ 33302546240309^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337726899 10000000000 33302546240309 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520544613/1250000000 : ℝ)^1065 ≤ (15780751467797/50000000000000 : ℝ)^809 := by
    have hnat : (520544613 : ℕ)^1065*50000000000000^809 ≤ 15780751467797^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520544613 1250000000 15780751467797 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451795509/1000000000 : ℝ)^1065 ≤ (35135950805929/100000000000000 : ℝ)^809 := by
    have hnat : (451795509 : ℕ)^1065*100000000000000^809 ≤ 35135950805929^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451795509 1000000000 35135950805929 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337726899/10000000000 : ℝ), (520544613/1250000000 : ℝ), (451795509/1000000000 : ℝ)] ![(33302546240309/100000000000000 : ℝ), (15780751467797/50000000000000 : ℝ), (35135950805929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337726899/10000000000 : ℝ)|^1065 ≤ (33302546240309/100000000000000 : ℝ)^809
        have hw : |(4337726899/10000000000 : ℝ)|=(4337726899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520544613/1250000000 : ℝ)|^1065 ≤ (15780751467797/50000000000000 : ℝ)^809
        have hw : |(520544613/1250000000 : ℝ)|=(520544613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451795509/1000000000 : ℝ)|^1065 ≤ (35135950805929/100000000000000 : ℝ)^809
        have hw : |(451795509/1000000000 : ℝ)|=(451795509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080836093/10000000000 : ℝ)*x 0 + (2621948579/5000000000 : ℝ)*x 1 + (2707096719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080836093/10000000000 : ℝ)^1065 ≤ (6330981365219/50000000000000 : ℝ)^809 := by
    have hnat : (2080836093 : ℕ)^1065*50000000000000^809 ≤ 6330981365219^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080836093 10000000000 6330981365219 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621948579/5000000000 : ℝ)^1065 ≤ (42750531273097/100000000000000 : ℝ)^809 := by
    have hnat : (2621948579 : ℕ)^1065*100000000000000^809 ≤ 42750531273097^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621948579 5000000000 42750531273097 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707096719/5000000000 : ℝ)^1065 ≤ (44587505978873/100000000000000 : ℝ)^809 := by
    have hnat : (2707096719 : ℕ)^1065*100000000000000^809 ≤ 44587505978873^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707096719 5000000000 44587505978873 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080836093/10000000000 : ℝ), (2621948579/5000000000 : ℝ), (2707096719/5000000000 : ℝ)] ![(6330981365219/50000000000000 : ℝ), (42750531273097/100000000000000 : ℝ), (44587505978873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080836093/10000000000 : ℝ)|^1065 ≤ (6330981365219/50000000000000 : ℝ)^809
        have hw : |(-2080836093/10000000000 : ℝ)|=(2080836093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621948579/5000000000 : ℝ)|^1065 ≤ (42750531273097/100000000000000 : ℝ)^809
        have hw : |(2621948579/5000000000 : ℝ)|=(2621948579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707096719/5000000000 : ℝ)|^1065 ≤ (44587505978873/100000000000000 : ℝ)^809
        have hw : |(2707096719/5000000000 : ℝ)|=(2707096719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305704113/10000000000 : ℝ)*x 0 + (-199734121/1000000000 : ℝ)*x 1 + (5414193373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305704113/10000000000 : ℝ)^1065 ≤ (21707544540927/50000000000000 : ℝ)^809 := by
    have hnat : (5305704113 : ℕ)^1065*50000000000000^809 ≤ 21707544540927^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305704113 10000000000 21707544540927 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199734121/1000000000 : ℝ)^1065 ≤ (11997405617221/100000000000000 : ℝ)^809 := by
    have hnat : (199734121 : ℕ)^1065*100000000000000^809 ≤ 11997405617221^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199734121 1000000000 11997405617221 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414193373/10000000000 : ℝ)^1065 ≤ (4458750527419/10000000000000 : ℝ)^809 := by
    have hnat : (5414193373 : ℕ)^1065*10000000000000^809 ≤ 4458750527419^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414193373 10000000000 4458750527419 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305704113/10000000000 : ℝ), (-199734121/1000000000 : ℝ), (5414193373/10000000000 : ℝ)] ![(21707544540927/50000000000000 : ℝ), (11997405617221/100000000000000 : ℝ), (4458750527419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305704113/10000000000 : ℝ)|^1065 ≤ (21707544540927/50000000000000 : ℝ)^809
        have hw : |(5305704113/10000000000 : ℝ)|=(5305704113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199734121/1000000000 : ℝ)|^1065 ≤ (11997405617221/100000000000000 : ℝ)^809
        have hw : |(-199734121/1000000000 : ℝ)|=(199734121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414193373/10000000000 : ℝ)|^1065 ≤ (4458750527419/10000000000000 : ℝ)^809
        have hw : |(5414193373/10000000000 : ℝ)|=(5414193373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265285221/500000000 : ℝ)*x 0 + (541419307/1000000000 : ℝ)*x 1 + (-249667651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265285221/500000000 : ℝ)^1065 ≤ (10853773097219/25000000000000 : ℝ)^809 := by
    have hnat : (265285221 : ℕ)^1065*25000000000000^809 ≤ 10853773097219^809*500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265285221 500000000 10853773097219 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541419307/1000000000 : ℝ)^1065 ≤ (44587501989283/100000000000000 : ℝ)^809 := by
    have hnat : (541419307 : ℕ)^1065*100000000000000^809 ≤ 44587501989283^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541419307 1000000000 44587501989283 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249667651/1250000000 : ℝ)^1065 ≤ (11997405601407/100000000000000 : ℝ)^809 := by
    have hnat : (249667651 : ℕ)^1065*100000000000000^809 ≤ 11997405601407^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249667651 1250000000 11997405601407 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265285221/500000000 : ℝ), (541419307/1000000000 : ℝ), (-249667651/1250000000 : ℝ)] ![(10853773097219/25000000000000 : ℝ), (44587501989283/100000000000000 : ℝ), (11997405601407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265285221/500000000 : ℝ)|^1065 ≤ (10853773097219/25000000000000 : ℝ)^809
        have hw : |(265285221/500000000 : ℝ)|=(265285221/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541419307/1000000000 : ℝ)|^1065 ≤ (44587501989283/100000000000000 : ℝ)^809
        have hw : |(541419307/1000000000 : ℝ)|=(541419307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249667651/1250000000 : ℝ)|^1065 ≤ (11997405601407/100000000000000 : ℝ)^809
        have hw : |(-249667651/1250000000 : ℝ)|=(249667651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_s7_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2168875693/5000000000 : ℝ)*x 0 + (451669449/1000000000 : ℝ)*x 1 + (4165625513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168875693/5000000000 : ℝ)^1065 ≤ (33302793727251/100000000000000 : ℝ)^809 := by
    have hnat : (2168875693 : ℕ)^1065*100000000000000^809 ≤ 33302793727251^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168875693 5000000000 33302793727251 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451669449/1000000000 : ℝ)^1065 ≤ (2195190342429/6250000000000 : ℝ)^809 := by
    have hnat : (451669449 : ℕ)^1065*6250000000000^809 ≤ 2195190342429^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451669449 1000000000 2195190342429 6250000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165625513/10000000000 : ℝ)^1065 ≤ (789354019343/2500000000000 : ℝ)^809 := by
    have hnat : (4165625513 : ℕ)^1065*2500000000000^809 ≤ 789354019343^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165625513 10000000000 789354019343 2500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168875693/5000000000 : ℝ), (451669449/1000000000 : ℝ), (4165625513/10000000000 : ℝ)] ![(33302793727251/100000000000000 : ℝ), (2195190342429/6250000000000 : ℝ), (789354019343/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168875693/5000000000 : ℝ)|^1065 ≤ (33302793727251/100000000000000 : ℝ)^809
        have hw : |(2168875693/5000000000 : ℝ)|=(2168875693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451669449/1000000000 : ℝ)|^1065 ≤ (2195190342429/6250000000000 : ℝ)^809
        have hw : |(451669449/1000000000 : ℝ)|=(451669449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165625513/10000000000 : ℝ)|^1065 ≤ (789354019343/2500000000000 : ℝ)^809
        have hw : |(4165625513/10000000000 : ℝ)|=(4165625513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1381/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7339/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (367/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (367/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (367/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5523/50000 : ℝ) ^ (4259/1024 : ℝ) ≤ (2096755680634177/20000000000000000000 : ℝ) := by
    have hpowers : (5523/50000 : ℝ)^4259 ≤ (2096755680634177/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5523 : ℕ)^4259*20000000000000000000^1024 ≤ 2096755680634177^1024*50000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5523 50000 2096755680634177 20000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5523/50000 : ℝ)) (X := (2096755680634177/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (367/2500 : ℝ) ^ (4259/1024 : ℝ) ≤ (1368749355136159/4000000000000000000 : ℝ) := by
    have hpowers : (367/2500 : ℝ)^4259 ≤ (1368749355136159/4000000000000000000 : ℝ)^1024 := by
      have hnat : (367 : ℕ)^4259*4000000000000000000^1024 ≤ 1368749355136159^1024*2500^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        367 2500 1368749355136159 4000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (367/2500 : ℝ)) (X := (1368749355136159/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002096755680634177/10000000000000000000 : ℝ) ≤ (5000252043538757/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (10002096755680634177/10000000000000000000 : ℝ)^1024 ≤ (5000252043538757/5000000000000000 : ℝ)^4259 := by
      have hnat : (10002096755680634177 : ℕ)^1024*5000000000000000^4259 ≤ 5000252043538757^4259*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002096755680634177 10000000000000000000 5000252043538757 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000252043538757/5000000000000000 : ℝ)) (X := (10002096755680634177/10000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002235125614078743/5000000000000000000 : ℝ) ≤ (5000537304569051/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (5002235125614078743/5000000000000000000 : ℝ)^1024 ≤ (5000537304569051/5000000000000000 : ℝ)^4259 := by
      have hnat : (5002235125614078743 : ℕ)^1024*5000000000000000^4259 ≤ 5000537304569051^4259*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002235125614078743 5000000000000000000 5000537304569051 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000537304569051/5000000000000000 : ℝ)) (X := (5002235125614078743/5000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001368749355136159/2000000000000000000 : ℝ) ≤ (1000164513119869/1000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (2001368749355136159/2000000000000000000 : ℝ)^1024 ≤ (1000164513119869/1000000000000000 : ℝ)^4259 := by
      have hnat : (2001368749355136159 : ℕ)^1024*1000000000000000^4259 ≤ 1000164513119869^4259*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001368749355136159 2000000000000000000 1000164513119869 1000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000164513119869/1000000000000000 : ℝ)) (X := (2001368749355136159/2000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2096755680634177/20000000000000000000 : ℝ) ≤ ((1816461393953858789/1817000000000000000 : ℝ)+2*(142630515147/90850000000000 : ℝ)*(5523/50000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (1816461393953858789/1817000000000000000 : ℝ)+2*(142630515147/90850000000000 : ℝ)*(5523/50000 : ℝ)=(5000252043538757/5000000000000000 : ℝ) by norm_num, show 1+2*(2096755680634177/20000000000000000000 : ℝ)=(10002096755680634177/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1368749355136159/4000000000000000000 : ℝ)+(2096755680634177/20000000000000000000 : ℝ) ≤ ((1816461393953858789/1817000000000000000 : ℝ)+(142630515147/90850000000000 : ℝ)*((367/2500 : ℝ)+(5523/50000 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (1816461393953858789/1817000000000000000 : ℝ)+(142630515147/90850000000000 : ℝ)*((367/2500 : ℝ)+(5523/50000 : ℝ))=(5000537304569051/5000000000000000 : ℝ) by norm_num, show 1+(1368749355136159/4000000000000000000 : ℝ)+(2096755680634177/20000000000000000000 : ℝ)=(5002235125614078743/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1368749355136159/4000000000000000000 : ℝ) ≤ ((1816461393953858789/1817000000000000000 : ℝ)+2*(142630515147/90850000000000 : ℝ)*(367/2500 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (1816461393953858789/1817000000000000000 : ℝ)+2*(142630515147/90850000000000 : ℝ)*(367/2500 : ℝ)=(1000164513119869/1000000000000000 : ℝ) by norm_num, show 1+2*(1368749355136159/4000000000000000000 : ℝ)=(2001368749355136159/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1816461393953858789/1817000000000000000 : ℝ)*(X 1 0+X 2 0)+(142630515147/90850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (1816461393953858789/1817000000000000000 : ℝ)) (alpha := (142630515147/90850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1816461393953858789/1817000000000000000 : ℝ)*(X 0 1+X 2 1)+(142630515147/90850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (1816461393953858789/1817000000000000000 : ℝ)) (alpha := (142630515147/90850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1816461393953858789/1817000000000000000 : ℝ)*(X 0 2+X 1 2)+(142630515147/90850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (367/2500 : ℝ)) (c := (1816461393953858789/1817000000000000000 : ℝ)) (alpha := (142630515147/90850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1040411497/5000000000 : ℝ)*X 0 0+(1353702091/2500000000 : ℝ)*X 0 1+(655410717/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349662631/10000000000 : ℝ)*X 1 0+(-2168248007/10000000000 : ℝ)*X 1 1+(2621643077/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349661899/10000000000 : ℝ)*X 2 0+(2621643609/5000000000 : ℝ)*X 2 1+(-86729903/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4337726899/10000000000 : ℝ)*X 0 0+(520544613/1250000000 : ℝ)*X 0 1+(451795509/1000000000 : ℝ)*X 0 2+(4337726899/10000000000 : ℝ)*X 1 0+(520544613/1250000000 : ℝ)*X 1 1+(451795509/1000000000 : ℝ)*X 1 2+(4337726899/10000000000 : ℝ)*X 2 0+(520544613/1250000000 : ℝ)*X 2 1+(451795509/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2080836093/10000000000 : ℝ)*X 0 0+(2621948579/5000000000 : ℝ)*X 0 1+(2707096719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305704113/10000000000 : ℝ)*X 1 0+(-199734121/1000000000 : ℝ)*X 1 1+(5414193373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265285221/500000000 : ℝ)*X 2 0+(541419307/1000000000 : ℝ)*X 2 1+(-249667651/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2168875693/5000000000 : ℝ)*X 0 0+(451669449/1000000000 : ℝ)*X 0 1+(4165625513/10000000000 : ℝ)*X 0 2+(2168875693/5000000000 : ℝ)*X 1 0+(451669449/1000000000 : ℝ)*X 1 1+(4165625513/10000000000 : ℝ)*X 1 2+(2168875693/5000000000 : ℝ)*X 2 0+(451669449/1000000000 : ℝ)*X 2 1+(4165625513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37081384528409815825086801/22712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (234649851/10000000000000 : ℝ)*(base19) + (1035605789/100000000000000 : ℝ)*(base23) + (137254663/50000000000000 : ℝ)*(lower2) + (391037931/100000000000000 : ℝ)*(upper3) + (384871721/100000000000000 : ℝ)*(upper5) + (1082297026574397/25000000000000 : ℝ)*(major0) + (1082297026574397/25000000000000 : ℝ)*(major1) + (1082297026574397/25000000000000 : ℝ)*(major2) + (5830191006222847/100000000000000 : ℝ)*(sp0) + (2915122673482889/50000000000000 : ℝ)*(sp1) + (5830246657858499/100000000000000 : ℝ)*(sp2) + (353512362570173/12500000000000 : ℝ)*(sp3) + (354295259/625000000000 : ℝ)*(sp4) + (29564148087/100000000000000 : ℝ)*(sp7) + (2828128464709471/100000000000000 : ℝ)*(f.failure) + (182195240420759/3125000000000 : ℝ)*(f.sum) + (10671335933841/1135625000000000000000000000 : ℝ)*base66 + (501534968610555233/45425000000000000000000000000000 : ℝ)*base67 + (347652615879230233/45425000000000000000000000000000 : ℝ)*base69 + (511103603043705233/45425000000000000000000000000000 : ℝ)*base71 + (142466149823/141953125000000000000000000 : ℝ)*base73 + (379926727218269767/45425000000000000000000000000000 : ℝ)*base76 + (1000276902543430233/45425000000000000000000000000000 : ℝ)*base77 + (1179192118849894767/45425000000000000000000000000000 : ℝ)*base80 + (2165195807869/4542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (34574733/10000000000000000000000 : ℝ)*base90 + (34574733/10000000000000000000000 : ℝ)*base92 + (34574733/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132898053777114628299877767/45425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157885289/12500000000000 : ℝ)*(base19) + (315474041/12500000000000 : ℝ)*(base23) + (5705767/2000000000000 : ℝ)*(lower1) + (107886023/25000000000000 : ℝ)*(upper2) + (255768111/100000000000000 : ℝ)*(upper3) + (1707587/400000000000 : ℝ)*(upper5) + (2180133191951933/50000000000000 : ℝ)*(major0) + (2180133191951933/50000000000000 : ℝ)*(major1) + (2180133191951933/50000000000000 : ℝ)*(major2) + (12984797079/100000000000000 : ℝ)*(sp2) + (146802542523887/2500000000000 : ℝ)*(sp4) + (367006277367073/6250000000000 : ℝ)*(sp5) + (5872086192366073/100000000000000 : ℝ)*(sp6) + (71210774233257/2500000000000 : ℝ)*(sp7) + (71210774233257/2500000000000 : ℝ)*(f.failure) + (146802542523887/2500000000000 : ℝ)*(f.sum) + (1259483665199/2271250000000000000000000000 : ℝ)*base66 + (810739338756609137/90850000000000000000000000000000 : ℝ)*base67 + (2090008105942609137/90850000000000000000000000000000 : ℝ)*base69 + (1057576515326209137/90850000000000000000000000000000 : ℝ)*base71 + (4155044599149/2271250000000000000000000000 : ℝ)*base74 + (613334438672209137/90850000000000000000000000000000 : ℝ)*base75 + (1501197456253759137/90850000000000000000000000000000 : ℝ)*base77 + (399404653658409137/90850000000000000000000000000000 : ℝ)*base79 + (143347955494969/9085000000000000000000000000 : ℝ)*base81 + (507211/250000000000000000000 : ℝ)*base90 + (507211/250000000000000000000 : ℝ)*base92 + (507211/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1300_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (367/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1300_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1300_box_0 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1910145953/10000000000 : ℝ)*x 0 + (269584211/500000000 : ℝ)*x 1 + (5391684167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1910145953/10000000000 : ℝ)^1065 ≤ (2262544932401/20000000000000 : ℝ)^809 := by
    have hnat : (1910145953 : ℕ)^1065*20000000000000^809 ≤ 2262544932401^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1910145953 10000000000 2262544932401 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269584211/500000000 : ℝ)^1065 ≤ (44343637951393/100000000000000 : ℝ)^809 := by
    have hnat : (269584211 : ℕ)^1065*100000000000000^809 ≤ 44343637951393^809*500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269584211 500000000 44343637951393 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391684167/10000000000 : ℝ)^1065 ≤ (22171818688781/50000000000000 : ℝ)^809 := by
    have hnat : (5391684167 : ℕ)^1065*50000000000000^809 ≤ 22171818688781^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391684167 10000000000 22171818688781 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1910145953/10000000000 : ℝ), (269584211/500000000 : ℝ), (5391684167/10000000000 : ℝ)] ![(2262544932401/20000000000000 : ℝ), (44343637951393/100000000000000 : ℝ), (22171818688781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1910145953/10000000000 : ℝ)|^1065 ≤ (2262544932401/20000000000000 : ℝ)^809
        have hw : |(-1910145953/10000000000 : ℝ)|=(1910145953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269584211/500000000 : ℝ)|^1065 ≤ (44343637951393/100000000000000 : ℝ)^809
        have hw : |(269584211/500000000 : ℝ)|=(269584211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391684167/10000000000 : ℝ)|^1065 ≤ (22171818688781/50000000000000 : ℝ)^809
        have hw : |(5391684167/10000000000 : ℝ)|=(5391684167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_1 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (528451107/1000000000 : ℝ)*x 0 + (-1028378129/5000000000 : ℝ)*x 1 + (1078336807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528451107/1000000000 : ℝ)^1065 ≤ (21593470382977/50000000000000 : ℝ)^809 := by
    have hnat : (528451107 : ℕ)^1065*50000000000000^809 ≤ 21593470382977^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528451107 1000000000 21593470382977 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028378129/5000000000 : ℝ)^1065 ≤ (3117355818743/25000000000000 : ℝ)^809 := by
    have hnat : (1028378129 : ℕ)^1065*25000000000000^809 ≤ 3117355818743^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028378129 5000000000 3117355818743 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078336807/2000000000 : ℝ)^1065 ≤ (44343635948399/100000000000000 : ℝ)^809 := by
    have hnat : (1078336807 : ℕ)^1065*100000000000000^809 ≤ 44343635948399^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078336807 2000000000 44343635948399 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528451107/1000000000 : ℝ), (-1028378129/5000000000 : ℝ), (1078336807/2000000000 : ℝ)] ![(21593470382977/50000000000000 : ℝ), (3117355818743/25000000000000 : ℝ), (44343635948399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528451107/1000000000 : ℝ)|^1065 ≤ (21593470382977/50000000000000 : ℝ)^809
        have hw : |(528451107/1000000000 : ℝ)|=(528451107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1028378129/5000000000 : ℝ)|^1065 ≤ (3117355818743/25000000000000 : ℝ)^809
        have hw : |(-1028378129/5000000000 : ℝ)|=(1028378129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078336807/2000000000 : ℝ)|^1065 ≤ (44343635948399/100000000000000 : ℝ)^809
        have hw : |(1078336807/2000000000 : ℝ)|=(1078336807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_2 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5284510841/10000000000 : ℝ)*x 0 + (5391684281/10000000000 : ℝ)*x 1 + (-257094529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284510841/10000000000 : ℝ)^1065 ≤ (1727477532091/4000000000000 : ℝ)^809 := by
    have hnat : (5284510841 : ℕ)^1065*4000000000000^809 ≤ 1727477532091^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284510841 10000000000 1727477532091 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391684281/10000000000 : ℝ)^1065 ≤ (69286935331/156250000000 : ℝ)^809 := by
    have hnat : (5391684281 : ℕ)^1065*156250000000^809 ≤ 69286935331^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391684281 10000000000 69286935331 156250000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257094529/1250000000 : ℝ)^1065 ≤ (6234711533731/50000000000000 : ℝ)^809 := by
    have hnat : (257094529 : ℕ)^1065*50000000000000^809 ≤ 6234711533731^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257094529 1250000000 6234711533731 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284510841/10000000000 : ℝ), (5391684281/10000000000 : ℝ), (-257094529/1250000000 : ℝ)] ![(1727477532091/4000000000000 : ℝ), (69286935331/156250000000 : ℝ), (6234711533731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284510841/10000000000 : ℝ)|^1065 ≤ (1727477532091/4000000000000 : ℝ)^809
        have hw : |(5284510841/10000000000 : ℝ)|=(5284510841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391684281/10000000000 : ℝ)|^1065 ≤ (69286935331/156250000000 : ℝ)^809
        have hw : |(5391684281/10000000000 : ℝ)|=(5391684281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-257094529/1250000000 : ℝ)|^1065 ≤ (6234711533731/50000000000000 : ℝ)^809
        have hw : |(-257094529/1250000000 : ℝ)|=(257094529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_3 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4486946331/10000000000 : ℝ)*x 0 + (4267100829/10000000000 : ℝ)*x 1 + (4267100867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486946331/10000000000 : ℝ)^1065 ≤ (17409415758041/50000000000000 : ℝ)^809 := by
    have hnat : (4486946331 : ℕ)^1065*50000000000000^809 ≤ 17409415758041^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486946331 10000000000 17409415758041 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4267100829/10000000000 : ℝ)^1065 ≤ (16295292019289/50000000000000 : ℝ)^809 := by
    have hnat : (4267100829 : ℕ)^1065*50000000000000^809 ≤ 16295292019289^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267100829 10000000000 16295292019289 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4267100867/10000000000 : ℝ)^1065 ≤ (32590584420649/100000000000000 : ℝ)^809 := by
    have hnat : (4267100867 : ℕ)^1065*100000000000000^809 ≤ 32590584420649^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267100867 10000000000 32590584420649 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4486946331/10000000000 : ℝ), (4267100829/10000000000 : ℝ), (4267100867/10000000000 : ℝ)] ![(17409415758041/50000000000000 : ℝ), (16295292019289/50000000000000 : ℝ), (32590584420649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4486946331/10000000000 : ℝ)|^1065 ≤ (17409415758041/50000000000000 : ℝ)^809
        have hw : |(4486946331/10000000000 : ℝ)|=(4486946331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4267100829/10000000000 : ℝ)|^1065 ≤ (16295292019289/50000000000000 : ℝ)^809
        have hw : |(4267100829/10000000000 : ℝ)|=(4267100829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4267100867/10000000000 : ℝ)|^1065 ≤ (32590584420649/100000000000000 : ℝ)^809
        have hw : |(4267100867/10000000000 : ℝ)|=(4267100867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_4 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2254259117/10000000000 : ℝ)*x 0 + (526390749/1000000000 : ℝ)*x 1 + (1315976953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254259117/10000000000 : ℝ)^1065 ≤ (14069165430939/100000000000000 : ℝ)^809 := by
    have hnat : (2254259117 : ℕ)^1065*100000000000000^809 ≤ 14069165430939^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254259117 10000000000 14069165430939 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526390749/1000000000 : ℝ)^1065 ≤ (4296541554647/10000000000000 : ℝ)^809 := by
    have hnat : (526390749 : ℕ)^1065*10000000000000^809 ≤ 4296541554647^809*1000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526390749 1000000000 4296541554647 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315976953/2500000000 : ℝ)^1065 ≤ (42965419006403/100000000000000 : ℝ)^809 := by
    have hnat : (1315976953 : ℕ)^1065*100000000000000^809 ≤ 42965419006403^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315976953 2500000000 42965419006403 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2254259117/10000000000 : ℝ), (526390749/1000000000 : ℝ), (1315976953/2500000000 : ℝ)] ![(14069165430939/100000000000000 : ℝ), (4296541554647/10000000000000 : ℝ), (42965419006403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2254259117/10000000000 : ℝ)|^1065 ≤ (14069165430939/100000000000000 : ℝ)^809
        have hw : |(-2254259117/10000000000 : ℝ)|=(2254259117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526390749/1000000000 : ℝ)|^1065 ≤ (4296541554647/10000000000000 : ℝ)^809
        have hw : |(526390749/1000000000 : ℝ)|=(526390749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315976953/2500000000 : ℝ)|^1065 ≤ (42965419006403/100000000000000 : ℝ)^809
        have hw : |(1315976953/2500000000 : ℝ)|=(1315976953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_5 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5374419523/10000000000 : ℝ)*x 0 + (-2107721749/10000000000 : ℝ)*x 1 + (5263907951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374419523/10000000000 : ℝ)^1065 ≤ (11039201981547/25000000000000 : ℝ)^809 := by
    have hnat : (5374419523 : ℕ)^1065*25000000000000^809 ≤ 11039201981547^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374419523 10000000000 11039201981547 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107721749/10000000000 : ℝ)^1065 ≤ (643888577993/5000000000000 : ℝ)^809 := by
    have hnat : (2107721749 : ℕ)^1065*5000000000000^809 ≤ 643888577993^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107721749 10000000000 643888577993 5000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263907951/10000000000 : ℝ)^1065 ≤ (42965420499977/100000000000000 : ℝ)^809 := by
    have hnat : (5263907951 : ℕ)^1065*100000000000000^809 ≤ 42965420499977^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263907951 10000000000 42965420499977 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374419523/10000000000 : ℝ), (-2107721749/10000000000 : ℝ), (5263907951/10000000000 : ℝ)] ![(11039201981547/25000000000000 : ℝ), (643888577993/5000000000000 : ℝ), (42965420499977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374419523/10000000000 : ℝ)|^1065 ≤ (11039201981547/25000000000000 : ℝ)^809
        have hw : |(5374419523/10000000000 : ℝ)|=(5374419523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107721749/10000000000 : ℝ)|^1065 ≤ (643888577993/5000000000000 : ℝ)^809
        have hw : |(-2107721749/10000000000 : ℝ)|=(2107721749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263907951/10000000000 : ℝ)|^1065 ≤ (42965420499977/100000000000000 : ℝ)^809
        have hw : |(5263907951/10000000000 : ℝ)|=(5263907951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_6 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (107488391/200000000 : ℝ)*x 0 + (5263907811/10000000000 : ℝ)*x 1 + (-21077219/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107488391/200000000 : ℝ)^1065 ≤ (2207840410911/5000000000000 : ℝ)^809 := by
    have hnat : (107488391 : ℕ)^1065*5000000000000^809 ≤ 2207840410911^809*200000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107488391 200000000 2207840410911 5000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263907811/10000000000 : ℝ)^1065 ≤ (21482709497829/50000000000000 : ℝ)^809 := by
    have hnat : (5263907811 : ℕ)^1065*50000000000000^809 ≤ 21482709497829^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263907811 10000000000 21482709497829 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21077219/100000000 : ℝ)^1065 ≤ (12877772774383/100000000000000 : ℝ)^809 := by
    have hnat : (21077219 : ℕ)^1065*100000000000000^809 ≤ 12877772774383^809*100000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21077219 100000000 12877772774383 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107488391/200000000 : ℝ), (5263907811/10000000000 : ℝ), (-21077219/100000000 : ℝ)] ![(2207840410911/5000000000000 : ℝ), (21482709497829/50000000000000 : ℝ), (12877772774383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107488391/200000000 : ℝ)|^1065 ≤ (2207840410911/5000000000000 : ℝ)^809
        have hw : |(107488391/200000000 : ℝ)|=(107488391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263907811/10000000000 : ℝ)|^1065 ≤ (21482709497829/50000000000000 : ℝ)^809
        have hw : |(5263907811/10000000000 : ℝ)|=(5263907811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21077219/100000000 : ℝ)|^1065 ≤ (12877772774383/100000000000000 : ℝ)^809
        have hw : |(-21077219/100000000 : ℝ)|=(21077219/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_7 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1046910457/2500000000 : ℝ)*x 0 + (552087293/1250000000 : ℝ)*x 1 + (4416697717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046910457/2500000000 : ℝ)^1065 ≤ (6358805538507/20000000000000 : ℝ)^809 := by
    have hnat : (1046910457 : ℕ)^1065*20000000000000^809 ≤ 6358805538507^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046910457 2500000000 6358805538507 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552087293/1250000000 : ℝ)^1065 ≤ (8525747333181/25000000000000 : ℝ)^809 := by
    have hnat : (552087293 : ℕ)^1065*25000000000000^809 ≤ 8525747333181^809*1250000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552087293 1250000000 8525747333181 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4416697717/10000000000 : ℝ)^1065 ≤ (34102982959439/100000000000000 : ℝ)^809 := by
    have hnat : (4416697717 : ℕ)^1065*100000000000000^809 ≤ 34102982959439^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416697717 10000000000 34102982959439 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046910457/2500000000 : ℝ), (552087293/1250000000 : ℝ), (4416697717/10000000000 : ℝ)] ![(6358805538507/20000000000000 : ℝ), (8525747333181/25000000000000 : ℝ), (34102982959439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046910457/2500000000 : ℝ)|^1065 ≤ (6358805538507/20000000000000 : ℝ)^809
        have hw : |(1046910457/2500000000 : ℝ)|=(1046910457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552087293/1250000000 : ℝ)|^1065 ≤ (8525747333181/25000000000000 : ℝ)^809
        have hw : |(552087293/1250000000 : ℝ)|=(552087293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4416697717/10000000000 : ℝ)|^1065 ≤ (34102982959439/100000000000000 : ℝ)^809
        have hw : |(4416697717/10000000000 : ℝ)|=(4416697717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_8 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1091056621/5000000000 : ℝ)*x 0 + (5176145901/10000000000 : ℝ)*x 1 + (5405719997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091056621/5000000000 : ℝ)^1065 ≤ (2695886325149/20000000000000 : ℝ)^809 := by
    have hnat : (1091056621 : ℕ)^1065*20000000000000^809 ≤ 2695886325149^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091056621 5000000000 2695886325149 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176145901/10000000000 : ℝ)^1065 ≤ (42024902551547/100000000000000 : ℝ)^809 := by
    have hnat : (5176145901 : ℕ)^1065*100000000000000^809 ≤ 42024902551547^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176145901 10000000000 42024902551547 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405719997/10000000000 : ℝ)^1065 ≤ (22247832900489/50000000000000 : ℝ)^809 := by
    have hnat : (5405719997 : ℕ)^1065*50000000000000^809 ≤ 22247832900489^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405719997 10000000000 22247832900489 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1091056621/5000000000 : ℝ), (5176145901/10000000000 : ℝ), (5405719997/10000000000 : ℝ)] ![(2695886325149/20000000000000 : ℝ), (42024902551547/100000000000000 : ℝ), (22247832900489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1091056621/5000000000 : ℝ)|^1065 ≤ (2695886325149/20000000000000 : ℝ)^809
        have hw : |(-1091056621/5000000000 : ℝ)|=(1091056621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176145901/10000000000 : ℝ)|^1065 ≤ (42024902551547/100000000000000 : ℝ)^809
        have hw : |(5176145901/10000000000 : ℝ)|=(5176145901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405719997/10000000000 : ℝ)|^1065 ≤ (22247832900489/50000000000000 : ℝ)^809
        have hw : |(5405719997/10000000000 : ℝ)|=(5405719997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_9 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5274629037/10000000000 : ℝ)*x 0 + (-2051022193/10000000000 : ℝ)*x 1 + (5405719807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274629037/10000000000 : ℝ)^1065 ≤ (21540328559773/50000000000000 : ℝ)^809 := by
    have hnat : (5274629037 : ℕ)^1065*50000000000000^809 ≤ 21540328559773^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274629037 10000000000 21540328559773 50000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051022193/10000000000 : ℝ)^1065 ≤ (12423679131039/100000000000000 : ℝ)^809 := by
    have hnat : (2051022193 : ℕ)^1065*100000000000000^809 ≤ 12423679131039^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051022193 10000000000 12423679131039 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405719807/10000000000 : ℝ)^1065 ≤ (11123915935539/25000000000000 : ℝ)^809 := by
    have hnat : (5405719807 : ℕ)^1065*25000000000000^809 ≤ 11123915935539^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405719807 10000000000 11123915935539 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274629037/10000000000 : ℝ), (-2051022193/10000000000 : ℝ), (5405719807/10000000000 : ℝ)] ![(21540328559773/50000000000000 : ℝ), (12423679131039/100000000000000 : ℝ), (11123915935539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274629037/10000000000 : ℝ)|^1065 ≤ (21540328559773/50000000000000 : ℝ)^809
        have hw : |(5274629037/10000000000 : ℝ)|=(5274629037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051022193/10000000000 : ℝ)|^1065 ≤ (12423679131039/100000000000000 : ℝ)^809
        have hw : |(-2051022193/10000000000 : ℝ)|=(2051022193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405719807/10000000000 : ℝ)|^1065 ≤ (11123915935539/25000000000000 : ℝ)^809
        have hw : |(5405719807/10000000000 : ℝ)|=(5405719807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_10 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5274628943/10000000000 : ℝ)*x 0 + (1351429939/2500000000 : ℝ)*x 1 + (-2051022389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274628943/10000000000 : ℝ)^1065 ≤ (43080656108853/100000000000000 : ℝ)^809 := by
    have hnat : (5274628943 : ℕ)^1065*100000000000000^809 ≤ 43080656108853^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274628943 10000000000 43080656108853 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351429939/2500000000 : ℝ)^1065 ≤ (1779826527581/4000000000000 : ℝ)^809 := by
    have hnat : (1351429939 : ℕ)^1065*4000000000000^809 ≤ 1779826527581^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351429939 2500000000 1779826527581 4000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2051022389/10000000000 : ℝ)^1065 ≤ (310592017349/2500000000000 : ℝ)^809 := by
    have hnat : (2051022389 : ℕ)^1065*2500000000000^809 ≤ 310592017349^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051022389 10000000000 310592017349 2500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274628943/10000000000 : ℝ), (1351429939/2500000000 : ℝ), (-2051022389/10000000000 : ℝ)] ![(43080656108853/100000000000000 : ℝ), (1779826527581/4000000000000 : ℝ), (310592017349/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274628943/10000000000 : ℝ)|^1065 ≤ (43080656108853/100000000000000 : ℝ)^809
        have hw : |(5274628943/10000000000 : ℝ)|=(5274628943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351429939/2500000000 : ℝ)|^1065 ≤ (1779826527581/4000000000000 : ℝ)^809
        have hw : |(1351429939/2500000000 : ℝ)|=(1351429939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2051022389/10000000000 : ℝ)|^1065 ≤ (310592017349/2500000000000 : ℝ)^809
        have hw : |(-2051022389/10000000000 : ℝ)|=(2051022389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_11 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4519263391/10000000000 : ℝ)*x 0 + (4250654643/10000000000 : ℝ)*x 1 + (850130941/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4519263391/10000000000 : ℝ)^1065 ≤ (35149345674497/100000000000000 : ℝ)^809 := by
    have hnat : (4519263391 : ℕ)^1065*100000000000000^809 ≤ 35149345674497^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519263391 10000000000 35149345674497 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250654643/10000000000 : ℝ)^1065 ≤ (6485065369131/20000000000000 : ℝ)^809 := by
    have hnat : (4250654643 : ℕ)^1065*20000000000000^809 ≤ 6485065369131^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250654643 10000000000 6485065369131 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850130941/2000000000 : ℝ)^1065 ≤ (32425327468273/100000000000000 : ℝ)^809 := by
    have hnat : (850130941 : ℕ)^1065*100000000000000^809 ≤ 32425327468273^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850130941 2000000000 32425327468273 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4519263391/10000000000 : ℝ), (4250654643/10000000000 : ℝ), (850130941/2000000000 : ℝ)] ![(35149345674497/100000000000000 : ℝ), (6485065369131/20000000000000 : ℝ), (32425327468273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4519263391/10000000000 : ℝ)|^1065 ≤ (35149345674497/100000000000000 : ℝ)^809
        have hw : |(4519263391/10000000000 : ℝ)|=(4519263391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250654643/10000000000 : ℝ)|^1065 ≤ (6485065369131/20000000000000 : ℝ)^809
        have hw : |(4250654643/10000000000 : ℝ)|=(4250654643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850130941/2000000000 : ℝ)|^1065 ≤ (32425327468273/100000000000000 : ℝ)^809
        have hw : |(850130941/2000000000 : ℝ)|=(850130941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_12 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-495678411/2500000000 : ℝ)*x 0 + (2738571077/5000000000 : ℝ)*x 1 + (1050575277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (495678411/2500000000 : ℝ)^1065 ≤ (95054985583/800000000000 : ℝ)^809 := by
    have hnat : (495678411 : ℕ)^1065*800000000000^809 ≤ 95054985583^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495678411 2500000000 95054985583 800000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738571077/5000000000 : ℝ)^1065 ≤ (11317800656541/25000000000000 : ℝ)^809 := by
    have hnat : (2738571077 : ℕ)^1065*25000000000000^809 ≤ 11317800656541^809*5000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738571077 5000000000 11317800656541 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050575277/2000000000 : ℝ)^1065 ≤ (5355865519967/12500000000000 : ℝ)^809 := by
    have hnat : (1050575277 : ℕ)^1065*12500000000000^809 ≤ 5355865519967^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050575277 2000000000 5355865519967 12500000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-495678411/2500000000 : ℝ), (2738571077/5000000000 : ℝ), (1050575277/2000000000 : ℝ)] ![(95054985583/800000000000 : ℝ), (11317800656541/25000000000000 : ℝ), (5355865519967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-495678411/2500000000 : ℝ)|^1065 ≤ (95054985583/800000000000 : ℝ)^809
        have hw : |(-495678411/2500000000 : ℝ)|=(495678411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738571077/5000000000 : ℝ)|^1065 ≤ (11317800656541/25000000000000 : ℝ)^809
        have hw : |(2738571077/5000000000 : ℝ)|=(2738571077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050575277/2000000000 : ℝ)|^1065 ≤ (5355865519967/12500000000000 : ℝ)^809
        have hw : |(1050575277/2000000000 : ℝ)|=(1050575277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_13 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1345544677/2500000000 : ℝ)*x 0 + (-2112016279/10000000000 : ℝ)*x 1 + (1050575293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345544677/2500000000 : ℝ)^1065 ≤ (44240750534561/100000000000000 : ℝ)^809 := by
    have hnat : (1345544677 : ℕ)^1065*100000000000000^809 ≤ 44240750534561^809*2500000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345544677 2500000000 44240750534561 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112016279/10000000000 : ℝ)^1065 ≤ (12912324426661/100000000000000 : ℝ)^809 := by
    have hnat : (2112016279 : ℕ)^1065*100000000000000^809 ≤ 12912324426661^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112016279 10000000000 12912324426661 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050575293/2000000000 : ℝ)^1065 ≤ (42846925018777/100000000000000 : ℝ)^809 := by
    have hnat : (1050575293 : ℕ)^1065*100000000000000^809 ≤ 42846925018777^809*2000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050575293 2000000000 42846925018777 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345544677/2500000000 : ℝ), (-2112016279/10000000000 : ℝ), (1050575293/2000000000 : ℝ)] ![(44240750534561/100000000000000 : ℝ), (12912324426661/100000000000000 : ℝ), (42846925018777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345544677/2500000000 : ℝ)|^1065 ≤ (44240750534561/100000000000000 : ℝ)^809
        have hw : |(1345544677/2500000000 : ℝ)|=(1345544677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112016279/10000000000 : ℝ)|^1065 ≤ (12912324426661/100000000000000 : ℝ)^809
        have hw : |(-2112016279/10000000000 : ℝ)|=(2112016279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050575293/2000000000 : ℝ)|^1065 ≤ (42846925018777/100000000000000 : ℝ)^809
        have hw : |(1050575293/2000000000 : ℝ)|=(1050575293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_14 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5382178941/10000000000 : ℝ)*x 0 + (5252876291/10000000000 : ℝ)*x 1 + (-2112016199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382178941/10000000000 : ℝ)^1065 ≤ (44240753055843/100000000000000 : ℝ)^809 := by
    have hnat : (5382178941 : ℕ)^1065*100000000000000^809 ≤ 44240753055843^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382178941 10000000000 44240753055843 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252876291/10000000000 : ℝ)^1065 ≤ (10711730787591/25000000000000 : ℝ)^809 := by
    have hnat : (5252876291 : ℕ)^1065*25000000000000^809 ≤ 10711730787591^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252876291 10000000000 10711730787591 25000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112016199/10000000000 : ℝ)^1065 ≤ (12912323782791/100000000000000 : ℝ)^809 := by
    have hnat : (2112016199 : ℕ)^1065*100000000000000^809 ≤ 12912323782791^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112016199 10000000000 12912323782791 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382178941/10000000000 : ℝ), (5252876291/10000000000 : ℝ), (-2112016199/10000000000 : ℝ)] ![(44240753055843/100000000000000 : ℝ), (10711730787591/25000000000000 : ℝ), (12912323782791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382178941/10000000000 : ℝ)|^1065 ≤ (44240753055843/100000000000000 : ℝ)^809
        have hw : |(5382178941/10000000000 : ℝ)|=(5382178941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252876291/10000000000 : ℝ)|^1065 ≤ (10711730787591/25000000000000 : ℝ)^809
        have hw : |(5252876291/10000000000 : ℝ)|=(5252876291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112016199/10000000000 : ℝ)|^1065 ≤ (12912323782791/100000000000000 : ℝ)^809
        have hw : |(-2112016199/10000000000 : ℝ)|=(2112016199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1300_box_15 (p : ℝ) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4161355489/10000000000 : ℝ)*x 0 + (4429602633/10000000000 : ℝ)*x 1 + (4429602873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161355489/10000000000 : ℝ)^1065 ≤ (3153156048571/10000000000000 : ℝ)^809 := by
    have hnat : (4161355489 : ℕ)^1065*10000000000000^809 ≤ 3153156048571^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161355489 10000000000 3153156048571 10000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429602633/10000000000 : ℝ)^1065 ≤ (6846843705271/20000000000000 : ℝ)^809 := by
    have hnat : (4429602633 : ℕ)^1065*20000000000000^809 ≤ 6846843705271^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429602633 10000000000 6846843705271 20000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429602873/10000000000 : ℝ)^1065 ≤ (34234220968143/100000000000000 : ℝ)^809 := by
    have hnat : (4429602873 : ℕ)^1065*100000000000000^809 ≤ 34234220968143^809*10000000000^1065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429602873 10000000000 34234220968143 100000000000000 1065 809 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1065/256 : ℝ)) 1065 809 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161355489/10000000000 : ℝ), (4429602633/10000000000 : ℝ), (4429602873/10000000000 : ℝ)] ![(3153156048571/10000000000000 : ℝ), (6846843705271/20000000000000 : ℝ), (34234220968143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161355489/10000000000 : ℝ)|^1065 ≤ (3153156048571/10000000000000 : ℝ)^809
        have hw : |(4161355489/10000000000 : ℝ)|=(4161355489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429602633/10000000000 : ℝ)|^1065 ≤ (6846843705271/20000000000000 : ℝ)^809
        have hw : |(4429602633/10000000000 : ℝ)|=(4429602633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4429602873/10000000000 : ℝ)|^1065 ≤ (34234220968143/100000000000000 : ℝ)^809
        have hw : |(4429602873/10000000000 : ℝ)|=(4429602873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1300_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(62841/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2943/5000 : ℝ) ∧ (15941/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84187/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1381/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1381/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1381/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1381/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1381/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1381/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1381/12500 : ℝ) ^ (4259/1024 : ℝ) ≤ (10491675631239333/100000000000000000000 : ℝ) := by
    have hpowers : (1381/12500 : ℝ)^4259 ≤ (10491675631239333/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1381 : ℕ)^4259*100000000000000000000^1024 ≤ 10491675631239333^1024*12500^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1381 12500 10491675631239333 100000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1381/12500 : ℝ)) (X := (10491675631239333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7339/50000 : ℝ) ^ (4259/1024 : ℝ) ≤ (17099674075592061/50000000000000000000 : ℝ) := by
    have hpowers : (7339/50000 : ℝ)^4259 ≤ (17099674075592061/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7339 : ℕ)^4259*50000000000000000000^1024 ≤ 17099674075592061^1024*50000^4259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 50000 17099674075592061 50000000000000000000 4259 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/50000 : ℝ)) (X := (17099674075592061/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010491675631239333/50000000000000000000 : ℝ) ≤ (2500126116691583/2500000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (50010491675631239333/50000000000000000000 : ℝ)^1024 ≤ (2500126116691583/2500000000000000 : ℝ)^4259 := by
      have hnat : (50010491675631239333 : ℕ)^1024*2500000000000000^4259 ≤ 2500126116691583^4259*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010491675631239333 50000000000000000000 2500126116691583 2500000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500126116691583/2500000000000000 : ℝ)) (X := (50010491675631239333/50000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008938204756484691/20000000000000000000 : ℝ) ≤ (10001074333011529/10000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (20008938204756484691/20000000000000000000 : ℝ)^1024 ≤ (10001074333011529/10000000000000000 : ℝ)^4259 := by
      have hnat : (20008938204756484691 : ℕ)^1024*10000000000000000^4259 ≤ 10001074333011529^4259*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008938204756484691 20000000000000000000 10001074333011529 10000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001074333011529/10000000000000000 : ℝ)) (X := (20008938204756484691/20000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017099674075592061/25000000000000000000 : ℝ) ≤ (5000822099628363/5000000000000000 : ℝ) ^ (4259/1024 : ℝ) := by
    have hpowers : (25017099674075592061/25000000000000000000 : ℝ)^1024 ≤ (5000822099628363/5000000000000000 : ℝ)^4259 := by
      have hnat : (25017099674075592061 : ℕ)^1024*5000000000000000^4259 ≤ 5000822099628363^4259*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017099674075592061 25000000000000000000 5000822099628363 5000000000000000 1024 4259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000822099628363/5000000000000000 : ℝ)) (X := (25017099674075592061/25000000000000000000 : ℝ)) (by norm_num) 4259 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10491675631239333/100000000000000000000 : ℝ) ≤ ((4536154931225989031/4537500000000000000 : ℝ)+2*(569866245197/363000000000000 : ℝ)*(1381/12500 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (4536154931225989031/4537500000000000000 : ℝ)+2*(569866245197/363000000000000 : ℝ)*(1381/12500 : ℝ)=(2500126116691583/2500000000000000 : ℝ) by norm_num, show 1+2*(10491675631239333/100000000000000000000 : ℝ)=(50010491675631239333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17099674075592061/50000000000000000000 : ℝ)+(10491675631239333/100000000000000000000 : ℝ) ≤ ((4536154931225989031/4537500000000000000 : ℝ)+(569866245197/363000000000000 : ℝ)*((7339/50000 : ℝ)+(1381/12500 : ℝ)))^(4259/1024 : ℝ) := by
    rw [show (4536154931225989031/4537500000000000000 : ℝ)+(569866245197/363000000000000 : ℝ)*((7339/50000 : ℝ)+(1381/12500 : ℝ))=(10001074333011529/10000000000000000 : ℝ) by norm_num, show 1+(17099674075592061/50000000000000000000 : ℝ)+(10491675631239333/100000000000000000000 : ℝ)=(20008938204756484691/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17099674075592061/50000000000000000000 : ℝ) ≤ ((4536154931225989031/4537500000000000000 : ℝ)+2*(569866245197/363000000000000 : ℝ)*(7339/50000 : ℝ))^(4259/1024 : ℝ) := by
    rw [show (4536154931225989031/4537500000000000000 : ℝ)+2*(569866245197/363000000000000 : ℝ)*(7339/50000 : ℝ)=(5000822099628363/5000000000000000 : ℝ) by norm_num, show 1+2*(17099674075592061/50000000000000000000 : ℝ)=(25017099674075592061/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4536154931225989031/4537500000000000000 : ℝ)*(X 1 0+X 2 0)+(569866245197/363000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (4536154931225989031/4537500000000000000 : ℝ)) (alpha := (569866245197/363000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4536154931225989031/4537500000000000000 : ℝ)*(X 0 1+X 2 1)+(569866245197/363000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (4536154931225989031/4537500000000000000 : ℝ)) (alpha := (569866245197/363000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4536154931225989031/4537500000000000000 : ℝ)*(X 0 2+X 1 2)+(569866245197/363000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4259/1024 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (4536154931225989031/4537500000000000000 : ℝ)) (alpha := (569866245197/363000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1910145953/10000000000 : ℝ)*X 0 0+(269584211/500000000 : ℝ)*X 0 1+(5391684167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528451107/1000000000 : ℝ)*X 1 0+(-1028378129/5000000000 : ℝ)*X 1 1+(1078336807/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284510841/10000000000 : ℝ)*X 2 0+(5391684281/10000000000 : ℝ)*X 2 1+(-257094529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4486946331/10000000000 : ℝ)*X 0 0+(4267100829/10000000000 : ℝ)*X 0 1+(4267100867/10000000000 : ℝ)*X 0 2+(4486946331/10000000000 : ℝ)*X 1 0+(4267100829/10000000000 : ℝ)*X 1 1+(4267100867/10000000000 : ℝ)*X 1 2+(4486946331/10000000000 : ℝ)*X 2 0+(4267100829/10000000000 : ℝ)*X 2 1+(4267100867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2254259117/10000000000 : ℝ)*X 0 0+(526390749/1000000000 : ℝ)*X 0 1+(1315976953/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374419523/10000000000 : ℝ)*X 1 0+(-2107721749/10000000000 : ℝ)*X 1 1+(5263907951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((107488391/200000000 : ℝ)*X 2 0+(5263907811/10000000000 : ℝ)*X 2 1+(-21077219/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1046910457/2500000000 : ℝ)*X 0 0+(552087293/1250000000 : ℝ)*X 0 1+(4416697717/10000000000 : ℝ)*X 0 2+(1046910457/2500000000 : ℝ)*X 1 0+(552087293/1250000000 : ℝ)*X 1 1+(4416697717/10000000000 : ℝ)*X 1 2+(1046910457/2500000000 : ℝ)*X 2 0+(552087293/1250000000 : ℝ)*X 2 1+(4416697717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1091056621/5000000000 : ℝ)*X 0 0+(5176145901/10000000000 : ℝ)*X 0 1+(5405719997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274629037/10000000000 : ℝ)*X 1 0+(-2051022193/10000000000 : ℝ)*X 1 1+(5405719807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274628943/10000000000 : ℝ)*X 2 0+(1351429939/2500000000 : ℝ)*X 2 1+(-2051022389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4519263391/10000000000 : ℝ)*X 0 0+(4250654643/10000000000 : ℝ)*X 0 1+(850130941/2000000000 : ℝ)*X 0 2+(4519263391/10000000000 : ℝ)*X 1 0+(4250654643/10000000000 : ℝ)*X 1 1+(850130941/2000000000 : ℝ)*X 1 2+(4519263391/10000000000 : ℝ)*X 2 0+(4250654643/10000000000 : ℝ)*X 2 1+(850130941/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-495678411/2500000000 : ℝ)*X 0 0+(2738571077/5000000000 : ℝ)*X 0 1+(1050575277/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345544677/2500000000 : ℝ)*X 1 0+(-2112016279/10000000000 : ℝ)*X 1 1+(1050575293/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382178941/10000000000 : ℝ)*X 2 0+(5252876291/10000000000 : ℝ)*X 2 1+(-2112016199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4161355489/10000000000 : ℝ)*X 0 0+(4429602633/10000000000 : ℝ)*X 0 1+(4429602873/10000000000 : ℝ)*X 0 2+(4161355489/10000000000 : ℝ)*X 1 0+(4429602633/10000000000 : ℝ)*X 1 1+(4429602873/10000000000 : ℝ)*X 1 2+(4161355489/10000000000 : ℝ)*X 2 0+(4429602633/10000000000 : ℝ)*X 2 1+(4429602873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1300_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62841/100000 : ℝ) ≤ (-2376093144319843220507565073107/3781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (58504841/100000000000000 : ℝ)*(lower0) + (42332527/50000000000000 : ℝ)*(upper1) + (49582347/100000000000000 : ℝ)*(lower4) + (287315070195447/10000000000000 : ℝ)*(major0) + (287315070195447/10000000000000 : ℝ)*(major1) + (287315070195447/10000000000000 : ℝ)*(major2) + (269820509/50000000000000 : ℝ)*(sp3) + (972576025917529/25000000000000 : ℝ)*(sp4) + (972544584032393/25000000000000 : ℝ)*(sp5) + (3890255776191887/100000000000000 : ℝ)*(sp6) + (187694245384481/10000000000000 : ℝ)*(sp7) + (582405391/100000000000000 : ℝ)*(sp12) + (7896871621/6250000000000 : ℝ)*(sp13) + (2445494181/5000000000000 : ℝ)*(sp14) + (1876942993485827/100000000000000 : ℝ)*(f.failure) + (972576171518877/25000000000000 : ℝ)*(f.sum) + (2875033894157/605000000000000000000000000 : ℝ)*base66 + (151488869399293119/15125000000000000000000000000000 : ℝ)*base67 + (39402342158418119/15125000000000000000000000000000 : ℝ)*base69 + (99541106051043119/15125000000000000000000000000000 : ℝ)*base71 + (8788622120403/605000000000000000000000000 : ℝ)*base73 + (47117824197793119/15125000000000000000000000000000 : ℝ)*base75 + (149993985607793119/15125000000000000000000000000000 : ℝ)*base77 + (105891164161081881/15125000000000000000000000000000 : ℝ)*base80 + (562881456727/605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (47739321/10000000000000000000000 : ℝ)*base90 + (47739321/10000000000000000000000 : ℝ)*base92 + (47739321/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (2943/5000 : ℝ) ≤ (2782185454912528400571518689229/4726562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3061433/50000000000000 : ℝ)*(lower0) + (1028419/4000000000000 : ℝ)*(upper2) + (4883177/50000000000000 : ℝ)*(lower4) + (7863093/100000000000000 : ℝ)*(lower5) + (367555696043293/12500000000000 : ℝ)*(major0) + (367555696043293/12500000000000 : ℝ)*(major1) + (367555696043293/12500000000000 : ℝ)*(major2) + (985091376875193/25000000000000 : ℝ)*(sp0) + (985082112542411/25000000000000 : ℝ)*(sp1) + (3940363490191873/100000000000000 : ℝ)*(sp2) + (480225878640409/25000000000000 : ℝ)*(sp3) + (20173089/1000000000000 : ℝ)*(sp6) + (596206901/50000000000000 : ℝ)*(sp7) + (37057331129/100000000000000 : ℝ)*(sp9) + (1920904706975437/100000000000000 : ℝ)*(f.failure) + (985091376875193/25000000000000 : ℝ)*(f.sum) + (17447049334579/2268750000000000000000000000 : ℝ)*base66 + (90549606244581139/18906250000000000000000000000000 : ℝ)*base68 + (55729044511981361/18906250000000000000000000000000 : ℝ)*base69 + (344552455590362389/18906250000000000000000000000000 : ℝ)*base72 + (299266005351659/9075000000000000000000000000 : ℝ)*base73 + (115499732831612389/18906250000000000000000000000000 : ℝ)*base76 + (282998211705987389/18906250000000000000000000000000 : ℝ)*base78 + (642868291703387611/18906250000000000000000000000000 : ℝ)*base79 + (22945609064183/4537500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (31320649/10000000000000000000000 : ℝ)*base89 + (31320649/10000000000000000000000 : ℝ)*base91 + (31320649/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (15941/20000 : ℝ) ≤ (3013934518433112627220397913899/3781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2195471/20000000000000 : ℝ)*(upper0) + (70561959/100000000000000 : ℝ)*(upper2) + (13197569/20000000000000 : ℝ)*(lower5) + (325415535140471/10000000000000 : ℝ)*(major0) + (325415535140471/10000000000000 : ℝ)*(major1) + (325415535140471/10000000000000 : ℝ)*(major2) + (936564041/3125000000000 : ℝ)*(sp1) + (40507212073/100000000000000 : ℝ)*(sp3) + (2614727153/50000000000000 : ℝ)*(sp4) + (4355891159779411/100000000000000 : ℝ)*(sp8) + (4355869734163523/100000000000000 : ℝ)*(sp9) + (2177949852106417/50000000000000 : ℝ)*(sp10) + (85032054866511/4000000000000 : ℝ)*(sp11) + (1657489559/50000000000000 : ℝ)*(sp12) + (66432558714839/3125000000000 : ℝ)*(f.failure) + (2177949852106417/50000000000000 : ℝ)*(f.sum) + (9499147141207/1815000000000000000000000000 : ℝ)*base65 + (139292598603954633/15125000000000000000000000000000 : ℝ)*base68 + (140517434962295367/15125000000000000000000000000000 : ℝ)*base69 + (145697701421795367/15125000000000000000000000000000 : ℝ)*base71 + (3547147600459/907500000000000000000000000 : ℝ)*base74 + (128133307118295367/15125000000000000000000000000000 : ℝ)*base75 + (202922333197920367/15125000000000000000000000000000 : ℝ)*base77 + (131792593670920367/15125000000000000000000000000000 : ℝ)*base79 + (1707237237187/1815000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2943397/312500000000000000000 : ℝ)*base90 + (2943397/312500000000000000000 : ℝ)*base92 + (2943397/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84187/100000 : ℝ) ≤ (-5093147534538333099669641883/6050000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840203/10000000000000 : ℝ)*(lower1) + (6038723/12500000000000 : ℝ)*(lower2) + (2918273/20000000000000 : ℝ)*(lower4) + (58845787/50000000000000 : ℝ)*(upper5) + (3290144334316363/100000000000000 : ℝ)*(major0) + (3290144334316363/100000000000000 : ℝ)*(major1) + (3290144334316363/100000000000000 : ℝ)*(major2) + (18524468551/100000000000000 : ℝ)*(sp5) + (21792871617/20000000000000 : ℝ)*(sp6) + (3121176793/100000000000000 : ℝ)*(sp8) + (2229497283355753/50000000000000 : ℝ)*(sp12) + (1114744790854937/25000000000000 : ℝ)*(sp13) + (2229444361765107/50000000000000 : ℝ)*(sp14) + (429870479933499/20000000000000 : ℝ)*(sp15) + (429870479933499/20000000000000 : ℝ)*(f.failure) + (2229498843944149/50000000000000 : ℝ)*(f.sum) + (76291227735761/18150000000000000000000000000 : ℝ)*base65 + (277641800438932749/151250000000000000000000000000000 : ℝ)*base68 + (129717583943567251/151250000000000000000000000000000 : ℝ)*base69 + (1350149963263932749/151250000000000000000000000000000 : ℝ)*base72 + (54974567124911/18150000000000000000000000000 : ℝ)*base73 + (768572719956067251/151250000000000000000000000000000 : ℝ)*base75 + (109966358727317251/151250000000000000000000000000000 : ℝ)*base77 + (447428817728932749/151250000000000000000000000000000 : ℝ)*base80 + (73396924119161/18150000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12196577/2000000000000000000000 : ℝ)*base90 + (12196577/2000000000000000000000 : ℝ)*base92 + (12196577/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1300_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2943/5000 : ℝ) else (15941/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84187/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1300_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1300_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2943/5000 : ℝ) else (15941/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84187/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1300_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1300_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1300_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4259/1024 : ℝ) ≤ p) (hpb : p ≤ (1065/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153076077/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14691/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2759/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2943/5000 : ℝ) else (15941/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84187/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1300_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

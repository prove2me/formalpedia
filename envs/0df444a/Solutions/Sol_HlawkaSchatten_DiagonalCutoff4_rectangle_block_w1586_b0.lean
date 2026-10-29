-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1586_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:31:29.926096+00:00
-- url     : https://prove2.me/submissions/436e8606-57fb-4ee7-99e5-807d035fd273

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
theorem support_rectangle_w1586_s0_0 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-201260279/1250000000 : ℝ)*x 0 + (2929039831/5000000000 : ℝ)*x 1 + (4885711823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201260279/1250000000 : ℝ)^4669 ≤ (1204857503127/12500000000000 : ℝ)^3645 := by
    have hnat : (201260279 : ℕ)^4669*12500000000000^3645 ≤ 1204857503127^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201260279 1250000000 1204857503127 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2929039831/5000000000 : ℝ)^4669 ≤ (50409236005753/100000000000000 : ℝ)^3645 := by
    have hnat : (2929039831 : ℕ)^4669*100000000000000^3645 ≤ 50409236005753^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929039831 5000000000 50409236005753 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885711823/10000000000 : ℝ)^4669 ≤ (39951903958943/100000000000000 : ℝ)^3645 := by
    have hnat : (4885711823 : ℕ)^4669*100000000000000^3645 ≤ 39951903958943^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885711823 10000000000 39951903958943 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201260279/1250000000 : ℝ), (2929039831/5000000000 : ℝ), (4885711823/10000000000 : ℝ)] ![(1204857503127/12500000000000 : ℝ), (50409236005753/100000000000000 : ℝ), (39951903958943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201260279/1250000000 : ℝ)|^4669 ≤ (1204857503127/12500000000000 : ℝ)^3645
        have hw : |(-201260279/1250000000 : ℝ)|=(201260279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2929039831/5000000000 : ℝ)|^4669 ≤ (50409236005753/100000000000000 : ℝ)^3645
        have hw : |(2929039831/5000000000 : ℝ)|=(2929039831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4885711823/10000000000 : ℝ)|^4669 ≤ (39951903958943/100000000000000 : ℝ)^3645
        have hw : |(4885711823/10000000000 : ℝ)|=(4885711823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_1 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092415179/2000000000 : ℝ)*x 0 + (-1075075897/5000000000 : ℝ)*x 1 + (4885711719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092415179/2000000000 : ℝ)^4669 ≤ (46086412865317/100000000000000 : ℝ)^3645 := by
    have hnat : (1092415179 : ℕ)^4669*100000000000000^3645 ≤ 46086412865317^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092415179 2000000000 46086412865317 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075075897/5000000000 : ℝ)^4669 ≤ (3490421063359/25000000000000 : ℝ)^3645 := by
    have hnat : (1075075897 : ℕ)^4669*25000000000000^3645 ≤ 3490421063359^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075075897 5000000000 3490421063359 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4885711719/10000000000 : ℝ)^4669 ≤ (39951902869589/100000000000000 : ℝ)^3645 := by
    have hnat : (4885711719 : ℕ)^4669*100000000000000^3645 ≤ 39951902869589^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4885711719 10000000000 39951902869589 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092415179/2000000000 : ℝ), (-1075075897/5000000000 : ℝ), (4885711719/10000000000 : ℝ)] ![(46086412865317/100000000000000 : ℝ), (3490421063359/25000000000000 : ℝ), (39951902869589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092415179/2000000000 : ℝ)|^4669 ≤ (46086412865317/100000000000000 : ℝ)^3645
        have hw : |(1092415179/2000000000 : ℝ)|=(1092415179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075075897/5000000000 : ℝ)|^4669 ≤ (3490421063359/25000000000000 : ℝ)^3645
        have hw : |(-1075075897/5000000000 : ℝ)|=(1075075897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4885711719/10000000000 : ℝ)|^4669 ≤ (39951902869589/100000000000000 : ℝ)^3645
        have hw : |(4885711719/10000000000 : ℝ)|=(4885711719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_2 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85344937/156250000 : ℝ)*x 0 + (977142321/2000000000 : ℝ)*x 1 + (-1075075921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85344937/156250000 : ℝ)^4669 ≤ (23043206827147/50000000000000 : ℝ)^3645 := by
    have hnat : (85344937 : ℕ)^4669*50000000000000^3645 ≤ 23043206827147^3645*156250000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85344937 156250000 23043206827147 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977142321/2000000000 : ℝ)^4669 ≤ (1248496927359/3125000000000 : ℝ)^3645 := by
    have hnat : (977142321 : ℕ)^4669*3125000000000^3645 ≤ 1248496927359^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977142321 2000000000 1248496927359 3125000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075075921/5000000000 : ℝ)^4669 ≤ (6980842326339/50000000000000 : ℝ)^3645 := by
    have hnat : (1075075921 : ℕ)^4669*50000000000000^3645 ≤ 6980842326339^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075075921 5000000000 6980842326339 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85344937/156250000 : ℝ), (977142321/2000000000 : ℝ), (-1075075921/5000000000 : ℝ)] ![(23043206827147/50000000000000 : ℝ), (1248496927359/3125000000000 : ℝ), (6980842326339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85344937/156250000 : ℝ)|^4669 ≤ (23043206827147/50000000000000 : ℝ)^3645
        have hw : |(85344937/156250000 : ℝ)|=(85344937/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(977142321/2000000000 : ℝ)|^4669 ≤ (1248496927359/3125000000000 : ℝ)^3645
        have hw : |(977142321/2000000000 : ℝ)|=(977142321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075075921/5000000000 : ℝ)|^4669 ≤ (6980842326339/50000000000000 : ℝ)^3645
        have hw : |(-1075075921/5000000000 : ℝ)|=(1075075921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_3 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825149067/2000000000 : ℝ)*x 0 + (77353653/250000000 : ℝ)*x 1 + (1082904103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825149067/2000000000 : ℝ)^4669 ≤ (16086236337217/50000000000000 : ℝ)^3645 := by
    have hnat : (825149067 : ℕ)^4669*50000000000000^3645 ≤ 16086236337217^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825149067 2000000000 16086236337217 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77353653/250000000 : ℝ)^4669 ≤ (22254458579259/100000000000000 : ℝ)^3645 := by
    have hnat : (77353653 : ℕ)^4669*100000000000000^3645 ≤ 22254458579259^3645*250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77353653 250000000 22254458579259 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082904103/2000000000 : ℝ)^4669 ≤ (9114613745451/20000000000000 : ℝ)^3645 := by
    have hnat : (1082904103 : ℕ)^4669*20000000000000^3645 ≤ 9114613745451^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082904103 2000000000 9114613745451 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825149067/2000000000 : ℝ), (77353653/250000000 : ℝ), (1082904103/2000000000 : ℝ)] ![(16086236337217/50000000000000 : ℝ), (22254458579259/100000000000000 : ℝ), (9114613745451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825149067/2000000000 : ℝ)|^4669 ≤ (16086236337217/50000000000000 : ℝ)^3645
        have hw : |(825149067/2000000000 : ℝ)|=(825149067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77353653/250000000 : ℝ)|^4669 ≤ (22254458579259/100000000000000 : ℝ)^3645
        have hw : |(77353653/250000000 : ℝ)|=(77353653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082904103/2000000000 : ℝ)|^4669 ≤ (9114613745451/20000000000000 : ℝ)^3645
        have hw : |(1082904103/2000000000 : ℝ)|=(1082904103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_4 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12904143/80000000 : ℝ)*x 0 + (982025543/2000000000 : ℝ)*x 1 + (58328031/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12904143/80000000 : ℝ)^4669 ≤ (386455097249/4000000000000 : ℝ)^3645 := by
    have hnat : (12904143 : ℕ)^4669*4000000000000^3645 ≤ 386455097249^3645*80000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12904143 80000000 386455097249 4000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982025543/2000000000 : ℝ)^4669 ≤ (8041565821027/20000000000000 : ℝ)^3645 := by
    have hnat : (982025543 : ℕ)^4669*20000000000000^3645 ≤ 8041565821027^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982025543 2000000000 8041565821027 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58328031/100000000 : ℝ)^4669 ≤ (25065396724377/50000000000000 : ℝ)^3645 := by
    have hnat : (58328031 : ℕ)^4669*50000000000000^3645 ≤ 25065396724377^3645*100000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58328031 100000000 25065396724377 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12904143/80000000 : ℝ), (982025543/2000000000 : ℝ), (58328031/100000000 : ℝ)] ![(386455097249/4000000000000 : ℝ), (8041565821027/20000000000000 : ℝ), (25065396724377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12904143/80000000 : ℝ)|^4669 ≤ (386455097249/4000000000000 : ℝ)^3645
        have hw : |(-12904143/80000000 : ℝ)|=(12904143/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(982025543/2000000000 : ℝ)|^4669 ≤ (8041565821027/20000000000000 : ℝ)^3645
        have hw : |(982025543/2000000000 : ℝ)|=(982025543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(58328031/100000000 : ℝ)|^4669 ≤ (25065396724377/50000000000000 : ℝ)^3645
        have hw : |(58328031/100000000 : ℝ)|=(58328031/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_5 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299059837/2500000000 : ℝ)*x 0 + (-1203059999/10000000000 : ℝ)*x 1 + (2916401593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299059837/2500000000 : ℝ)^4669 ≤ (43233152782919/100000000000000 : ℝ)^3645 := by
    have hnat : (1299059837 : ℕ)^4669*100000000000000^3645 ≤ 43233152782919^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299059837 2500000000 43233152782919 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203059999/10000000000 : ℝ)^4669 ≤ (265442112391/4000000000000 : ℝ)^3645 := by
    have hnat : (1203059999 : ℕ)^4669*4000000000000^3645 ≤ 265442112391^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203059999 10000000000 265442112391 4000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2916401593/5000000000 : ℝ)^4669 ≤ (50130794395541/100000000000000 : ℝ)^3645 := by
    have hnat : (2916401593 : ℕ)^4669*100000000000000^3645 ≤ 50130794395541^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916401593 5000000000 50130794395541 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299059837/2500000000 : ℝ), (-1203059999/10000000000 : ℝ), (2916401593/5000000000 : ℝ)] ![(43233152782919/100000000000000 : ℝ), (265442112391/4000000000000 : ℝ), (50130794395541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299059837/2500000000 : ℝ)|^4669 ≤ (43233152782919/100000000000000 : ℝ)^3645
        have hw : |(1299059837/2500000000 : ℝ)|=(1299059837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1203059999/10000000000 : ℝ)|^4669 ≤ (265442112391/4000000000000 : ℝ)^3645
        have hw : |(-1203059999/10000000000 : ℝ)|=(1203059999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2916401593/5000000000 : ℝ)|^4669 ≤ (50130794395541/100000000000000 : ℝ)^3645
        have hw : |(2916401593/5000000000 : ℝ)|=(2916401593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_6 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196239311/10000000000 : ℝ)*x 0 + (2916401543/5000000000 : ℝ)*x 1 + (-120306021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196239311/10000000000 : ℝ)^4669 ≤ (43233152388593/100000000000000 : ℝ)^3645 := by
    have hnat : (5196239311 : ℕ)^4669*100000000000000^3645 ≤ 43233152388593^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196239311 10000000000 43233152388593 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2916401543/5000000000 : ℝ)^4669 ≤ (25065396647313/50000000000000 : ℝ)^3645 := by
    have hnat : (2916401543 : ℕ)^4669*50000000000000^3645 ≤ 25065396647313^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2916401543 5000000000 25065396647313 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120306021/1000000000 : ℝ)^4669 ≤ (829506787577/12500000000000 : ℝ)^3645 := by
    have hnat : (120306021 : ℕ)^4669*12500000000000^3645 ≤ 829506787577^3645*1000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120306021 1000000000 829506787577 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196239311/10000000000 : ℝ), (2916401543/5000000000 : ℝ), (-120306021/1000000000 : ℝ)] ![(43233152388593/100000000000000 : ℝ), (25065396647313/50000000000000 : ℝ), (829506787577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196239311/10000000000 : ℝ)|^4669 ≤ (43233152388593/100000000000000 : ℝ)^3645
        have hw : |(5196239311/10000000000 : ℝ)|=(5196239311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2916401543/5000000000 : ℝ)|^4669 ≤ (25065396647313/50000000000000 : ℝ)^3645
        have hw : |(2916401543/5000000000 : ℝ)|=(2916401543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120306021/1000000000 : ℝ)|^4669 ≤ (829506787577/12500000000000 : ℝ)^3645
        have hw : |(-120306021/1000000000 : ℝ)|=(120306021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s0_7 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516593893/1250000000 : ℝ)*x 0 + (214250253/400000000 : ℝ)*x 1 + (3154463581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516593893/1250000000 : ℝ)^4669 ≤ (32242468185991/100000000000000 : ℝ)^3645 := by
    have hnat : (516593893 : ℕ)^4669*100000000000000^3645 ≤ 32242468185991^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516593893 1250000000 32242468185991 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214250253/400000000 : ℝ)^4669 ≤ (44945851932221/100000000000000 : ℝ)^3645 := by
    have hnat : (214250253 : ℕ)^4669*100000000000000^3645 ≤ 44945851932221^3645*400000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214250253 400000000 44945851932221 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154463581/10000000000 : ℝ)^4669 ≤ (11405839932131/50000000000000 : ℝ)^3645 := by
    have hnat : (3154463581 : ℕ)^4669*50000000000000^3645 ≤ 11405839932131^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154463581 10000000000 11405839932131 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516593893/1250000000 : ℝ), (214250253/400000000 : ℝ), (3154463581/10000000000 : ℝ)] ![(32242468185991/100000000000000 : ℝ), (44945851932221/100000000000000 : ℝ), (11405839932131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516593893/1250000000 : ℝ)|^4669 ≤ (32242468185991/100000000000000 : ℝ)^3645
        have hw : |(516593893/1250000000 : ℝ)|=(516593893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214250253/400000000 : ℝ)|^4669 ≤ (44945851932221/100000000000000 : ℝ)^3645
        have hw : |(214250253/400000000 : ℝ)|=(214250253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154463581/10000000000 : ℝ)|^4669 ≤ (11405839932131/50000000000000 : ℝ)^3645
        have hw : |(3154463581/10000000000 : ℝ)|=(3154463581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1586_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (933/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (307/1250 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4667/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4667 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4667*1^1024 ≤ 0^1024*1^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4667/1024 : ℝ) ≤ (1535825156206389627/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4667 ≤ (1535825156206389627/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4667*100000000000000000000^1024 ≤ 1535825156206389627^1024*5^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1535825156206389627 100000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1535825156206389627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4667 := by
      have hnat : (1 : ℕ)^1024*1^4667 ≤ 1^4667*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101535825156206389627/100000000000000000000 : ℝ) ≤ (10033497813496129/10000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (101535825156206389627/100000000000000000000 : ℝ)^1024 ≤ (10033497813496129/10000000000000000 : ℝ)^4667 := by
      have hnat : (101535825156206389627 : ℕ)^1024*10000000000000000^4667 ≤ 10033497813496129^4667*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101535825156206389627 100000000000000000000 10033497813496129 10000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10033497813496129/10000000000000000 : ℝ)) (X := (101535825156206389627/100000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51535825156206389627/50000000000000000000 : ℝ) ≤ (5033497813496129/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (51535825156206389627/50000000000000000000 : ℝ)^1024 ≤ (5033497813496129/5000000000000000 : ℝ)^4667 := by
      have hnat : (51535825156206389627 : ℕ)^1024*5000000000000000^4667 ≤ 5033497813496129^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51535825156206389627 50000000000000000000 5033497813496129 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033497813496129/5000000000000000 : ℝ)) (X := (51535825156206389627/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(33497813496129/4000000000000000 : ℝ)*(0 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(33497813496129/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1535825156206389627/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(33497813496129/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4667/1024 : ℝ) := by
    rw [show (1 : ℝ)+(33497813496129/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10033497813496129/10000000000000000 : ℝ) by norm_num, show 1+(1535825156206389627/100000000000000000000 : ℝ)+(0 : ℝ)=(101535825156206389627/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1535825156206389627/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(33497813496129/4000000000000000 : ℝ)*(2/5 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(33497813496129/4000000000000000 : ℝ)*(2/5 : ℝ)=(5033497813496129/5000000000000000 : ℝ) by norm_num, show 1+2*(1535825156206389627/100000000000000000000 : ℝ)=(51535825156206389627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(33497813496129/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33497813496129/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(33497813496129/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33497813496129/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(33497813496129/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (33497813496129/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-201260279/1250000000 : ℝ)*X 0 0+(2929039831/5000000000 : ℝ)*X 0 1+(4885711823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1092415179/2000000000 : ℝ)*X 1 0+(-1075075897/5000000000 : ℝ)*X 1 1+(4885711719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((85344937/156250000 : ℝ)*X 2 0+(977142321/2000000000 : ℝ)*X 2 1+(-1075075921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((825149067/2000000000 : ℝ)*X 0 0+(77353653/250000000 : ℝ)*X 0 1+(1082904103/2000000000 : ℝ)*X 0 2+(825149067/2000000000 : ℝ)*X 1 0+(77353653/250000000 : ℝ)*X 1 1+(1082904103/2000000000 : ℝ)*X 1 2+(825149067/2000000000 : ℝ)*X 2 0+(77353653/250000000 : ℝ)*X 2 1+(1082904103/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12904143/80000000 : ℝ)*X 0 0+(982025543/2000000000 : ℝ)*X 0 1+(58328031/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299059837/2500000000 : ℝ)*X 1 0+(-1203059999/10000000000 : ℝ)*X 1 1+(2916401593/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196239311/10000000000 : ℝ)*X 2 0+(2916401543/5000000000 : ℝ)*X 2 1+(-120306021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((516593893/1250000000 : ℝ)*X 0 0+(214250253/400000000 : ℝ)*X 0 1+(3154463581/10000000000 : ℝ)*X 0 2+(516593893/1250000000 : ℝ)*X 1 0+(214250253/400000000 : ℝ)*X 1 1+(3154463581/10000000000 : ℝ)*X 1 2+(516593893/1250000000 : ℝ)*X 2 0+(214250253/400000000 : ℝ)*X 2 1+(3154463581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129056719679666377163349/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (23085567/50000000000000 : ℝ)*(base1) + (953028553/100000000000000 : ℝ)*(base19) + (966773307/100000000000000 : ℝ)*(base23) + (62547463/50000000000000 : ℝ)*(upper3) + (113968823/100000000000000 : ℝ)*(upper5) + (91212017612091/12500000000000 : ℝ)*(major0) + (91212017612091/12500000000000 : ℝ)*(major1) + (91212017612091/12500000000000 : ℝ)*(major2) + (32138148688273/3125000000000 : ℝ)*(sp0) + (514211616614953/50000000000000 : ℝ)*(sp1) + (1028423219485151/100000000000000 : ℝ)*(sp2) + (430966347274651/100000000000000 : ℝ)*(sp3) + (3474404857/100000000000000 : ℝ)*(sp4) + (76500679/5000000000000 : ℝ)*(sp7) + (215483961729683/50000000000000 : ℝ)*(f.failure) + (1028424186258459/100000000000000 : ℝ)*(f.sum) + (52202127645739/25000000000000000000000000000 : ℝ)*base65 + (162056421745739/50000000000000000000000000000 : ℝ)*base67 + (146592431554261/50000000000000000000000000000 : ℝ)*base70 + (109780128345739/50000000000000000000000000000 : ℝ)*base71 + (48529195695739/25000000000000000000000000000 : ℝ)*base73 + (23449669145739/50000000000000000000000000000 : ℝ)*base75 + (107068363445739/50000000000000000000000000000 : ℝ)*base77 + (480804103345739/50000000000000000000000000000 : ℝ)*base79 + (67309575479261/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (28779/100000000000000000000 : ℝ)*base89 + (28779/100000000000000000000 : ℝ)*base91 + (28779/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53070505333107689126043/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (584791119/100000000000000 : ℝ)*(base19) + (72204581/12500000000000 : ℝ)*(base23) + (40140133/50000000000000 : ℝ)*(base32) + (48008379/50000000000000 : ℝ)*(upper3) + (7490853/25000000000000 : ℝ)*(upper5) + (384494894809111/50000000000000 : ℝ)*(major0) + (384494894809111/50000000000000 : ℝ)*(major1) + (384494894809111/50000000000000 : ℝ)*(major2) + (1657684947/100000000000000 : ℝ)*(sp1) + (834342481/50000000000000 : ℝ)*(sp2) + (1083804233142119/100000000000000 : ℝ)*(sp4) + (1083801990666053/100000000000000 : ℝ)*(sp5) + (108380198682051/10000000000000 : ℝ)*(sp6) + (454175177363207/100000000000000 : ℝ)*(sp7) + (454175257643473/100000000000000 : ℝ)*(f.failure) + (1083804233142119/100000000000000 : ℝ)*(f.sum) + (211602824131319/100000000000000000000000000000 : ℝ)*base65 + (868288520431319/200000000000000000000000000000 : ℝ)*base67 + (1631714359031319/200000000000000000000000000000 : ℝ)*base69 + (1244188029031319/200000000000000000000000000000 : ℝ)*base71 + (148073451431319/100000000000000000000000000000 : ℝ)*base73 + (886820388831319/200000000000000000000000000000 : ℝ)*base75 + (598836865631319/200000000000000000000000000000 : ℝ)*base77 + (322261436568681/200000000000000000000000000000 : ℝ)*base80 + (605045276131319/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2014951/200000000000000000000 : ℝ)*base90 + (2014951/200000000000000000000 : ℝ)*base92 + (2014951/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1586_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (933/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (307/1250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1586_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1586_s1_0 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-872343711/5000000000 : ℝ)*x 0 + (5525939907/10000000000 : ℝ)*x 1 + (5131016269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872343711/5000000000 : ℝ)^4669 ≤ (2136590278727/20000000000000 : ℝ)^3645 := by
    have hnat : (872343711 : ℕ)^4669*20000000000000^3645 ≤ 2136590278727^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872343711 5000000000 2136590278727 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525939907/10000000000 : ℝ)^4669 ≤ (187111117997/400000000000 : ℝ)^3645 := by
    have hnat : (5525939907 : ℕ)^4669*400000000000^3645 ≤ 187111117997^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525939907 10000000000 187111117997 400000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131016269/10000000000 : ℝ)^4669 ≤ (42539269085041/100000000000000 : ℝ)^3645 := by
    have hnat : (5131016269 : ℕ)^4669*100000000000000^3645 ≤ 42539269085041^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131016269 10000000000 42539269085041 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-872343711/5000000000 : ℝ), (5525939907/10000000000 : ℝ), (5131016269/10000000000 : ℝ)] ![(2136590278727/20000000000000 : ℝ), (187111117997/400000000000 : ℝ), (42539269085041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-872343711/5000000000 : ℝ)|^4669 ≤ (2136590278727/20000000000000 : ℝ)^3645
        have hw : |(-872343711/5000000000 : ℝ)|=(872343711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525939907/10000000000 : ℝ)|^4669 ≤ (187111117997/400000000000 : ℝ)^3645
        have hw : |(5525939907/10000000000 : ℝ)|=(5525939907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131016269/10000000000 : ℝ)|^4669 ≤ (42539269085041/100000000000000 : ℝ)^3645
        have hw : |(5131016269/10000000000 : ℝ)|=(5131016269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_1 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373762287/10000000000 : ℝ)*x 0 + (-975459897/5000000000 : ℝ)*x 1 + (5131015877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373762287/10000000000 : ℝ)^4669 ≤ (22567052002239/50000000000000 : ℝ)^3645 := by
    have hnat : (5373762287 : ℕ)^4669*50000000000000^3645 ≤ 22567052002239^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373762287 10000000000 22567052002239 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975459897/5000000000 : ℝ)^4669 ≤ (1232663105853/10000000000000 : ℝ)^3645 := by
    have hnat : (975459897 : ℕ)^4669*10000000000000^3645 ≤ 1232663105853^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975459897 5000000000 1232663105853 10000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5131015877/10000000000 : ℝ)^4669 ≤ (83084501801/195312500000 : ℝ)^3645 := by
    have hnat : (5131015877 : ℕ)^4669*195312500000^3645 ≤ 83084501801^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131015877 10000000000 83084501801 195312500000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373762287/10000000000 : ℝ), (-975459897/5000000000 : ℝ), (5131015877/10000000000 : ℝ)] ![(22567052002239/50000000000000 : ℝ), (1232663105853/10000000000000 : ℝ), (83084501801/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373762287/10000000000 : ℝ)|^4669 ≤ (22567052002239/50000000000000 : ℝ)^3645
        have hw : |(5373762287/10000000000 : ℝ)|=(5373762287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-975459897/5000000000 : ℝ)|^4669 ≤ (1232663105853/10000000000000 : ℝ)^3645
        have hw : |(-975459897/5000000000 : ℝ)|=(975459897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5131015877/10000000000 : ℝ)|^4669 ≤ (83084501801/195312500000 : ℝ)^3645
        have hw : |(5131015877/10000000000 : ℝ)|=(5131015877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_2 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343440459/2500000000 : ℝ)*x 0 + (2565508143/5000000000 : ℝ)*x 1 + (-1950919857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343440459/2500000000 : ℝ)^4669 ≤ (45134099152383/100000000000000 : ℝ)^3645 := by
    have hnat : (1343440459 : ℕ)^4669*100000000000000^3645 ≤ 45134099152383^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343440459 2500000000 45134099152383 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2565508143/5000000000 : ℝ)^4669 ≤ (5317408658197/12500000000000 : ℝ)^3645 := by
    have hnat : (2565508143 : ℕ)^4669*12500000000000^3645 ≤ 5317408658197^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565508143 5000000000 5317408658197 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950919857/10000000000 : ℝ)^4669 ≤ (6163315784207/50000000000000 : ℝ)^3645 := by
    have hnat : (1950919857 : ℕ)^4669*50000000000000^3645 ≤ 6163315784207^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950919857 10000000000 6163315784207 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343440459/2500000000 : ℝ), (2565508143/5000000000 : ℝ), (-1950919857/10000000000 : ℝ)] ![(45134099152383/100000000000000 : ℝ), (5317408658197/12500000000000 : ℝ), (6163315784207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343440459/2500000000 : ℝ)|^4669 ≤ (45134099152383/100000000000000 : ℝ)^3645
        have hw : |(1343440459/2500000000 : ℝ)|=(1343440459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2565508143/5000000000 : ℝ)|^4669 ≤ (5317408658197/12500000000000 : ℝ)^3645
        have hw : |(2565508143/5000000000 : ℝ)|=(2565508143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950919857/10000000000 : ℝ)|^4669 ≤ (6163315784207/50000000000000 : ℝ)^3645
        have hw : |(-1950919857/10000000000 : ℝ)|=(1950919857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_3 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055661107/2500000000 : ℝ)*x 0 + (3772370263/10000000000 : ℝ)*x 1 + (4714782279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055661107/2500000000 : ℝ)^4669 ≤ (33143542638559/100000000000000 : ℝ)^3645 := by
    have hnat : (1055661107 : ℕ)^4669*100000000000000^3645 ≤ 33143542638559^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055661107 2500000000 33143542638559 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3772370263/10000000000 : ℝ)^4669 ≤ (28686092376313/100000000000000 : ℝ)^3645 := by
    have hnat : (3772370263 : ℕ)^4669*100000000000000^3645 ≤ 28686092376313^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3772370263 10000000000 28686092376313 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4714782279/10000000000 : ℝ)^4669 ≤ (19085182482479/50000000000000 : ℝ)^3645 := by
    have hnat : (4714782279 : ℕ)^4669*50000000000000^3645 ≤ 19085182482479^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714782279 10000000000 19085182482479 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055661107/2500000000 : ℝ), (3772370263/10000000000 : ℝ), (4714782279/10000000000 : ℝ)] ![(33143542638559/100000000000000 : ℝ), (28686092376313/100000000000000 : ℝ), (19085182482479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055661107/2500000000 : ℝ)|^4669 ≤ (33143542638559/100000000000000 : ℝ)^3645
        have hw : |(1055661107/2500000000 : ℝ)|=(1055661107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3772370263/10000000000 : ℝ)|^4669 ≤ (28686092376313/100000000000000 : ℝ)^3645
        have hw : |(3772370263/10000000000 : ℝ)|=(3772370263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4714782279/10000000000 : ℝ)|^4669 ≤ (19085182482479/50000000000000 : ℝ)^3645
        have hw : |(4714782279/10000000000 : ℝ)|=(4714782279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_4 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69795173/400000000 : ℝ)*x 0 + (1283750743/2500000000 : ℝ)*x 1 + (2760947869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69795173/400000000 : ℝ)^4669 ≤ (10684456573629/100000000000000 : ℝ)^3645 := by
    have hnat : (69795173 : ℕ)^4669*100000000000000^3645 ≤ 10684456573629^3645*400000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69795173 400000000 10684456573629 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283750743/2500000000 : ℝ)^4669 ≤ (8516322273081/20000000000000 : ℝ)^3645 := by
    have hnat : (1283750743 : ℕ)^4669*20000000000000^3645 ≤ 8516322273081^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283750743 2500000000 8516322273081 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2760947869/5000000000 : ℝ)^4669 ≤ (1460435376273/3125000000000 : ℝ)^3645 := by
    have hnat : (2760947869 : ℕ)^4669*3125000000000^3645 ≤ 1460435376273^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760947869 5000000000 1460435376273 3125000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69795173/400000000 : ℝ), (1283750743/2500000000 : ℝ), (2760947869/5000000000 : ℝ)] ![(10684456573629/100000000000000 : ℝ), (8516322273081/20000000000000 : ℝ), (1460435376273/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69795173/400000000 : ℝ)|^4669 ≤ (10684456573629/100000000000000 : ℝ)^3645
        have hw : |(-69795173/400000000 : ℝ)|=(69795173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283750743/2500000000 : ℝ)|^4669 ≤ (8516322273081/20000000000000 : ℝ)^3645
        have hw : |(1283750743/2500000000 : ℝ)|=(1283750743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2760947869/5000000000 : ℝ)|^4669 ≤ (1460435376273/3125000000000 : ℝ)^3645
        have hw : |(2760947869/5000000000 : ℝ)|=(2760947869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_5 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263445969/500000000 : ℝ)*x 0 + (-780019989/5000000000 : ℝ)*x 1 + (138047413/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263445969/500000000 : ℝ)^4669 ≤ (44009254776591/100000000000000 : ℝ)^3645 := by
    have hnat : (263445969 : ℕ)^4669*100000000000000^3645 ≤ 44009254776591^3645*500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263445969 500000000 44009254776591 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (780019989/5000000000 : ℝ)^4669 ≤ (9256804699113/100000000000000 : ℝ)^3645 := by
    have hnat : (780019989 : ℕ)^4669*100000000000000^3645 ≤ 9256804699113^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780019989 5000000000 9256804699113 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138047413/250000000 : ℝ)^4669 ≤ (2336697025921/5000000000000 : ℝ)^3645 := by
    have hnat : (138047413 : ℕ)^4669*5000000000000^3645 ≤ 2336697025921^3645*250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138047413 250000000 2336697025921 5000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263445969/500000000 : ℝ), (-780019989/5000000000 : ℝ), (138047413/250000000 : ℝ)] ![(44009254776591/100000000000000 : ℝ), (9256804699113/100000000000000 : ℝ), (2336697025921/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263445969/500000000 : ℝ)|^4669 ≤ (44009254776591/100000000000000 : ℝ)^3645
        have hw : |(263445969/500000000 : ℝ)|=(263445969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-780019989/5000000000 : ℝ)|^4669 ≤ (9256804699113/100000000000000 : ℝ)^3645
        have hw : |(-780019989/5000000000 : ℝ)|=(780019989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138047413/250000000 : ℝ)|^4669 ≤ (2336697025921/5000000000000 : ℝ)^3645
        have hw : |(138047413/250000000 : ℝ)|=(138047413/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_6 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2634459201/5000000000 : ℝ)*x 0 + (5521896911/10000000000 : ℝ)*x 1 + (-390010199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634459201/5000000000 : ℝ)^4669 ≤ (22004622156417/50000000000000 : ℝ)^3645 := by
    have hnat : (2634459201 : ℕ)^4669*50000000000000^3645 ≤ 22004622156417^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634459201 5000000000 22004622156417 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521896911/10000000000 : ℝ)^4669 ≤ (23366972378631/50000000000000 : ℝ)^3645 := by
    have hnat : (5521896911 : ℕ)^4669*50000000000000^3645 ≤ 23366972378631^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521896911 10000000000 23366972378631 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390010199/2500000000 : ℝ)^4669 ≤ (462840545823/5000000000000 : ℝ)^3645 := by
    have hnat : (390010199 : ℕ)^4669*5000000000000^3645 ≤ 462840545823^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390010199 2500000000 462840545823 5000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2634459201/5000000000 : ℝ), (5521896911/10000000000 : ℝ), (-390010199/2500000000 : ℝ)] ![(22004622156417/50000000000000 : ℝ), (23366972378631/50000000000000 : ℝ), (462840545823/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2634459201/5000000000 : ℝ)|^4669 ≤ (22004622156417/50000000000000 : ℝ)^3645
        have hw : |(2634459201/5000000000 : ℝ)|=(2634459201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521896911/10000000000 : ℝ)|^4669 ≤ (23366972378631/50000000000000 : ℝ)^3645
        have hw : |(5521896911/10000000000 : ℝ)|=(5521896911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390010199/2500000000 : ℝ)|^4669 ≤ (462840545823/5000000000000 : ℝ)^3645
        have hw : |(-390010199/2500000000 : ℝ)|=(390010199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s1_7 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055775373/2500000000 : ℝ)*x 0 + (2352634959/5000000000 : ℝ)*x 1 + (1891009749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055775373/2500000000 : ℝ)^4669 ≤ (828703451243/2500000000000 : ℝ)^3645 := by
    have hnat : (1055775373 : ℕ)^4669*2500000000000^3645 ≤ 828703451243^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055775373 2500000000 828703451243 2500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2352634959/5000000000 : ℝ)^4669 ≤ (38071746967607/100000000000000 : ℝ)^3645 := by
    have hnat : (2352634959 : ℕ)^4669*100000000000000^3645 ≤ 38071746967607^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352634959 5000000000 38071746967607 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1891009749/5000000000 : ℝ)^4669 ≤ (7195028742147/25000000000000 : ℝ)^3645 := by
    have hnat : (1891009749 : ℕ)^4669*25000000000000^3645 ≤ 7195028742147^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891009749 5000000000 7195028742147 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055775373/2500000000 : ℝ), (2352634959/5000000000 : ℝ), (1891009749/5000000000 : ℝ)] ![(828703451243/2500000000000 : ℝ), (38071746967607/100000000000000 : ℝ), (7195028742147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055775373/2500000000 : ℝ)|^4669 ≤ (828703451243/2500000000000 : ℝ)^3645
        have hw : |(1055775373/2500000000 : ℝ)|=(1055775373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2352634959/5000000000 : ℝ)|^4669 ≤ (38071746967607/100000000000000 : ℝ)^3645
        have hw : |(2352634959/5000000000 : ℝ)|=(2352634959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1891009749/5000000000 : ℝ)|^4669 ≤ (7195028742147/25000000000000 : ℝ)^3645
        have hw : |(1891009749/5000000000 : ℝ)|=(1891009749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1586_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (307/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (933/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1849/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4403/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (307/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (933/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (307/1250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (933/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (307/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (933/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (307/1250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (933/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (307/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (933/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (307/1250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (933/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (933/25000 : ℝ) ^ (4667/1024 : ℝ) ≤ (31006778815359/100000000000000000000 : ℝ) := by
    have hpowers : (933/25000 : ℝ)^4667 ≤ (31006778815359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (933 : ℕ)^4667*100000000000000000000^1024 ≤ 31006778815359^1024*25000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        933 25000 31006778815359 100000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (933/25000 : ℝ)) (X := (31006778815359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (307/1250 : ℝ) ^ (4667/1024 : ℝ) ≤ (166300786948119951/100000000000000000000 : ℝ) := by
    have hpowers : (307/1250 : ℝ)^4667 ≤ (166300786948119951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (307 : ℕ)^4667*100000000000000000000^1024 ≤ 166300786948119951^1024*1250^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        307 1250 166300786948119951 100000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (307/1250 : ℝ)) (X := (166300786948119951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000031006778815359/50000000000000000000 : ℝ) ≤ (10000001360657117/10000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (50000031006778815359/50000000000000000000 : ℝ)^1024 ≤ (10000001360657117/10000000000000000 : ℝ)^4667 := by
      have hnat : (50000031006778815359 : ℕ)^1024*10000000000000000^4667 ≤ 10000001360657117^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000031006778815359 50000000000000000000 10000001360657117 10000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001360657117/10000000000000000 : ℝ)) (X := (50000031006778815359/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10016633179372693531/10000000000000000000 : ℝ) ≤ (5001823583615249/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (10016633179372693531/10000000000000000000 : ℝ)^1024 ≤ (5001823583615249/5000000000000000 : ℝ)^4667 := by
      have hnat : (10016633179372693531 : ℕ)^1024*5000000000000000^4667 ≤ 5001823583615249^4667*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10016633179372693531 10000000000000000000 5001823583615249 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001823583615249/5000000000000000 : ℝ)) (X := (10016633179372693531/10000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50166300786948119951/50000000000000000000 : ℝ) ≤ (10007292973803879/10000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (50166300786948119951/50000000000000000000 : ℝ)^1024 ≤ (10007292973803879/10000000000000000 : ℝ)^4667 := by
      have hnat : (50166300786948119951 : ℕ)^1024*10000000000000000^4667 ≤ 10007292973803879^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50166300786948119951 50000000000000000000 10007292973803879 10000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007292973803879/10000000000000000 : ℝ)) (X := (50166300786948119951/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(31006778815359/100000000000000000000 : ℝ) ≤ ((52063204009875679273/52070000000000000000 : ℝ)+2*(3645806573381/2082800000000000 : ℝ)*(933/25000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (52063204009875679273/52070000000000000000 : ℝ)+2*(3645806573381/2082800000000000 : ℝ)*(933/25000 : ℝ)=(10000001360657117/10000000000000000 : ℝ) by norm_num, show 1+2*(31006778815359/100000000000000000000 : ℝ)=(50000031006778815359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(166300786948119951/100000000000000000000 : ℝ)+(31006778815359/100000000000000000000 : ℝ) ≤ ((52063204009875679273/52070000000000000000 : ℝ)+(3645806573381/2082800000000000 : ℝ)*((307/1250 : ℝ)+(933/25000 : ℝ)))^(4667/1024 : ℝ) := by
    rw [show (52063204009875679273/52070000000000000000 : ℝ)+(3645806573381/2082800000000000 : ℝ)*((307/1250 : ℝ)+(933/25000 : ℝ))=(5001823583615249/5000000000000000 : ℝ) by norm_num, show 1+(166300786948119951/100000000000000000000 : ℝ)+(31006778815359/100000000000000000000 : ℝ)=(10016633179372693531/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(166300786948119951/100000000000000000000 : ℝ) ≤ ((52063204009875679273/52070000000000000000 : ℝ)+2*(3645806573381/2082800000000000 : ℝ)*(307/1250 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (52063204009875679273/52070000000000000000 : ℝ)+2*(3645806573381/2082800000000000 : ℝ)*(307/1250 : ℝ)=(10007292973803879/10000000000000000 : ℝ) by norm_num, show 1+2*(166300786948119951/100000000000000000000 : ℝ)=(50166300786948119951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52063204009875679273/52070000000000000000 : ℝ)*(X 1 0+X 2 0)+(3645806573381/2082800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (933/25000 : ℝ)) (hi := (307/1250 : ℝ)) (c := (52063204009875679273/52070000000000000000 : ℝ)) (alpha := (3645806573381/2082800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52063204009875679273/52070000000000000000 : ℝ)*(X 0 1+X 2 1)+(3645806573381/2082800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (933/25000 : ℝ)) (hi := (307/1250 : ℝ)) (c := (52063204009875679273/52070000000000000000 : ℝ)) (alpha := (3645806573381/2082800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52063204009875679273/52070000000000000000 : ℝ)*(X 0 2+X 1 2)+(3645806573381/2082800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (933/25000 : ℝ)) (hi := (307/1250 : ℝ)) (c := (52063204009875679273/52070000000000000000 : ℝ)) (alpha := (3645806573381/2082800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-872343711/5000000000 : ℝ)*X 0 0+(5525939907/10000000000 : ℝ)*X 0 1+(5131016269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5373762287/10000000000 : ℝ)*X 1 0+(-975459897/5000000000 : ℝ)*X 1 1+(5131015877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343440459/2500000000 : ℝ)*X 2 0+(2565508143/5000000000 : ℝ)*X 2 1+(-1950919857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1055661107/2500000000 : ℝ)*X 0 0+(3772370263/10000000000 : ℝ)*X 0 1+(4714782279/10000000000 : ℝ)*X 0 2+(1055661107/2500000000 : ℝ)*X 1 0+(3772370263/10000000000 : ℝ)*X 1 1+(4714782279/10000000000 : ℝ)*X 1 2+(1055661107/2500000000 : ℝ)*X 2 0+(3772370263/10000000000 : ℝ)*X 2 1+(4714782279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-69795173/400000000 : ℝ)*X 0 0+(1283750743/2500000000 : ℝ)*X 0 1+(2760947869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263445969/500000000 : ℝ)*X 1 0+(-780019989/5000000000 : ℝ)*X 1 1+(138047413/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2634459201/5000000000 : ℝ)*X 2 0+(5521896911/10000000000 : ℝ)*X 2 1+(-390010199/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1055775373/2500000000 : ℝ)*X 0 0+(2352634959/5000000000 : ℝ)*X 0 1+(1891009749/5000000000 : ℝ)*X 0 2+(1055775373/2500000000 : ℝ)*X 1 0+(2352634959/5000000000 : ℝ)*X 1 1+(1891009749/5000000000 : ℝ)*X 1 2+(1055775373/2500000000 : ℝ)*X 2 0+(2352634959/5000000000 : ℝ)*X 2 1+(1891009749/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1613982626300129896081636959/1301750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1091144779/100000000000000 : ℝ)*(base19) + (871540967/100000000000000 : ℝ)*(base23) + (50976589/100000000000000 : ℝ)*(upper2) + (10143739/12500000000000 : ℝ)*(upper3) + (54786313/100000000000000 : ℝ)*(upper4) + (1796635425492439/100000000000000 : ℝ)*(major0) + (1796635425492439/100000000000000 : ℝ)*(major1) + (1796635425492439/100000000000000 : ℝ)*(major2) + (1266072924684557/50000000000000 : ℝ)*(sp0) + (633038433638381/25000000000000 : ℝ)*(sp1) + (506430790831467/20000000000000 : ℝ)*(sp2) + (1061111332958179/100000000000000 : ℝ)*(sp3) + (2244082297/25000000000000 : ℝ)*(sp4) + (4650999853/100000000000000 : ℝ)*(sp7) + (1061115983958033/100000000000000 : ℝ)*(f.failure) + (1266077412849151/50000000000000 : ℝ)*(f.sum) + (363685306935059/104140000000000000000000000000 : ℝ)*base65 + (36344169165951991847/5207000000000000000000000000000000 : ℝ)*base67 + (55573474994791991847/5207000000000000000000000000000000 : ℝ)*base69 + (40322971107874991847/5207000000000000000000000000000000 : ℝ)*base71 + (357399000495759/104140000000000000000000000000 : ℝ)*base73 + (5494138411774008153/5207000000000000000000000000000000 : ℝ)*base76 + (17889560989770991847/5207000000000000000000000000000000 : ℝ)*base77 + (49699193800019991847/5207000000000000000000000000000000 : ℝ)*base79 + (754876015636659/104140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (602329/200000000000000000000 : ℝ)*base89 + (602329/200000000000000000000 : ℝ)*base91 + (602329/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92321143143792184804692261/31750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (479847817/100000000000000 : ℝ)*(base19) + (43781947/12500000000000 : ℝ)*(base23) + (96700481/50000000000000 : ℝ)*(upper2) + (45003457/20000000000000 : ℝ)*(upper3) + (916954524851693/50000000000000 : ℝ)*(major0) + (916954524851693/50000000000000 : ℝ)*(major1) + (916954524851693/50000000000000 : ℝ)*(major2) + (2455815057/50000000000000 : ℝ)*(sp1) + (4062754643/100000000000000 : ℝ)*(sp2) + (111045887/100000000000000 : ℝ)*(sp3) + (2584687736789533/100000000000000 : ℝ)*(sp4) + (1292341172655801/50000000000000 : ℝ)*(sp5) + (1292341661889657/50000000000000 : ℝ)*(sp6) + (1083130154646261/100000000000000 : ℝ)*(sp7) + (270782566423037/25000000000000 : ℝ)*(f.failure) + (2584687736789533/100000000000000 : ℝ)*(f.sum) + (194881038079577/52070000000000000000000000000 : ℝ)*base66 + (15558949284782615811/2603500000000000000000000000000000 : ℝ)*base68 + (15118220603757615811/2603500000000000000000000000000000 : ℝ)*base70 + (28457520287881115811/2603500000000000000000000000000000 : ℝ)*base72 + (91748581332457/52070000000000000000000000000 : ℝ)*base74 + (20869442351481615811/2603500000000000000000000000000000 : ℝ)*base76 + (15657108704224115811/2603500000000000000000000000000000 : ℝ)*base78 + (16558492492448615811/2603500000000000000000000000000000 : ℝ)*base80 + (46148791669887/52070000000000000000000000000 : ℝ)*base82 + (692581/50000000000000000000 : ℝ)*base89 + (692581/50000000000000000000 : ℝ)*base91 + (692581/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1586_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (307/1250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (933/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1849/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4403/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1586_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1586_s2_0 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1761893107/10000000000 : ℝ)*x 0 + (33984607/62500000 : ℝ)*x 1 + (5208188791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1761893107/10000000000 : ℝ)^4669 ≤ (1352260949313/12500000000000 : ℝ)^3645 := by
    have hnat : (1761893107 : ℕ)^4669*12500000000000^3645 ≤ 1352260949313^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1761893107 10000000000 1352260949313 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33984607/62500000 : ℝ)^4669 ≤ (11455341915447/25000000000000 : ℝ)^3645 := by
    have hnat : (33984607 : ℕ)^4669*25000000000000^3645 ≤ 11455341915447^3645*62500000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33984607 62500000 11455341915447 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5208188791/10000000000 : ℝ)^4669 ≤ (43360544722549/100000000000000 : ℝ)^3645 := by
    have hnat : (5208188791 : ℕ)^4669*100000000000000^3645 ≤ 43360544722549^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208188791 10000000000 43360544722549 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1761893107/10000000000 : ℝ), (33984607/62500000 : ℝ), (5208188791/10000000000 : ℝ)] ![(1352260949313/12500000000000 : ℝ), (11455341915447/25000000000000 : ℝ), (43360544722549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1761893107/10000000000 : ℝ)|^4669 ≤ (1352260949313/12500000000000 : ℝ)^3645
        have hw : |(-1761893107/10000000000 : ℝ)|=(1761893107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33984607/62500000 : ℝ)|^4669 ≤ (11455341915447/25000000000000 : ℝ)^3645
        have hw : |(33984607/62500000 : ℝ)|=(33984607/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5208188791/10000000000 : ℝ)|^4669 ≤ (43360544722549/100000000000000 : ℝ)^3645
        have hw : |(5208188791/10000000000 : ℝ)|=(5208188791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_1 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350838873/10000000000 : ℝ)*x 0 + (-469882001/2500000000 : ℝ)*x 1 + (104163777/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350838873/10000000000 : ℝ)^4669 ≤ (2805476863743/6250000000000 : ℝ)^3645 := by
    have hnat : (5350838873 : ℕ)^4669*6250000000000^3645 ≤ 2805476863743^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350838873 10000000000 2805476863743 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469882001/2500000000 : ℝ)^4669 ≤ (734489051269/6250000000000 : ℝ)^3645 := by
    have hnat : (469882001 : ℕ)^4669*6250000000000^3645 ≤ 734489051269^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469882001 2500000000 734489051269 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104163777/200000000 : ℝ)^4669 ≤ (8672109070349/20000000000000 : ℝ)^3645 := by
    have hnat : (104163777 : ℕ)^4669*20000000000000^3645 ≤ 8672109070349^3645*200000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104163777 200000000 8672109070349 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350838873/10000000000 : ℝ), (-469882001/2500000000 : ℝ), (104163777/200000000 : ℝ)] ![(2805476863743/6250000000000 : ℝ), (734489051269/6250000000000 : ℝ), (8672109070349/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350838873/10000000000 : ℝ)|^4669 ≤ (2805476863743/6250000000000 : ℝ)^3645
        have hw : |(5350838873/10000000000 : ℝ)|=(5350838873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469882001/2500000000 : ℝ)|^4669 ≤ (734489051269/6250000000000 : ℝ)^3645
        have hw : |(-469882001/2500000000 : ℝ)|=(469882001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104163777/200000000 : ℝ)|^4669 ≤ (8672109070349/20000000000000 : ℝ)^3645
        have hw : |(104163777/200000000 : ℝ)|=(104163777/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_2 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668854847/1250000000 : ℝ)*x 0 + (2604094651/5000000000 : ℝ)*x 1 + (-469881883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668854847/1250000000 : ℝ)^4669 ≤ (11221907194391/25000000000000 : ℝ)^3645 := by
    have hnat : (668854847 : ℕ)^4669*25000000000000^3645 ≤ 11221907194391^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668854847 1250000000 11221907194391 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604094651/5000000000 : ℝ)^4669 ≤ (43360550172031/100000000000000 : ℝ)^3645 := by
    have hnat : (2604094651 : ℕ)^4669*100000000000000^3645 ≤ 43360550172031^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604094651 5000000000 43360550172031 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469881883/2500000000 : ℝ)^4669 ≤ (734488815001/6250000000000 : ℝ)^3645 := by
    have hnat : (469881883 : ℕ)^4669*6250000000000^3645 ≤ 734488815001^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469881883 2500000000 734488815001 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668854847/1250000000 : ℝ), (2604094651/5000000000 : ℝ), (-469881883/2500000000 : ℝ)] ![(11221907194391/25000000000000 : ℝ), (43360550172031/100000000000000 : ℝ), (734488815001/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668854847/1250000000 : ℝ)|^4669 ≤ (11221907194391/25000000000000 : ℝ)^3645
        have hw : |(668854847/1250000000 : ℝ)|=(668854847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2604094651/5000000000 : ℝ)|^4669 ≤ (43360550172031/100000000000000 : ℝ)^3645
        have hw : |(2604094651/5000000000 : ℝ)|=(2604094651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-469881883/2500000000 : ℝ)|^4669 ≤ (734488815001/6250000000000 : ℝ)^3645
        have hw : |(-469881883/2500000000 : ℝ)|=(469881883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_3 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235145313/10000000000 : ℝ)*x 0 + (3968561949/10000000000 : ℝ)*x 1 + (4515858937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235145313/10000000000 : ℝ)^4669 ≤ (33269279306823/100000000000000 : ℝ)^3645 := by
    have hnat : (4235145313 : ℕ)^4669*100000000000000^3645 ≤ 33269279306823^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235145313 10000000000 33269279306823 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3968561949/10000000000 : ℝ)^4669 ≤ (30610897357049/100000000000000 : ℝ)^3645 := by
    have hnat : (3968561949 : ℕ)^4669*100000000000000^3645 ≤ 30610897357049^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3968561949 10000000000 30610897357049 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515858937/10000000000 : ℝ)^4669 ≤ (4514977914663/12500000000000 : ℝ)^3645 := by
    have hnat : (4515858937 : ℕ)^4669*12500000000000^3645 ≤ 4514977914663^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515858937 10000000000 4514977914663 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235145313/10000000000 : ℝ), (3968561949/10000000000 : ℝ), (4515858937/10000000000 : ℝ)] ![(33269279306823/100000000000000 : ℝ), (30610897357049/100000000000000 : ℝ), (4514977914663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235145313/10000000000 : ℝ)|^4669 ≤ (33269279306823/100000000000000 : ℝ)^3645
        have hw : |(4235145313/10000000000 : ℝ)|=(4235145313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3968561949/10000000000 : ℝ)|^4669 ≤ (30610897357049/100000000000000 : ℝ)^3645
        have hw : |(3968561949/10000000000 : ℝ)|=(3968561949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515858937/10000000000 : ℝ)|^4669 ≤ (4514977914663/12500000000000 : ℝ)^3645
        have hw : |(4515858937/10000000000 : ℝ)|=(4515858937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_4 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-880965067/5000000000 : ℝ)*x 0 + (2604770677/5000000000 : ℝ)*x 1 + (5436173759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (880965067/5000000000 : ℝ)^4669 ≤ (10818378811747/100000000000000 : ℝ)^3645 := by
    have hnat : (880965067 : ℕ)^4669*100000000000000^3645 ≤ 10818378811747^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880965067 5000000000 10818378811747 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2604770677/5000000000 : ℝ)^4669 ≤ (43374969452669/100000000000000 : ℝ)^3645 := by
    have hnat : (2604770677 : ℕ)^4669*100000000000000^3645 ≤ 43374969452669^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2604770677 5000000000 43374969452669 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436173759/10000000000 : ℝ)^4669 ≤ (1832266069257/4000000000000 : ℝ)^3645 := by
    have hnat : (5436173759 : ℕ)^4669*4000000000000^3645 ≤ 1832266069257^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436173759 10000000000 1832266069257 4000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-880965067/5000000000 : ℝ), (2604770677/5000000000 : ℝ), (5436173759/10000000000 : ℝ)] ![(10818378811747/100000000000000 : ℝ), (43374969452669/100000000000000 : ℝ), (1832266069257/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-880965067/5000000000 : ℝ)|^4669 ≤ (10818378811747/100000000000000 : ℝ)^3645
        have hw : |(-880965067/5000000000 : ℝ)|=(880965067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2604770677/5000000000 : ℝ)|^4669 ≤ (43374969452669/100000000000000 : ℝ)^3645
        have hw : |(2604770677/5000000000 : ℝ)|=(2604770677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436173759/10000000000 : ℝ)|^4669 ≤ (1832266069257/4000000000000 : ℝ)^3645
        have hw : |(5436173759/10000000000 : ℝ)|=(5436173759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_5 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322510973/2500000000 : ℝ)*x 0 + (-825771401/5000000000 : ℝ)*x 1 + (5436175017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322510973/2500000000 : ℝ)^4669 ≤ (44235396014199/100000000000000 : ℝ)^3645 := by
    have hnat : (1322510973 : ℕ)^4669*100000000000000^3645 ≤ 44235396014199^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322510973 2500000000 44235396014199 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825771401/5000000000 : ℝ)^4669 ≤ (9957938655737/100000000000000 : ℝ)^3645 := by
    have hnat : (825771401 : ℕ)^4669*100000000000000^3645 ≤ 9957938655737^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825771401 5000000000 9957938655737 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436175017/10000000000 : ℝ)^4669 ≤ (366453322477/800000000000 : ℝ)^3645 := by
    have hnat : (5436175017 : ℕ)^4669*800000000000^3645 ≤ 366453322477^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436175017 10000000000 366453322477 800000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322510973/2500000000 : ℝ), (-825771401/5000000000 : ℝ), (5436175017/10000000000 : ℝ)] ![(44235396014199/100000000000000 : ℝ), (9957938655737/100000000000000 : ℝ), (366453322477/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322510973/2500000000 : ℝ)|^4669 ≤ (44235396014199/100000000000000 : ℝ)^3645
        have hw : |(1322510973/2500000000 : ℝ)|=(1322510973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-825771401/5000000000 : ℝ)|^4669 ≤ (9957938655737/100000000000000 : ℝ)^3645
        have hw : |(-825771401/5000000000 : ℝ)|=(825771401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436175017/10000000000 : ℝ)|^4669 ≤ (366453322477/800000000000 : ℝ)^3645
        have hw : |(5436175017/10000000000 : ℝ)|=(5436175017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_6 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058008803/2000000000 : ℝ)*x 0 + (1359044041/2500000000 : ℝ)*x 1 + (-165154103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058008803/2000000000 : ℝ)^4669 ≤ (44235397331673/100000000000000 : ℝ)^3645 := by
    have hnat : (1058008803 : ℕ)^4669*100000000000000^3645 ≤ 44235397331673^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058008803 2000000000 44235397331673 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359044041/2500000000 : ℝ)^4669 ≤ (183226710759/400000000000 : ℝ)^3645 := by
    have hnat : (1359044041 : ℕ)^4669*400000000000^3645 ≤ 183226710759^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359044041 2500000000 183226710759 400000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165154103/1000000000 : ℝ)^4669 ≤ (1991584993991/20000000000000 : ℝ)^3645 := by
    have hnat : (165154103 : ℕ)^4669*20000000000000^3645 ≤ 1991584993991^3645*1000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165154103 1000000000 1991584993991 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058008803/2000000000 : ℝ), (1359044041/2500000000 : ℝ), (-165154103/1000000000 : ℝ)] ![(44235397331673/100000000000000 : ℝ), (183226710759/400000000000 : ℝ), (1991584993991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058008803/2000000000 : ℝ)|^4669 ≤ (44235397331673/100000000000000 : ℝ)^3645
        have hw : |(1058008803/2000000000 : ℝ)|=(1058008803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359044041/2500000000 : ℝ)|^4669 ≤ (183226710759/400000000000 : ℝ)^3645
        have hw : |(1359044041/2500000000 : ℝ)|=(1359044041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165154103/1000000000 : ℝ)|^4669 ≤ (1991584993991/20000000000000 : ℝ)^3645
        have hw : |(-165154103/1000000000 : ℝ)|=(165154103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s2_7 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058808587/2500000000 : ℝ)*x 0 + (902526537/2000000000 : ℝ)*x 1 + (3971816059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058808587/2500000000 : ℝ)^4669 ≤ (1330807008597/4000000000000 : ℝ)^3645 := by
    have hnat : (1058808587 : ℕ)^4669*4000000000000^3645 ≤ 1330807008597^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058808587 2500000000 1330807008597 4000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902526537/2000000000 : ℝ)^4669 ≤ (36086772189341/100000000000000 : ℝ)^3645 := by
    have hnat : (902526537 : ℕ)^4669*100000000000000^3645 ≤ 36086772189341^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902526537 2000000000 36086772189341 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3971816059/10000000000 : ℝ)^4669 ≤ (15321526288201/50000000000000 : ℝ)^3645 := by
    have hnat : (3971816059 : ℕ)^4669*50000000000000^3645 ≤ 15321526288201^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3971816059 10000000000 15321526288201 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058808587/2500000000 : ℝ), (902526537/2000000000 : ℝ), (3971816059/10000000000 : ℝ)] ![(1330807008597/4000000000000 : ℝ), (36086772189341/100000000000000 : ℝ), (15321526288201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058808587/2500000000 : ℝ)|^4669 ≤ (1330807008597/4000000000000 : ℝ)^3645
        have hw : |(1058808587/2500000000 : ℝ)|=(1058808587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902526537/2000000000 : ℝ)|^4669 ≤ (36086772189341/100000000000000 : ℝ)^3645
        have hw : |(902526537/2000000000 : ℝ)|=(902526537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3971816059/10000000000 : ℝ)|^4669 ≤ (15321526288201/50000000000000 : ℝ)^3645
        have hw : |(3971816059/10000000000 : ℝ)|=(3971816059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1586_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4403/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1849/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5453/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4403/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1849/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4403/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1849/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4403/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1849/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4403/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1849/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4403/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1849/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4403/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1849/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (1849/20000 : ℝ) ^ (4667/1024 : ℝ) ≤ (24205251396367/1250000000000000000 : ℝ) := by
    have hpowers : (1849/20000 : ℝ)^4667 ≤ (24205251396367/1250000000000000000 : ℝ)^1024 := by
      have hnat : (1849 : ℕ)^4667*1250000000000000000^1024 ≤ 24205251396367^1024*20000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1849 20000 24205251396367 1250000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1849/20000 : ℝ)) (X := (24205251396367/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4403/25000 : ℝ) ^ (4667/1024 : ℝ) ≤ (4566617910696147/12500000000000000000 : ℝ) := by
    have hpowers : (4403/25000 : ℝ)^4667 ≤ (4566617910696147/12500000000000000000 : ℝ)^1024 := by
      have hnat : (4403 : ℕ)^4667*12500000000000000000^1024 ≤ 4566617910696147^1024*25000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4403 25000 4566617910696147 12500000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4403/25000 : ℝ)) (X := (4566617910696147/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (625024205251396367/625000000000000000 : ℝ) ≤ (5000042486912851/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (625024205251396367/625000000000000000 : ℝ)^1024 ≤ (5000042486912851/5000000000000000 : ℝ)^4667 := by
      have hnat : (625024205251396367 : ℕ)^1024*5000000000000000^4667 ≤ 5000042486912851^4667*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625024205251396367 625000000000000000 5000042486912851 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042486912851/5000000000000000 : ℝ)) (X := (625024205251396367/625000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504808670424659817/12500000000000000000 : ℝ) ≤ (2000168788150521/2000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (12504808670424659817/12500000000000000000 : ℝ)^1024 ≤ (2000168788150521/2000000000000000 : ℝ)^4667 := by
      have hnat : (12504808670424659817 : ℕ)^1024*2000000000000000^4667 ≤ 2000168788150521^4667*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504808670424659817 12500000000000000000 2000168788150521 2000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000168788150521/2000000000000000 : ℝ)) (X := (12504808670424659817/12500000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254566617910696147/6250000000000000000 : ℝ) ≤ (2500400726919877/2500000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (6254566617910696147/6250000000000000000 : ℝ)^1024 ≤ (2500400726919877/2500000000000000 : ℝ)^4667 := by
      have hnat : (6254566617910696147 : ℕ)^1024*2500000000000000^4667 ≤ 2500400726919877^4667*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254566617910696147 6250000000000000000 2500400726919877 2500000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500400726919877/2500000000000000 : ℝ)) (X := (6254566617910696147/6250000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24205251396367/1250000000000000000 : ℝ) ≤ ((20914169419380303041/20917500000000000000 : ℝ)+2*(758966926903/836700000000000 : ℝ)*(1849/20000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (20914169419380303041/20917500000000000000 : ℝ)+2*(758966926903/836700000000000 : ℝ)*(1849/20000 : ℝ)=(5000042486912851/5000000000000000 : ℝ) by norm_num, show 1+2*(24205251396367/1250000000000000000 : ℝ)=(625024205251396367/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4566617910696147/12500000000000000000 : ℝ)+(24205251396367/1250000000000000000 : ℝ) ≤ ((20914169419380303041/20917500000000000000 : ℝ)+(758966926903/836700000000000 : ℝ)*((4403/25000 : ℝ)+(1849/20000 : ℝ)))^(4667/1024 : ℝ) := by
    rw [show (20914169419380303041/20917500000000000000 : ℝ)+(758966926903/836700000000000 : ℝ)*((4403/25000 : ℝ)+(1849/20000 : ℝ))=(2000168788150521/2000000000000000 : ℝ) by norm_num, show 1+(4566617910696147/12500000000000000000 : ℝ)+(24205251396367/1250000000000000000 : ℝ)=(12504808670424659817/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4566617910696147/12500000000000000000 : ℝ) ≤ ((20914169419380303041/20917500000000000000 : ℝ)+2*(758966926903/836700000000000 : ℝ)*(4403/25000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (20914169419380303041/20917500000000000000 : ℝ)+2*(758966926903/836700000000000 : ℝ)*(4403/25000 : ℝ)=(2500400726919877/2500000000000000 : ℝ) by norm_num, show 1+2*(4566617910696147/12500000000000000000 : ℝ)=(6254566617910696147/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20914169419380303041/20917500000000000000 : ℝ)*(X 1 0+X 2 0)+(758966926903/836700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (1849/20000 : ℝ)) (hi := (4403/25000 : ℝ)) (c := (20914169419380303041/20917500000000000000 : ℝ)) (alpha := (758966926903/836700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20914169419380303041/20917500000000000000 : ℝ)*(X 0 1+X 2 1)+(758966926903/836700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (1849/20000 : ℝ)) (hi := (4403/25000 : ℝ)) (c := (20914169419380303041/20917500000000000000 : ℝ)) (alpha := (758966926903/836700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20914169419380303041/20917500000000000000 : ℝ)*(X 0 2+X 1 2)+(758966926903/836700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (1849/20000 : ℝ)) (hi := (4403/25000 : ℝ)) (c := (20914169419380303041/20917500000000000000 : ℝ)) (alpha := (758966926903/836700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1761893107/10000000000 : ℝ)*X 0 0+(33984607/62500000 : ℝ)*X 0 1+(5208188791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350838873/10000000000 : ℝ)*X 1 0+(-469882001/2500000000 : ℝ)*X 1 1+(104163777/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668854847/1250000000 : ℝ)*X 2 0+(2604094651/5000000000 : ℝ)*X 2 1+(-469881883/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4235145313/10000000000 : ℝ)*X 0 0+(3968561949/10000000000 : ℝ)*X 0 1+(4515858937/10000000000 : ℝ)*X 0 2+(4235145313/10000000000 : ℝ)*X 1 0+(3968561949/10000000000 : ℝ)*X 1 1+(4515858937/10000000000 : ℝ)*X 1 2+(4235145313/10000000000 : ℝ)*X 2 0+(3968561949/10000000000 : ℝ)*X 2 1+(4515858937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-880965067/5000000000 : ℝ)*X 0 0+(2604770677/5000000000 : ℝ)*X 0 1+(5436173759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322510973/2500000000 : ℝ)*X 1 0+(-825771401/5000000000 : ℝ)*X 1 1+(5436175017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058008803/2000000000 : ℝ)*X 2 0+(1359044041/2500000000 : ℝ)*X 2 1+(-165154103/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1058808587/2500000000 : ℝ)*X 0 0+(902526537/2000000000 : ℝ)*X 0 1+(3971816059/10000000000 : ℝ)*X 0 2+(1058808587/2500000000 : ℝ)*X 1 0+(902526537/2000000000 : ℝ)*X 1 1+(3971816059/10000000000 : ℝ)*X 1 2+(1058808587/2500000000 : ℝ)*X 2 0+(902526537/2000000000 : ℝ)*X 2 1+(3971816059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63199913231164644828250911/5447265625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1912100777/100000000000000 : ℝ)*(base19) + (355540411/20000000000000 : ℝ)*(base23) + (29620241/100000000000000 : ℝ)*(lower2) + (82233847/100000000000000 : ℝ)*(upper3) + (93147947/20000000000000 : ℝ)*(upper5) + (386714578581591/12500000000000 : ℝ)*(major0) + (386714578581591/12500000000000 : ℝ)*(major1) + (386714578581591/12500000000000 : ℝ)*(major2) + (2180103169824631/50000000000000 : ℝ)*(sp0) + (1090060534418497/25000000000000 : ℝ)*(sp1) + (436024227207271/10000000000000 : ℝ)*(sp2) + (1827176957604711/100000000000000 : ℝ)*(sp3) + (37710125503/100000000000000 : ℝ)*(sp4) + (5931594063/50000000000000 : ℝ)*(sp7) + (913594410396419/50000000000000 : ℝ)*(f.failure) + (872048809954953/20000000000000 : ℝ)*(f.sum) + (11655283709653/13945000000000000000000000000 : ℝ)*base65 + (595571654590487327/87156250000000000000000000000000 : ℝ)*base67 + (1094177821934206077/87156250000000000000000000000000 : ℝ)*base69 + (326468290884387673/87156250000000000000000000000000 : ℝ)*base72 + (1411242894463/13945000000000000000000000000 : ℝ)*base73 + (1441797406521424827/87156250000000000000000000000000 : ℝ)*base75 + (42371081646737327/87156250000000000000000000000000 : ℝ)*base77 + (658847796487299827/87156250000000000000000000000000 : ℝ)*base79 + (45535512328783/13945000000000000000000000000 : ℝ)*base81 + (813147/100000000000000000000 : ℝ)*base89 + (813147/100000000000000000000 : ℝ)*base91 + (813147/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1452429981784083043322241987/174312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26466329/50000000000000 : ℝ)*(base8) + (44606883/10000000000000 : ℝ)*(base15) + (32610589/50000000000000 : ℝ)*(lower2) + (5266049/20000000000000 : ℝ)*(lower4) + (3130744600162293/100000000000000 : ℝ)*(major0) + (3130744600162293/100000000000000 : ℝ)*(major1) + (3130744600162293/100000000000000 : ℝ)*(major2) + (14973193483/100000000000000 : ℝ)*(sp1) + (9400283511/20000000000000 : ℝ)*(sp2) + (706665759/50000000000000 : ℝ)*(sp3) + (441243085276461/10000000000000 : ℝ)*(sp4) + (1103103871608739/25000000000000 : ℝ)*(sp5) + (2206191952139857/50000000000000 : ℝ)*(sp6) + (462264150887831/25000000000000 : ℝ)*(sp7) + (924529008441421/50000000000000 : ℝ)*(f.failure) + (1103107726424317/25000000000000 : ℝ)*(f.sum) + (208499868409777/13945000000000000000000000000 : ℝ)*base66 + (4738594715065802671/697250000000000000000000000000000 : ℝ)*base67 + (4387042576406697329/697250000000000000000000000000000 : ℝ)*base70 + (1607949302612052671/697250000000000000000000000000000 : ℝ)*base71 + (38260071647517/13945000000000000000000000000 : ℝ)*base74 + (1351262302176302671/697250000000000000000000000000000 : ℝ)*base75 + (5398917787504302671/697250000000000000000000000000000 : ℝ)*base77 + (137545321222302671/697250000000000000000000000000000 : ℝ)*base79 + (25665643837697/13945000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (670773/100000000000000000000 : ℝ)*base89 + (670773/100000000000000000000 : ℝ)*base91 + (670773/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1586_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4403/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1849/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1586_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1586_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1586_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1586_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1586_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1586_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

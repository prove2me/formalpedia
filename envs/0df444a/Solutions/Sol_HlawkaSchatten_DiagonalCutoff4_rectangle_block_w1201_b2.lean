-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1201_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:11.527722+00:00
-- url     : https://prove2.me/submissions/659266b4-e4ff-45ce-bcad-b9ab7693409c

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
theorem support_rectangle_w1201_s6_0 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138964611/10000000000 : ℝ)*x 0 + (5392203523/10000000000 : ℝ)*x 1 + (5266411623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138964611/10000000000 : ℝ)^4197 ≤ (3250760101619/25000000000000 : ℝ)^3173 := by
    have hnat : (2138964611 : ℕ)^4197*25000000000000^3173 ≤ 3250760101619^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138964611 10000000000 3250760101619 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392203523/10000000000 : ℝ)^4197 ≤ (11044373849993/25000000000000 : ℝ)^3173 := by
    have hnat : (5392203523 : ℕ)^4197*25000000000000^3173 ≤ 11044373849993^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392203523 10000000000 11044373849993 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266411623/10000000000 : ℝ)^4197 ≤ (42819464183243/100000000000000 : ℝ)^3173 := by
    have hnat : (5266411623 : ℕ)^4197*100000000000000^3173 ≤ 42819464183243^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266411623 10000000000 42819464183243 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138964611/10000000000 : ℝ), (5392203523/10000000000 : ℝ), (5266411623/10000000000 : ℝ)] ![(3250760101619/25000000000000 : ℝ), (11044373849993/25000000000000 : ℝ), (42819464183243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138964611/10000000000 : ℝ)|^4197 ≤ (3250760101619/25000000000000 : ℝ)^3173
        have hw : |(-2138964611/10000000000 : ℝ)|=(2138964611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392203523/10000000000 : ℝ)|^4197 ≤ (11044373849993/25000000000000 : ℝ)^3173
        have hw : |(5392203523/10000000000 : ℝ)|=(5392203523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266411623/10000000000 : ℝ)|^4197 ≤ (42819464183243/100000000000000 : ℝ)^3173
        have hw : |(5266411623/10000000000 : ℝ)|=(5266411623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_1 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344574349/10000000000 : ℝ)*x 0 + (-2202757751/10000000000 : ℝ)*x 1 + (5266411699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344574349/10000000000 : ℝ)^4197 ≤ (43662081556827/100000000000000 : ℝ)^3173 := by
    have hnat : (5344574349 : ℕ)^4197*100000000000000^3173 ≤ 43662081556827^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344574349 10000000000 43662081556827 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202757751/10000000000 : ℝ)^4197 ≤ (13518453424171/100000000000000 : ℝ)^3173 := by
    have hnat : (2202757751 : ℕ)^4197*100000000000000^3173 ≤ 13518453424171^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202757751 10000000000 13518453424171 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266411699/10000000000 : ℝ)^4197 ≤ (21409732500297/50000000000000 : ℝ)^3173 := by
    have hnat : (5266411699 : ℕ)^4197*50000000000000^3173 ≤ 21409732500297^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266411699 10000000000 21409732500297 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344574349/10000000000 : ℝ), (-2202757751/10000000000 : ℝ), (5266411699/10000000000 : ℝ)] ![(43662081556827/100000000000000 : ℝ), (13518453424171/100000000000000 : ℝ), (21409732500297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344574349/10000000000 : ℝ)|^4197 ≤ (43662081556827/100000000000000 : ℝ)^3173
        have hw : |(5344574349/10000000000 : ℝ)|=(5344574349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202757751/10000000000 : ℝ)|^4197 ≤ (13518453424171/100000000000000 : ℝ)^3173
        have hw : |(-2202757751/10000000000 : ℝ)|=(2202757751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266411699/10000000000 : ℝ)|^4197 ≤ (21409732500297/50000000000000 : ℝ)^3173
        have hw : |(5266411699/10000000000 : ℝ)|=(5266411699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_2 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267228727/500000000 : ℝ)*x 0 + (5266411257/10000000000 : ℝ)*x 1 + (-1101379041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267228727/500000000 : ℝ)^4197 ≤ (43662083620751/100000000000000 : ℝ)^3173 := by
    have hnat : (267228727 : ℕ)^4197*100000000000000^3173 ≤ 43662083620751^3173*500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267228727 500000000 43662083620751 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266411257/10000000000 : ℝ)^4197 ≤ (856389204941/2000000000000 : ℝ)^3173 := by
    have hnat : (5266411257 : ℕ)^4197*2000000000000^3173 ≤ 856389204941^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266411257 10000000000 856389204941 2000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101379041/5000000000 : ℝ)^4197 ≤ (6759228055553/50000000000000 : ℝ)^3173 := by
    have hnat : (1101379041 : ℕ)^4197*50000000000000^3173 ≤ 6759228055553^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101379041 5000000000 6759228055553 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267228727/500000000 : ℝ), (5266411257/10000000000 : ℝ), (-1101379041/5000000000 : ℝ)] ![(43662083620751/100000000000000 : ℝ), (856389204941/2000000000000 : ℝ), (6759228055553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267228727/500000000 : ℝ)|^4197 ≤ (43662083620751/100000000000000 : ℝ)^3173
        have hw : |(267228727/500000000 : ℝ)|=(267228727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266411257/10000000000 : ℝ)|^4197 ≤ (856389204941/2000000000000 : ℝ)^3173
        have hw : |(5266411257/10000000000 : ℝ)|=(5266411257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1101379041/5000000000 : ℝ)|^4197 ≤ (6759228055553/50000000000000 : ℝ)^3173
        have hw : |(-1101379041/5000000000 : ℝ)|=(1101379041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_3 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (272275957/625000000 : ℝ)*x 0 + (2115819637/5000000000 : ℝ)*x 1 + (2242400069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272275957/625000000 : ℝ)^4197 ≤ (33317162121129/100000000000000 : ℝ)^3173 := by
    have hnat : (272275957 : ℕ)^4197*100000000000000^3173 ≤ 33317162121129^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272275957 625000000 33317162121129 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115819637/5000000000 : ℝ)^4197 ≤ (16030401517687/50000000000000 : ℝ)^3173 := by
    have hnat : (2115819637 : ℕ)^4197*50000000000000^3173 ≤ 16030401517687^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115819637 5000000000 16030401517687 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242400069/5000000000 : ℝ)^4197 ≤ (8655508706731/25000000000000 : ℝ)^3173 := by
    have hnat : (2242400069 : ℕ)^4197*25000000000000^3173 ≤ 8655508706731^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242400069 5000000000 8655508706731 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272275957/625000000 : ℝ), (2115819637/5000000000 : ℝ), (2242400069/5000000000 : ℝ)] ![(33317162121129/100000000000000 : ℝ), (16030401517687/50000000000000 : ℝ), (8655508706731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272275957/625000000 : ℝ)|^4197 ≤ (33317162121129/100000000000000 : ℝ)^3173
        have hw : |(272275957/625000000 : ℝ)|=(272275957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115819637/5000000000 : ℝ)|^4197 ≤ (16030401517687/50000000000000 : ℝ)^3173
        have hw : |(2115819637/5000000000 : ℝ)|=(2115819637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242400069/5000000000 : ℝ)|^4197 ≤ (8655508706731/25000000000000 : ℝ)^3173
        have hw : |(2242400069/5000000000 : ℝ)|=(2242400069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_4 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-427793927/2000000000 : ℝ)*x 0 + (5266729177/10000000000 : ℝ)*x 1 + (1078376929/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427793927/2000000000 : ℝ)^4197 ≤ (13003080804489/100000000000000 : ℝ)^3173 := by
    have hnat : (427793927 : ℕ)^4197*100000000000000^3173 ≤ 13003080804489^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427793927 2000000000 13003080804489 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266729177/10000000000 : ℝ)^4197 ≤ (21411439695539/50000000000000 : ℝ)^3173 := by
    have hnat : (5266729177 : ℕ)^4197*50000000000000^3173 ≤ 21411439695539^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266729177 10000000000 21411439695539 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078376929/2000000000 : ℝ)^4197 ≤ (11043509948681/25000000000000 : ℝ)^3173 := by
    have hnat : (1078376929 : ℕ)^4197*25000000000000^3173 ≤ 11043509948681^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078376929 2000000000 11043509948681 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427793927/2000000000 : ℝ), (5266729177/10000000000 : ℝ), (1078376929/2000000000 : ℝ)] ![(13003080804489/100000000000000 : ℝ), (21411439695539/50000000000000 : ℝ), (11043509948681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427793927/2000000000 : ℝ)|^4197 ≤ (13003080804489/100000000000000 : ℝ)^3173
        have hw : |(-427793927/2000000000 : ℝ)|=(427793927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266729177/10000000000 : ℝ)|^4197 ≤ (21411439695539/50000000000000 : ℝ)^3173
        have hw : |(5266729177/10000000000 : ℝ)|=(5266729177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078376929/2000000000 : ℝ)|^4197 ≤ (11043509948681/25000000000000 : ℝ)^3173
        have hw : |(1078376929/2000000000 : ℝ)|=(1078376929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_5 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062513743/2000000000 : ℝ)*x 0 + (-2077284599/10000000000 : ℝ)*x 1 + (673985567/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062513743/2000000000 : ℝ)^4197 ≤ (21658283554191/50000000000000 : ℝ)^3173 := by
    have hnat : (1062513743 : ℕ)^4197*50000000000000^3173 ≤ 21658283554191^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062513743 2000000000 21658283554191 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077284599/10000000000 : ℝ)^4197 ≤ (3127348563701/25000000000000 : ℝ)^3173 := by
    have hnat : (2077284599 : ℕ)^4197*25000000000000^3173 ≤ 3127348563701^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077284599 10000000000 3127348563701 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673985567/1250000000 : ℝ)^4197 ≤ (5521754826691/12500000000000 : ℝ)^3173 := by
    have hnat : (673985567 : ℕ)^4197*12500000000000^3173 ≤ 5521754826691^3173*1250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673985567 1250000000 5521754826691 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062513743/2000000000 : ℝ), (-2077284599/10000000000 : ℝ), (673985567/1250000000 : ℝ)] ![(21658283554191/50000000000000 : ℝ), (3127348563701/25000000000000 : ℝ), (5521754826691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062513743/2000000000 : ℝ)|^4197 ≤ (21658283554191/50000000000000 : ℝ)^3173
        have hw : |(1062513743/2000000000 : ℝ)|=(1062513743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077284599/10000000000 : ℝ)|^4197 ≤ (3127348563701/25000000000000 : ℝ)^3173
        have hw : |(-2077284599/10000000000 : ℝ)|=(2077284599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673985567/1250000000 : ℝ)|^4197 ≤ (5521754826691/12500000000000 : ℝ)^3173
        have hw : |(673985567/1250000000 : ℝ)|=(673985567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_6 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312568629/10000000000 : ℝ)*x 0 + (269594233/500000000 : ℝ)*x 1 + (-519321137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312568629/10000000000 : ℝ)^4197 ≤ (10829141545219/25000000000000 : ℝ)^3173 := by
    have hnat : (5312568629 : ℕ)^4197*25000000000000^3173 ≤ 10829141545219^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312568629 10000000000 10829141545219 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269594233/500000000 : ℝ)^4197 ≤ (22087019978637/50000000000000 : ℝ)^3173 := by
    have hnat : (269594233 : ℕ)^4197*50000000000000^3173 ≤ 22087019978637^3173*500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269594233 500000000 22087019978637 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519321137/2500000000 : ℝ)^4197 ≤ (12509393848567/100000000000000 : ℝ)^3173 := by
    have hnat : (519321137 : ℕ)^4197*100000000000000^3173 ≤ 12509393848567^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519321137 2500000000 12509393848567 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312568629/10000000000 : ℝ), (269594233/500000000 : ℝ), (-519321137/2500000000 : ℝ)] ![(10829141545219/25000000000000 : ℝ), (22087019978637/50000000000000 : ℝ), (12509393848567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312568629/10000000000 : ℝ)|^4197 ≤ (10829141545219/25000000000000 : ℝ)^3173
        have hw : |(5312568629/10000000000 : ℝ)|=(5312568629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269594233/500000000 : ℝ)|^4197 ≤ (22087019978637/50000000000000 : ℝ)^3173
        have hw : |(269594233/500000000 : ℝ)|=(269594233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519321137/2500000000 : ℝ)|^4197 ≤ (12509393848567/100000000000000 : ℝ)^3173
        have hw : |(-519321137/2500000000 : ℝ)|=(519321137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s6_7 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435642467/1000000000 : ℝ)*x 0 + (4484160087/10000000000 : ℝ)*x 1 + (4232281963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435642467/1000000000 : ℝ)^4197 ≤ (33317256786429/100000000000000 : ℝ)^3173 := by
    have hnat : (435642467 : ℕ)^4197*100000000000000^3173 ≤ 33317256786429^3173*1000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435642467 1000000000 33317256786429 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484160087/10000000000 : ℝ)^4197 ≤ (34615499264443/100000000000000 : ℝ)^3173 := by
    have hnat : (4484160087 : ℕ)^4197*100000000000000^3173 ≤ 34615499264443^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484160087 10000000000 34615499264443 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232281963/10000000000 : ℝ)^4197 ≤ (32067243929547/100000000000000 : ℝ)^3173 := by
    have hnat : (4232281963 : ℕ)^4197*100000000000000^3173 ≤ 32067243929547^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232281963 10000000000 32067243929547 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435642467/1000000000 : ℝ), (4484160087/10000000000 : ℝ), (4232281963/10000000000 : ℝ)] ![(33317256786429/100000000000000 : ℝ), (34615499264443/100000000000000 : ℝ), (32067243929547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435642467/1000000000 : ℝ)|^4197 ≤ (33317256786429/100000000000000 : ℝ)^3173
        have hw : |(435642467/1000000000 : ℝ)|=(435642467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484160087/10000000000 : ℝ)|^4197 ≤ (34615499264443/100000000000000 : ℝ)^3173
        have hw : |(4484160087/10000000000 : ℝ)|=(4484160087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232281963/10000000000 : ℝ)|^4197 ≤ (32067243929547/100000000000000 : ℝ)^3173
        have hw : |(4232281963/10000000000 : ℝ)|=(4232281963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1201_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11423/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11399/100000 : ℝ) ^ (8393/2048 : ℝ) ≤ (6821402069120023/50000000000000000000 : ℝ) := by
    have hpowers : (11399/100000 : ℝ)^8393 ≤ (6821402069120023/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11399 : ℕ)^8393*50000000000000000000^2048 ≤ 6821402069120023^2048*100000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11399 100000 6821402069120023 50000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11399/100000 : ℝ)) (X := (6821402069120023/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14113/100000 : ℝ) ^ (8393/2048 : ℝ) ≤ (32735362538659/100000000000000000 : ℝ) := by
    have hpowers : (14113/100000 : ℝ)^8393 ≤ (32735362538659/100000000000000000 : ℝ)^2048 := by
      have hnat : (14113 : ℕ)^8393*100000000000000000^2048 ≤ 32735362538659^2048*100000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14113 100000 32735362538659 100000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14113/100000 : ℝ)) (X := (32735362538659/100000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006821402069120023/25000000000000000000 : ℝ) ≤ (10000665735294083/10000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (25006821402069120023/25000000000000000000 : ℝ)^2048 ≤ (10000665735294083/10000000000000000 : ℝ)^8393 := by
      have hnat : (25006821402069120023 : ℕ)^2048*10000000000000000^8393 ≤ 10000665735294083^8393*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006821402069120023 25000000000000000000 10000665735294083 10000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665735294083/10000000000000000 : ℝ)) (X := (25006821402069120023/25000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023189083338449523/50000000000000000000 : ℝ) ≤ (5000565744303749/5000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (50023189083338449523/50000000000000000000 : ℝ)^2048 ≤ (5000565744303749/5000000000000000 : ℝ)^8393 := by
      have hnat : (50023189083338449523 : ℕ)^2048*5000000000000000^8393 ≤ 5000565744303749^8393*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023189083338449523 50000000000000000000 5000565744303749 5000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000565744303749/5000000000000000 : ℝ)) (X := (50023189083338449523/50000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032735362538659/50000000000000000 : ℝ) ≤ (10001597241920913/10000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (50032735362538659/50000000000000000 : ℝ)^2048 ≤ (10001597241920913/10000000000000000 : ℝ)^8393 := by
      have hnat : (50032735362538659 : ℕ)^2048*10000000000000000^8393 ≤ 10001597241920913^8393*50000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032735362538659 50000000000000000 10001597241920913 10000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001597241920913/10000000000000000 : ℝ)) (X := (50032735362538659/50000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6821402069120023/50000000000000000000 : ℝ) ≤ ((6782797140387226523/6785000000000000000 : ℝ)+2*(93150662683/54280000000000 : ℝ)*(11399/100000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (6782797140387226523/6785000000000000000 : ℝ)+2*(93150662683/54280000000000 : ℝ)*(11399/100000 : ℝ)=(10000665735294083/10000000000000000 : ℝ) by norm_num, show 1+2*(6821402069120023/50000000000000000000 : ℝ)=(25006821402069120023/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32735362538659/100000000000000000 : ℝ)+(6821402069120023/50000000000000000000 : ℝ) ≤ ((6782797140387226523/6785000000000000000 : ℝ)+(93150662683/54280000000000 : ℝ)*((14113/100000 : ℝ)+(11399/100000 : ℝ)))^(8393/2048 : ℝ) := by
    rw [show (6782797140387226523/6785000000000000000 : ℝ)+(93150662683/54280000000000 : ℝ)*((14113/100000 : ℝ)+(11399/100000 : ℝ))=(5000565744303749/5000000000000000 : ℝ) by norm_num, show 1+(32735362538659/100000000000000000 : ℝ)+(6821402069120023/50000000000000000000 : ℝ)=(50023189083338449523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32735362538659/100000000000000000 : ℝ) ≤ ((6782797140387226523/6785000000000000000 : ℝ)+2*(93150662683/54280000000000 : ℝ)*(14113/100000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (6782797140387226523/6785000000000000000 : ℝ)+2*(93150662683/54280000000000 : ℝ)*(14113/100000 : ℝ)=(10001597241920913/10000000000000000 : ℝ) by norm_num, show 1+2*(32735362538659/100000000000000000 : ℝ)=(50032735362538659/50000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6782797140387226523/6785000000000000000 : ℝ)*(X 1 0+X 2 0)+(93150662683/54280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (6782797140387226523/6785000000000000000 : ℝ)) (alpha := (93150662683/54280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6782797140387226523/6785000000000000000 : ℝ)*(X 0 1+X 2 1)+(93150662683/54280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (6782797140387226523/6785000000000000000 : ℝ)) (alpha := (93150662683/54280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6782797140387226523/6785000000000000000 : ℝ)*(X 0 2+X 1 2)+(93150662683/54280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (6782797140387226523/6785000000000000000 : ℝ)) (alpha := (93150662683/54280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138964611/10000000000 : ℝ)*X 0 0+(5392203523/10000000000 : ℝ)*X 0 1+(5266411623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344574349/10000000000 : ℝ)*X 1 0+(-2202757751/10000000000 : ℝ)*X 1 1+(5266411699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267228727/500000000 : ℝ)*X 2 0+(5266411257/10000000000 : ℝ)*X 2 1+(-1101379041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272275957/625000000 : ℝ)*X 0 0+(2115819637/5000000000 : ℝ)*X 0 1+(2242400069/5000000000 : ℝ)*X 0 2+(272275957/625000000 : ℝ)*X 1 0+(2115819637/5000000000 : ℝ)*X 1 1+(2242400069/5000000000 : ℝ)*X 1 2+(272275957/625000000 : ℝ)*X 2 0+(2115819637/5000000000 : ℝ)*X 2 1+(2242400069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427793927/2000000000 : ℝ)*X 0 0+(5266729177/10000000000 : ℝ)*X 0 1+(1078376929/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062513743/2000000000 : ℝ)*X 1 0+(-2077284599/10000000000 : ℝ)*X 1 1+(673985567/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312568629/10000000000 : ℝ)*X 2 0+(269594233/500000000 : ℝ)*X 2 1+(-519321137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435642467/1000000000 : ℝ)*X 0 0+(4484160087/10000000000 : ℝ)*X 0 1+(4232281963/10000000000 : ℝ)*X 0 2+(435642467/1000000000 : ℝ)*X 1 0+(4484160087/10000000000 : ℝ)*X 1 1+(4232281963/10000000000 : ℝ)*X 1 2+(435642467/1000000000 : ℝ)*X 2 0+(4484160087/10000000000 : ℝ)*X 2 1+(4232281963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (162218681268569881230759633/16962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731015867/100000000000000 : ℝ)*(base19) + (1238046789/100000000000000 : ℝ)*(base23) + (30709909/20000000000000 : ℝ)*(lower2) + (160907169/50000000000000 : ℝ)*(upper3) + (68174341/25000000000000 : ℝ)*(lower4) + (5949883919712859/100000000000000 : ℝ)*(major0) + (5949883919712859/100000000000000 : ℝ)*(major1) + (297494195985643/5000000000000 : ℝ)*(major2) + (63597287182019/800000000000 : ℝ)*(sp0) + (7949666912087049/100000000000000 : ℝ)*(sp1) + (3974833202528063/50000000000000 : ℝ)*(sp2) + (3950075321904181/100000000000000 : ℝ)*(sp3) + (6745350541/100000000000000 : ℝ)*(sp4) + (3069454947/12500000000000 : ℝ)*(sp7) + (1975049938771879/50000000000000 : ℝ)*(f.failure) + (1987416910775729/25000000000000 : ℝ)*(f.sum) + (16102119409219/5428000000000000000000000000 : ℝ)*base66 + (501494451513459257/678500000000000000000000000000000 : ℝ)*base67 + (653223561619865539/33925000000000000000000000000000 : ℝ)*base69 + (2049058905029040743/678500000000000000000000000000000 : ℝ)*base72 + (16217250100881/5428000000000000000000000000 : ℝ)*base73 + (655809030616940539/33925000000000000000000000000000 : ℝ)*base75 + (7590563187475915743/678500000000000000000000000000000 : ℝ)*base78 + (6562996576428084257/678500000000000000000000000000000 : ℝ)*base79 + (8562539441779/2714000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13710539/1250000000000000000000 : ℝ)*base89 + (13710539/1250000000000000000000 : ℝ)*base91 + (1210539/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (161331212751620949896187627/21203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (719868659/50000000000000 : ℝ)*(base19) + (195449489/12500000000000 : ℝ)*(base23) + (28367441/25000000000000 : ℝ)*(upper3) + (57595121/50000000000000 : ℝ)*(lower4) + (9049087/5000000000000 : ℝ)*(upper5) + (747514541656317/12500000000000 : ℝ)*(major0) + (747514541656317/12500000000000 : ℝ)*(major1) + (747514541656317/12500000000000 : ℝ)*(major2) + (18445671499/50000000000000 : ℝ)*(sp1) + (42928971167/100000000000000 : ℝ)*(sp2) + (7990061378542931/100000000000000 : ℝ)*(sp4) + (998752880932827/12500000000000 : ℝ)*(sp5) + (1997504221493963/25000000000000 : ℝ)*(sp6) + (3970171034330089/100000000000000 : ℝ)*(sp7) + (3970171034330089/100000000000000 : ℝ)*(f.failure) + (7990061378542931/100000000000000 : ℝ)*(f.sum) + (7470391344821/1357000000000000000000000000 : ℝ)*base66 + (1672184418218645791/84812500000000000000000000000000 : ℝ)*base67 + (959731966787145791/84812500000000000000000000000000 : ℝ)*base69 + (653336746443479209/84812500000000000000000000000000 : ℝ)*base72 + (1624448166867/1357000000000000000000000000 : ℝ)*base73 + (314712101222708291/84812500000000000000000000000000 : ℝ)*base75 + (384444410086395791/84812500000000000000000000000000 : ℝ)*base77 + (2146993675945895791/84812500000000000000000000000000 : ℝ)*base79 + (160832239229/54280000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3962149/2500000000000000000000 : ℝ)*base89 + (3962149/2500000000000000000000 : ℝ)*base91 + (3962149/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1201_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1201_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1201_s7_0 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069492477/5000000000 : ℝ)*x 0 + (539196561/1000000000 : ℝ)*x 1 + (5266636141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069492477/5000000000 : ℝ)^4197 ≤ (6501601992423/50000000000000 : ℝ)^3173 := by
    have hnat : (1069492477 : ℕ)^4197*50000000000000^3173 ≤ 6501601992423^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069492477 5000000000 6501601992423 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539196561/1000000000 : ℝ)^4197 ≤ (44174917186977/100000000000000 : ℝ)^3173 := by
    have hnat : (539196561 : ℕ)^4197*100000000000000^3173 ≤ 44174917186977^3173*1000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539196561 1000000000 44174917186977 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266636141/10000000000 : ℝ)^4197 ≤ (8564375761409/20000000000000 : ℝ)^3173 := by
    have hnat : (5266636141 : ℕ)^4197*20000000000000^3173 ≤ 8564375761409^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266636141 10000000000 8564375761409 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069492477/5000000000 : ℝ), (539196561/1000000000 : ℝ), (5266636141/10000000000 : ℝ)] ![(6501601992423/50000000000000 : ℝ), (44174917186977/100000000000000 : ℝ), (8564375761409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069492477/5000000000 : ℝ)|^4197 ≤ (6501601992423/50000000000000 : ℝ)^3173
        have hw : |(-1069492477/5000000000 : ℝ)|=(1069492477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539196561/1000000000 : ℝ)|^4197 ≤ (44174917186977/100000000000000 : ℝ)^3173
        have hw : |(539196561/1000000000 : ℝ)|=(539196561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266636141/10000000000 : ℝ)|^4197 ≤ (8564375761409/20000000000000 : ℝ)^3173
        have hw : |(5266636141/10000000000 : ℝ)|=(5266636141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_1 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344514577/10000000000 : ℝ)*x 0 + (-55063499/250000000 : ℝ)*x 1 + (5266636141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344514577/10000000000 : ℝ)^4197 ≤ (43661435668829/100000000000000 : ℝ)^3173 := by
    have hnat : (5344514577 : ℕ)^4197*100000000000000^3173 ≤ 43661435668829^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344514577 10000000000 43661435668829 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55063499/250000000 : ℝ)^4197 ≤ (2703337101193/20000000000000 : ℝ)^3173 := by
    have hnat : (55063499 : ℕ)^4197*20000000000000^3173 ≤ 2703337101193^3173*250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55063499 250000000 2703337101193 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266636141/10000000000 : ℝ)^4197 ≤ (8564375761409/20000000000000 : ℝ)^3173 := by
    have hnat : (5266636141 : ℕ)^4197*20000000000000^3173 ≤ 8564375761409^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266636141 10000000000 8564375761409 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344514577/10000000000 : ℝ), (-55063499/250000000 : ℝ), (5266636141/10000000000 : ℝ)] ![(43661435668829/100000000000000 : ℝ), (2703337101193/20000000000000 : ℝ), (8564375761409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344514577/10000000000 : ℝ)|^4197 ≤ (43661435668829/100000000000000 : ℝ)^3173
        have hw : |(5344514577/10000000000 : ℝ)|=(5344514577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55063499/250000000 : ℝ)|^4197 ≤ (2703337101193/20000000000000 : ℝ)^3173
        have hw : |(-55063499/250000000 : ℝ)|=(55063499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266636141/10000000000 : ℝ)|^4197 ≤ (8564375761409/20000000000000 : ℝ)^3173
        have hw : |(5266636141/10000000000 : ℝ)|=(5266636141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_2 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344514577/10000000000 : ℝ)*x 0 + (5266636141/10000000000 : ℝ)*x 1 + (-55063499/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344514577/10000000000 : ℝ)^4197 ≤ (43661435668829/100000000000000 : ℝ)^3173 := by
    have hnat : (5344514577 : ℕ)^4197*100000000000000^3173 ≤ 43661435668829^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344514577 10000000000 43661435668829 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266636141/10000000000 : ℝ)^4197 ≤ (8564375761409/20000000000000 : ℝ)^3173 := by
    have hnat : (5266636141 : ℕ)^4197*20000000000000^3173 ≤ 8564375761409^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266636141 10000000000 8564375761409 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55063499/250000000 : ℝ)^4197 ≤ (2703337101193/20000000000000 : ℝ)^3173 := by
    have hnat : (55063499 : ℕ)^4197*20000000000000^3173 ≤ 2703337101193^3173*250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55063499 250000000 2703337101193 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344514577/10000000000 : ℝ), (5266636141/10000000000 : ℝ), (-55063499/250000000 : ℝ)] ![(43661435668829/100000000000000 : ℝ), (8564375761409/20000000000000 : ℝ), (2703337101193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344514577/10000000000 : ℝ)|^4197 ≤ (43661435668829/100000000000000 : ℝ)^3173
        have hw : |(5344514577/10000000000 : ℝ)|=(5344514577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266636141/10000000000 : ℝ)|^4197 ≤ (8564375761409/20000000000000 : ℝ)^3173
        have hw : |(5266636141/10000000000 : ℝ)|=(5266636141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55063499/250000000 : ℝ)|^4197 ≤ (2703337101193/20000000000000 : ℝ)^3173
        have hw : |(-55063499/250000000 : ℝ)|=(55063499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_3 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (68069167/156250000 : ℝ)*x 0 + (264506509/625000000 : ℝ)*x 1 + (2242166309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68069167/156250000 : ℝ)^4197 ≤ (8329319300119/25000000000000 : ℝ)^3173 := by
    have hnat : (68069167 : ℕ)^4197*25000000000000^3173 ≤ 8329319300119^3173*156250000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68069167 156250000 8329319300119 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264506509/625000000 : ℝ)^4197 ≤ (3206546183329/10000000000000 : ℝ)^3173 := by
    have hnat : (264506509 : ℕ)^4197*10000000000000^3173 ≤ 3206546183329^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264506509 625000000 3206546183329 10000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242166309/5000000000 : ℝ)^4197 ≤ (34617260949311/100000000000000 : ℝ)^3173 := by
    have hnat : (2242166309 : ℕ)^4197*100000000000000^3173 ≤ 34617260949311^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242166309 5000000000 34617260949311 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68069167/156250000 : ℝ), (264506509/625000000 : ℝ), (2242166309/5000000000 : ℝ)] ![(8329319300119/25000000000000 : ℝ), (3206546183329/10000000000000 : ℝ), (34617260949311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68069167/156250000 : ℝ)|^4197 ≤ (8329319300119/25000000000000 : ℝ)^3173
        have hw : |(68069167/156250000 : ℝ)|=(68069167/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264506509/625000000 : ℝ)|^4197 ≤ (3206546183329/10000000000000 : ℝ)^3173
        have hw : |(264506509/625000000 : ℝ)|=(264506509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242166309/5000000000 : ℝ)|^4197 ≤ (34617260949311/100000000000000 : ℝ)^3173
        have hw : |(2242166309/5000000000 : ℝ)|=(2242166309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_4 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138989859/10000000000 : ℝ)*x 0 + (164592243/312500000 : ℝ)*x 1 + (1347912179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138989859/10000000000 : ℝ)^4197 ≤ (130032434261/1000000000000 : ℝ)^3173 := by
    have hnat : (2138989859 : ℕ)^4197*1000000000000^3173 ≤ 130032434261^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138989859 10000000000 130032434261 1000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164592243/312500000 : ℝ)^4197 ≤ (21412636711527/50000000000000 : ℝ)^3173 := by
    have hnat : (164592243 : ℕ)^4197*50000000000000^3173 ≤ 21412636711527^3173*312500000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164592243 312500000 21412636711527 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347912179/2500000000 : ℝ)^4197 ≤ (11042870782641/25000000000000 : ℝ)^3173 := by
    have hnat : (1347912179 : ℕ)^4197*25000000000000^3173 ≤ 11042870782641^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347912179 2500000000 11042870782641 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138989859/10000000000 : ℝ), (164592243/312500000 : ℝ), (1347912179/2500000000 : ℝ)] ![(130032434261/1000000000000 : ℝ), (21412636711527/50000000000000 : ℝ), (11042870782641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138989859/10000000000 : ℝ)|^4197 ≤ (130032434261/1000000000000 : ℝ)^3173
        have hw : |(-2138989859/10000000000 : ℝ)|=(2138989859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164592243/312500000 : ℝ)|^4197 ≤ (21412636711527/50000000000000 : ℝ)^3173
        have hw : |(164592243/312500000 : ℝ)|=(164592243/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347912179/2500000000 : ℝ)|^4197 ≤ (11042870782641/25000000000000 : ℝ)^3173
        have hw : |(1347912179/2500000000 : ℝ)|=(1347912179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_5 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312626347/10000000000 : ℝ)*x 0 + (-2077527167/10000000000 : ℝ)*x 1 + (1347912219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312626347/10000000000 : ℝ)^4197 ≤ (1082929716701/2500000000000 : ℝ)^3173 := by
    have hnat : (5312626347 : ℕ)^4197*2500000000000^3173 ≤ 1082929716701^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312626347 10000000000 1082929716701 2500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077527167/10000000000 : ℝ)^4197 ≤ (2502265289883/20000000000000 : ℝ)^3173 := by
    have hnat : (2077527167 : ℕ)^4197*20000000000000^3173 ≤ 2502265289883^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077527167 10000000000 2502265289883 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347912219/2500000000 : ℝ)^4197 ≤ (8834296972881/20000000000000 : ℝ)^3173 := by
    have hnat : (1347912219 : ℕ)^4197*20000000000000^3173 ≤ 8834296972881^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347912219 2500000000 8834296972881 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312626347/10000000000 : ℝ), (-2077527167/10000000000 : ℝ), (1347912219/2500000000 : ℝ)] ![(1082929716701/2500000000000 : ℝ), (2502265289883/20000000000000 : ℝ), (8834296972881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312626347/10000000000 : ℝ)|^4197 ≤ (1082929716701/2500000000000 : ℝ)^3173
        have hw : |(5312626347/10000000000 : ℝ)|=(5312626347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2077527167/10000000000 : ℝ)|^4197 ≤ (2502265289883/20000000000000 : ℝ)^3173
        have hw : |(-2077527167/10000000000 : ℝ)|=(2077527167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347912219/2500000000 : ℝ)|^4197 ≤ (8834296972881/20000000000000 : ℝ)^3173
        have hw : |(1347912219/2500000000 : ℝ)|=(1347912219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_6 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656313079/5000000000 : ℝ)*x 0 + (269582451/500000000 : ℝ)*x 1 + (-2077527227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656313079/5000000000 : ℝ)^4197 ≤ (10829296657419/25000000000000 : ℝ)^3173 := by
    have hnat : (2656313079 : ℕ)^4197*25000000000000^3173 ≤ 10829296657419^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656313079 5000000000 10829296657419 25000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269582451/500000000 : ℝ)^4197 ≤ (22085743212431/50000000000000 : ℝ)^3173 := by
    have hnat : (269582451 : ℕ)^4197*50000000000000^3173 ≤ 22085743212431^3173*500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269582451 500000000 22085743212431 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2077527227/10000000000 : ℝ)^4197 ≤ (6255663463679/50000000000000 : ℝ)^3173 := by
    have hnat : (2077527227 : ℕ)^4197*50000000000000^3173 ≤ 6255663463679^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077527227 10000000000 6255663463679 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656313079/5000000000 : ℝ), (269582451/500000000 : ℝ), (-2077527227/10000000000 : ℝ)] ![(10829296657419/25000000000000 : ℝ), (22085743212431/50000000000000 : ℝ), (6255663463679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656313079/5000000000 : ℝ)|^4197 ≤ (10829296657419/25000000000000 : ℝ)^3173
        have hw : |(2656313079/5000000000 : ℝ)|=(2656313079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269582451/500000000 : ℝ)|^4197 ≤ (22085743212431/50000000000000 : ℝ)^3173
        have hw : |(269582451/500000000 : ℝ)|=(269582451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2077527227/10000000000 : ℝ)|^4197 ≤ (6255663463679/50000000000000 : ℝ)^3173
        have hw : |(-2077527227/10000000000 : ℝ)|=(2077527227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s7_7 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178218187/5000000000 : ℝ)*x 0 + (1120924339/2500000000 : ℝ)*x 1 + (211637079/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178218187/5000000000 : ℝ)^4197 ≤ (333173751839/1000000000000 : ℝ)^3173 := by
    have hnat : (2178218187 : ℕ)^4197*1000000000000^3173 ≤ 333173751839^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178218187 5000000000 333173751839 1000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120924339/2500000000 : ℝ)^4197 ≤ (17305387252227/50000000000000 : ℝ)^3173 := by
    have hnat : (1120924339 : ℕ)^4197*50000000000000^3173 ≤ 17305387252227^3173*2500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120924339 2500000000 17305387252227 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211637079/500000000 : ℝ)^4197 ≤ (32071850308177/100000000000000 : ℝ)^3173 := by
    have hnat : (211637079 : ℕ)^4197*100000000000000^3173 ≤ 32071850308177^3173*500000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211637079 500000000 32071850308177 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178218187/5000000000 : ℝ), (1120924339/2500000000 : ℝ), (211637079/500000000 : ℝ)] ![(333173751839/1000000000000 : ℝ), (17305387252227/50000000000000 : ℝ), (32071850308177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178218187/5000000000 : ℝ)|^4197 ≤ (333173751839/1000000000000 : ℝ)^3173
        have hw : |(2178218187/5000000000 : ℝ)|=(2178218187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120924339/2500000000 : ℝ)|^4197 ≤ (17305387252227/50000000000000 : ℝ)^3173
        have hw : |(1120924339/2500000000 : ℝ)|=(1120924339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(211637079/500000000 : ℝ)|^4197 ≤ (32071850308177/100000000000000 : ℝ)^3173
        have hw : |(211637079/500000000 : ℝ)|=(211637079/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1201_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2857/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11423/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11423/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11423/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11423/100000 : ℝ) ^ (8393/2048 : ℝ) ≤ (13760904608225547/100000000000000000000 : ℝ) := by
    have hpowers : (11423/100000 : ℝ)^8393 ≤ (13760904608225547/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11423 : ℕ)^8393*100000000000000000000^2048 ≤ 13760904608225547^2048*100000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11423 100000 13760904608225547 100000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11423/100000 : ℝ)) (X := (13760904608225547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (8393/2048 : ℝ) ≤ (32498370799521993/100000000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^8393 ≤ (32498370799521993/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1761 : ℕ)^8393*100000000000000000000^2048 ≤ 32498370799521993^2048*12500^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 32498370799521993 100000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (32498370799521993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013760904608225547/50000000000000000000 : ℝ) ≤ (1250083937213401/1250000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (50013760904608225547/50000000000000000000 : ℝ)^2048 ≤ (1250083937213401/1250000000000000 : ℝ)^8393 := by
      have hnat : (50013760904608225547 : ℕ)^2048*1250000000000000^8393 ≤ 1250083937213401^8393*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013760904608225547 50000000000000000000 1250083937213401 1250000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250083937213401/1250000000000000 : ℝ)) (X := (50013760904608225547/50000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002312963770387377/5000000000000000000 : ℝ) ≤ (1000112858852299/1000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (5002312963770387377/5000000000000000000 : ℝ)^2048 ≤ (1000112858852299/1000000000000000 : ℝ)^8393 := by
      have hnat : (5002312963770387377 : ℕ)^2048*1000000000000000^8393 ≤ 1000112858852299^8393*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002312963770387377 5000000000000000000 1000112858852299 1000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000112858852299/1000000000000000 : ℝ)) (X := (5002312963770387377/5000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032498370799521993/50000000000000000000 : ℝ) ≤ (2500396419834693/2500000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (50032498370799521993/50000000000000000000 : ℝ)^2048 ≤ (2500396419834693/2500000000000000 : ℝ)^8393 := by
      have hnat : (50032498370799521993 : ℕ)^2048*2500000000000000^8393 ≤ 2500396419834693^8393*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032498370799521993 50000000000000000000 2500396419834693 2500000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500396419834693/2500000000000000 : ℝ)) (X := (50032498370799521993/50000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13760904608225547/100000000000000000000 : ℝ) ≤ ((6660336711153088437/6662500000000000000 : ℝ)+2*(228545407891/133250000000000 : ℝ)*(11423/100000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (6660336711153088437/6662500000000000000 : ℝ)+2*(228545407891/133250000000000 : ℝ)*(11423/100000 : ℝ)=(1250083937213401/1250000000000000 : ℝ) by norm_num, show 1+2*(13760904608225547/100000000000000000000 : ℝ)=(50013760904608225547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32498370799521993/100000000000000000000 : ℝ)+(13760904608225547/100000000000000000000 : ℝ) ≤ ((6660336711153088437/6662500000000000000 : ℝ)+(228545407891/133250000000000 : ℝ)*((1761/12500 : ℝ)+(11423/100000 : ℝ)))^(8393/2048 : ℝ) := by
    rw [show (6660336711153088437/6662500000000000000 : ℝ)+(228545407891/133250000000000 : ℝ)*((1761/12500 : ℝ)+(11423/100000 : ℝ))=(1000112858852299/1000000000000000 : ℝ) by norm_num, show 1+(32498370799521993/100000000000000000000 : ℝ)+(13760904608225547/100000000000000000000 : ℝ)=(5002312963770387377/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32498370799521993/100000000000000000000 : ℝ) ≤ ((6660336711153088437/6662500000000000000 : ℝ)+2*(228545407891/133250000000000 : ℝ)*(1761/12500 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (6660336711153088437/6662500000000000000 : ℝ)+2*(228545407891/133250000000000 : ℝ)*(1761/12500 : ℝ)=(2500396419834693/2500000000000000 : ℝ) by norm_num, show 1+2*(32498370799521993/100000000000000000000 : ℝ)=(50032498370799521993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6660336711153088437/6662500000000000000 : ℝ)*(X 1 0+X 2 0)+(228545407891/133250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (6660336711153088437/6662500000000000000 : ℝ)) (alpha := (228545407891/133250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6660336711153088437/6662500000000000000 : ℝ)*(X 0 1+X 2 1)+(228545407891/133250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (6660336711153088437/6662500000000000000 : ℝ)) (alpha := (228545407891/133250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6660336711153088437/6662500000000000000 : ℝ)*(X 0 2+X 1 2)+(228545407891/133250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (11423/100000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (6660336711153088437/6662500000000000000 : ℝ)) (alpha := (228545407891/133250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069492477/5000000000 : ℝ)*X 0 0+(539196561/1000000000 : ℝ)*X 0 1+(5266636141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344514577/10000000000 : ℝ)*X 1 0+(-55063499/250000000 : ℝ)*X 1 1+(5266636141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344514577/10000000000 : ℝ)*X 2 0+(5266636141/10000000000 : ℝ)*X 2 1+(-55063499/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68069167/156250000 : ℝ)*X 0 0+(264506509/625000000 : ℝ)*X 0 1+(2242166309/5000000000 : ℝ)*X 0 2+(68069167/156250000 : ℝ)*X 1 0+(264506509/625000000 : ℝ)*X 1 1+(2242166309/5000000000 : ℝ)*X 1 2+(68069167/156250000 : ℝ)*X 2 0+(264506509/625000000 : ℝ)*X 2 1+(2242166309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2138989859/10000000000 : ℝ)*X 0 0+(164592243/312500000 : ℝ)*X 0 1+(1347912179/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312626347/10000000000 : ℝ)*X 1 0+(-2077527167/10000000000 : ℝ)*X 1 1+(1347912219/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656313079/5000000000 : ℝ)*X 2 0+(269582451/500000000 : ℝ)*X 2 1+(-2077527227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178218187/5000000000 : ℝ)*X 0 0+(1120924339/2500000000 : ℝ)*X 0 1+(211637079/500000000 : ℝ)*X 0 2+(2178218187/5000000000 : ℝ)*X 1 0+(1120924339/2500000000 : ℝ)*X 1 1+(211637079/500000000 : ℝ)*X 1 2+(2178218187/5000000000 : ℝ)*X 2 0+(1120924339/2500000000 : ℝ)*X 2 1+(211637079/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3634617044159489791254213/625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (284863287/25000000000000 : ℝ)*(base19) + (1060515957/100000000000000 : ℝ)*(base23) + (8437619/20000000000000 : ℝ)*(lower2) + (146975979/100000000000000 : ℝ)*(upper3) + (88857287/100000000000000 : ℝ)*(upper5) + (2985931337154719/50000000000000 : ℝ)*(major0) + (2985931337154719/50000000000000 : ℝ)*(major1) + (5971862674309439/100000000000000 : ℝ)*(major2) + (7979002299358393/100000000000000 : ℝ)*(sp0) + (7979032546240147/100000000000000 : ℝ)*(sp1) + (3989516312588669/50000000000000 : ℝ)*(sp2) + (991168650896157/25000000000000 : ℝ)*(sp3) + (15693167451/50000000000000 : ℝ)*(sp4) + (16865494701/100000000000000 : ℝ)*(sp7) + (3964691469079329/100000000000000 : ℝ)*(f.failure) + (1595806737138659/20000000000000 : ℝ)*(f.sum) + (107315337622557/13325000000000000000000000000 : ℝ)*base65 + (2613114451968859203/333125000000000000000000000000000 : ℝ)*base67 + (2360806131612493157/666250000000000000000000000000000 : ℝ)*base70 + (2264176212424484203/333125000000000000000000000000000 : ℝ)*base71 + (19298297742307/13325000000000000000000000000 : ℝ)*base73 + (11592089958994993157/666250000000000000000000000000000 : ℝ)*base76 + (3726772047354665797/333125000000000000000000000000000 : ℝ)*base78 + (10885634753983415797/333125000000000000000000000000000 : ℝ)*base80 + (2999643669201/832812500000000000000000000 : ℝ)*base81 + (34740989/2500000000000000000000 : ℝ)*base89 + (34740989/2500000000000000000000 : ℝ)*base91 + (9740989/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2354096613990549769734201507/333125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (868274273/50000000000000 : ℝ)*(base19) + (23284381/1562500000000 : ℝ)*(base23) + (11387711/50000000000000 : ℝ)*(upper2) + (280905369/100000000000000 : ℝ)*(upper3) + (182891311/100000000000000 : ℝ)*(upper5) + (6002100321435037/100000000000000 : ℝ)*(major0) + (6002100321435037/100000000000000 : ℝ)*(major1) + (6002100321435037/100000000000000 : ℝ)*(major2) + (51808171647/100000000000000 : ℝ)*(sp1) + (12788606199/25000000000000 : ℝ)*(sp2) + (400971715344659/5000000000000 : ℝ)*(sp4) + (4009690381086493/50000000000000 : ℝ)*(sp5) + (2004845415567/25000000000 : ℝ)*(sp6) + (1992383050210001/50000000000000 : ℝ)*(sp7) + (1992383050210001/50000000000000 : ℝ)*(f.failure) + (400971715344659/5000000000000 : ℝ)*(f.sum) + (25781906536667/6662500000000000000000000000 : ℝ)*base65 + (2112626665410282831/666250000000000000000000000000000 : ℝ)*base68 + (5010172998390282831/666250000000000000000000000000000 : ℝ)*base70 + (6978080877763467169/666250000000000000000000000000000 : ℝ)*base71 + (1960421490829/3331250000000000000000000000 : ℝ)*base74 + (8081586219939032831/666250000000000000000000000000000 : ℝ)*base76 + (8861080046609717169/666250000000000000000000000000000 : ℝ)*base77 + (3721103775845282831/666250000000000000000000000000000 : ℝ)*base80 + (26050397160533/6662500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1233459/1250000000000000000000 : ℝ)*base90 + (1233459/1250000000000000000000 : ℝ)*base92 + (1233459/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1201_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1201_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1201_s8_0 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138988641/10000000000 : ℝ)*x 0 + (2695958963/5000000000 : ℝ)*x 1 + (658335179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138988641/10000000000 : ℝ)^4197 ≤ (6501616816061/50000000000000 : ℝ)^3173 := by
    have hnat : (2138988641 : ℕ)^4197*50000000000000^3173 ≤ 6501616816061^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138988641 10000000000 6501616816061 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695958963/5000000000 : ℝ)^4197 ≤ (5521800056243/12500000000000 : ℝ)^3173 := by
    have hnat : (2695958963 : ℕ)^4197*12500000000000^3173 ≤ 5521800056243^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695958963 5000000000 5521800056243 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658335179/1250000000 : ℝ)^4197 ≤ (42822365902203/100000000000000 : ℝ)^3173 := by
    have hnat : (658335179 : ℕ)^4197*100000000000000^3173 ≤ 42822365902203^3173*1250000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658335179 1250000000 42822365902203 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138988641/10000000000 : ℝ), (2695958963/5000000000 : ℝ), (658335179/1250000000 : ℝ)] ![(6501616816061/50000000000000 : ℝ), (5521800056243/12500000000000 : ℝ), (42822365902203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138988641/10000000000 : ℝ)|^4197 ≤ (6501616816061/50000000000000 : ℝ)^3173
        have hw : |(-2138988641/10000000000 : ℝ)|=(2138988641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695958963/5000000000 : ℝ)|^4197 ≤ (5521800056243/12500000000000 : ℝ)^3173
        have hw : |(2695958963/5000000000 : ℝ)|=(2695958963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658335179/1250000000 : ℝ)|^4197 ≤ (42822365902203/100000000000000 : ℝ)^3173
        have hw : |(658335179/1250000000 : ℝ)|=(658335179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_1 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344502567/10000000000 : ℝ)*x 0 + (-2202495123/10000000000 : ℝ)*x 1 + (105333641/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344502567/10000000000 : ℝ)^4197 ≤ (8732261178141/20000000000000 : ℝ)^3173 := by
    have hnat : (5344502567 : ℕ)^4197*20000000000000^3173 ≤ 8732261178141^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344502567 10000000000 8732261178141 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2202495123/10000000000 : ℝ)^4197 ≤ (13516321548669/100000000000000 : ℝ)^3173 := by
    have hnat : (2202495123 : ℕ)^4197*100000000000000^3173 ≤ 13516321548669^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202495123 10000000000 13516321548669 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105333641/200000000 : ℝ)^4197 ≤ (669099571073/1562500000000 : ℝ)^3173 := by
    have hnat : (105333641 : ℕ)^4197*1562500000000^3173 ≤ 669099571073^3173*200000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105333641 200000000 669099571073 1562500000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344502567/10000000000 : ℝ), (-2202495123/10000000000 : ℝ), (105333641/200000000 : ℝ)] ![(8732261178141/20000000000000 : ℝ), (13516321548669/100000000000000 : ℝ), (669099571073/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344502567/10000000000 : ℝ)|^4197 ≤ (8732261178141/20000000000000 : ℝ)^3173
        have hw : |(5344502567/10000000000 : ℝ)|=(5344502567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2202495123/10000000000 : ℝ)|^4197 ≤ (13516321548669/100000000000000 : ℝ)^3173
        have hw : |(-2202495123/10000000000 : ℝ)|=(2202495123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105333641/200000000 : ℝ)|^4197 ≤ (669099571073/1562500000000 : ℝ)^3173
        have hw : |(105333641/200000000 : ℝ)|=(105333641/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_2 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21378011/40000000 : ℝ)*x 0 + (2633340847/5000000000 : ℝ)*x 1 + (-2202495351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21378011/40000000 : ℝ)^4197 ≤ (43661307868173/100000000000000 : ℝ)^3173 := by
    have hnat : (21378011 : ℕ)^4197*100000000000000^3173 ≤ 43661307868173^3173*40000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21378011 40000000 43661307868173 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633340847/5000000000 : ℝ)^4197 ≤ (21411184359981/50000000000000 : ℝ)^3173 := by
    have hnat : (2633340847 : ℕ)^4197*50000000000000^3173 ≤ 21411184359981^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633340847 5000000000 21411184359981 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202495351/10000000000 : ℝ)^4197 ≤ (13516323399417/100000000000000 : ℝ)^3173 := by
    have hnat : (2202495351 : ℕ)^4197*100000000000000^3173 ≤ 13516323399417^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202495351 10000000000 13516323399417 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21378011/40000000 : ℝ), (2633340847/5000000000 : ℝ), (-2202495351/10000000000 : ℝ)] ![(43661307868173/100000000000000 : ℝ), (21411184359981/50000000000000 : ℝ), (13516323399417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21378011/40000000 : ℝ)|^4197 ≤ (43661307868173/100000000000000 : ℝ)^3173
        have hw : |(21378011/40000000 : ℝ)|=(21378011/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633340847/5000000000 : ℝ)|^4197 ≤ (21411184359981/50000000000000 : ℝ)^3173
        have hw : |(2633340847/5000000000 : ℝ)|=(2633340847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2202495351/10000000000 : ℝ)|^4197 ≤ (13516323399417/100000000000000 : ℝ)^3173
        have hw : |(-2202495351/10000000000 : ℝ)|=(2202495351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_3 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2178214711/5000000000 : ℝ)*x 0 + (846439557/2000000000 : ℝ)*x 1 + (2242119001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178214711/5000000000 : ℝ)^4197 ≤ (3331730485757/10000000000000 : ℝ)^3173 := by
    have hnat : (2178214711 : ℕ)^4197*10000000000000^3173 ≤ 3331730485757^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178214711 5000000000 3331730485757 10000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846439557/2000000000 : ℝ)^4197 ≤ (16033200148673/50000000000000 : ℝ)^3173 := by
    have hnat : (846439557 : ℕ)^4197*50000000000000^3173 ≤ 16033200148673^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846439557 2000000000 16033200148673 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242119001/5000000000 : ℝ)^4197 ≤ (276930358709/800000000000 : ℝ)^3173 := by
    have hnat : (2242119001 : ℕ)^4197*800000000000^3173 ≤ 276930358709^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242119001 5000000000 276930358709 800000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178214711/5000000000 : ℝ), (846439557/2000000000 : ℝ), (2242119001/5000000000 : ℝ)] ![(3331730485757/10000000000000 : ℝ), (16033200148673/50000000000000 : ℝ), (276930358709/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178214711/5000000000 : ℝ)|^4197 ≤ (3331730485757/10000000000000 : ℝ)^3173
        have hw : |(2178214711/5000000000 : ℝ)|=(2178214711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846439557/2000000000 : ℝ)|^4197 ≤ (16033200148673/50000000000000 : ℝ)^3173
        have hw : |(846439557/2000000000 : ℝ)|=(846439557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242119001/5000000000 : ℝ)|^4197 ≤ (276930358709/800000000000 : ℝ)^3173
        have hw : |(2242119001/5000000000 : ℝ)|=(2242119001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_4 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069496559/5000000000 : ℝ)*x 0 + (2633498463/5000000000 : ℝ)*x 1 + (336975093/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069496559/5000000000 : ℝ)^4197 ≤ (6501634815917/50000000000000 : ℝ)^3173 := by
    have hnat : (1069496559 : ℕ)^4197*50000000000000^3173 ≤ 6501634815917^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069496559 5000000000 6501634815917 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633498463/5000000000 : ℝ)^4197 ≤ (5353219876397/12500000000000 : ℝ)^3173 := by
    have hnat : (2633498463 : ℕ)^4197*12500000000000^3173 ≤ 5353219876397^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633498463 5000000000 5353219876397 12500000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336975093/625000000 : ℝ)^4197 ≤ (8834194268953/20000000000000 : ℝ)^3173 := by
    have hnat : (336975093 : ℕ)^4197*20000000000000^3173 ≤ 8834194268953^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336975093 625000000 8834194268953 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069496559/5000000000 : ℝ), (2633498463/5000000000 : ℝ), (336975093/625000000 : ℝ)] ![(6501634815917/50000000000000 : ℝ), (5353219876397/12500000000000 : ℝ), (8834194268953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069496559/5000000000 : ℝ)|^4197 ≤ (6501634815917/50000000000000 : ℝ)^3173
        have hw : |(-1069496559/5000000000 : ℝ)|=(1069496559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633498463/5000000000 : ℝ)|^4197 ≤ (5353219876397/12500000000000 : ℝ)^3173
        have hw : |(2633498463/5000000000 : ℝ)|=(2633498463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336975093/625000000 : ℝ)|^4197 ≤ (8834194268953/20000000000000 : ℝ)^3173
        have hw : |(336975093/625000000 : ℝ)|=(336975093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_5 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312638179/10000000000 : ℝ)*x 0 + (-415515123/2000000000 : ℝ)*x 1 + (336975093/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312638179/10000000000 : ℝ)^4197 ≤ (43317316276129/100000000000000 : ℝ)^3173 := by
    have hnat : (5312638179 : ℕ)^4197*100000000000000^3173 ≤ 43317316276129^3173*10000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312638179 10000000000 43317316276129 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415515123/2000000000 : ℝ)^4197 ≤ (6255856187259/50000000000000 : ℝ)^3173 := by
    have hnat : (415515123 : ℕ)^4197*50000000000000^3173 ≤ 6255856187259^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415515123 2000000000 6255856187259 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336975093/625000000 : ℝ)^4197 ≤ (8834194268953/20000000000000 : ℝ)^3173 := by
    have hnat : (336975093 : ℕ)^4197*20000000000000^3173 ≤ 8834194268953^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336975093 625000000 8834194268953 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312638179/10000000000 : ℝ), (-415515123/2000000000 : ℝ), (336975093/625000000 : ℝ)] ![(43317316276129/100000000000000 : ℝ), (6255856187259/50000000000000 : ℝ), (8834194268953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312638179/10000000000 : ℝ)|^4197 ≤ (43317316276129/100000000000000 : ℝ)^3173
        have hw : |(5312638179/10000000000 : ℝ)|=(5312638179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415515123/2000000000 : ℝ)|^4197 ≤ (6255856187259/50000000000000 : ℝ)^3173
        have hw : |(-415515123/2000000000 : ℝ)|=(415515123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336975093/625000000 : ℝ)|^4197 ≤ (8834194268953/20000000000000 : ℝ)^3173
        have hw : |(336975093/625000000 : ℝ)|=(336975093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_6 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656319089/5000000000 : ℝ)*x 0 + (336975093/625000000 : ℝ)*x 1 + (-415515123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656319089/5000000000 : ℝ)^4197 ≤ (338416533323/781250000000 : ℝ)^3173 := by
    have hnat : (2656319089 : ℕ)^4197*781250000000^3173 ≤ 338416533323^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656319089 5000000000 338416533323 781250000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336975093/625000000 : ℝ)^4197 ≤ (8834194268953/20000000000000 : ℝ)^3173 := by
    have hnat : (336975093 : ℕ)^4197*20000000000000^3173 ≤ 8834194268953^3173*625000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336975093 625000000 8834194268953 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (415515123/2000000000 : ℝ)^4197 ≤ (6255856187259/50000000000000 : ℝ)^3173 := by
    have hnat : (415515123 : ℕ)^4197*50000000000000^3173 ≤ 6255856187259^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415515123 2000000000 6255856187259 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656319089/5000000000 : ℝ), (336975093/625000000 : ℝ), (-415515123/2000000000 : ℝ)] ![(338416533323/781250000000 : ℝ), (8834194268953/20000000000000 : ℝ), (6255856187259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656319089/5000000000 : ℝ)|^4197 ≤ (338416533323/781250000000 : ℝ)^3173
        have hw : |(2656319089/5000000000 : ℝ)|=(2656319089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336975093/625000000 : ℝ)|^4197 ≤ (8834194268953/20000000000000 : ℝ)^3173
        have hw : |(336975093/625000000 : ℝ)|=(336975093/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-415515123/2000000000 : ℝ)|^4197 ≤ (6255856187259/50000000000000 : ℝ)^3173
        have hw : |(-415515123/2000000000 : ℝ)|=(415515123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1201_s8_7 (p : ℝ) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435643859/1000000000 : ℝ)*x 0 + (896720803/2000000000 : ℝ)*x 1 + (2116417217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435643859/1000000000 : ℝ)^4197 ≤ (33317397600931/100000000000000 : ℝ)^3173 := by
    have hnat : (435643859 : ℕ)^4197*100000000000000^3173 ≤ 33317397600931^3173*1000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435643859 1000000000 33317397600931 100000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896720803/2000000000 : ℝ)^4197 ≤ (6921964291229/20000000000000 : ℝ)^3173 := by
    have hnat : (896720803 : ℕ)^4197*20000000000000^3173 ≤ 6921964291229^3173*2000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896720803 2000000000 6921964291229 20000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116417217/5000000000 : ℝ)^4197 ≤ (16036390465087/50000000000000 : ℝ)^3173 := by
    have hnat : (2116417217 : ℕ)^4197*50000000000000^3173 ≤ 16036390465087^3173*5000000000^4197 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116417217 5000000000 16036390465087 50000000000000 4197 3173 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4197/1024 : ℝ)) 4197 3173 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435643859/1000000000 : ℝ), (896720803/2000000000 : ℝ), (2116417217/5000000000 : ℝ)] ![(33317397600931/100000000000000 : ℝ), (6921964291229/20000000000000 : ℝ), (16036390465087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435643859/1000000000 : ℝ)|^4197 ≤ (33317397600931/100000000000000 : ℝ)^3173
        have hw : |(435643859/1000000000 : ℝ)|=(435643859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896720803/2000000000 : ℝ)|^4197 ≤ (6921964291229/20000000000000 : ℝ)^3173
        have hw : |(896720803/2000000000 : ℝ)|=(896720803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116417217/5000000000 : ℝ)|^4197 ≤ (16036390465087/50000000000000 : ℝ)^3173
        have hw : |(2116417217/5000000000 : ℝ)|=(2116417217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1201_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11429/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2857/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2857/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2857/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2857/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2857/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2857/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2857/25000 : ℝ) ^ (8393/2048 : ℝ) ≤ (2757121167265749/20000000000000000000 : ℝ) := by
    have hpowers : (2857/25000 : ℝ)^8393 ≤ (2757121167265749/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2857 : ℕ)^8393*20000000000000000000^2048 ≤ 2757121167265749^2048*25000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2857 25000 2757121167265749 20000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2857/25000 : ℝ)) (X := (2757121167265749/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (8393/2048 : ℝ) ≤ (16225564265319429/50000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^8393 ≤ (16225564265319429/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14083 : ℕ)^8393*50000000000000000000^2048 ≤ 16225564265319429^2048*100000^8393 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 16225564265319429 50000000000000000000 8393 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (16225564265319429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002757121167265749/10000000000000000000 : ℝ) ≤ (10000672702939731/10000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (10002757121167265749/10000000000000000000 : ℝ)^2048 ≤ (10000672702939731/10000000000000000 : ℝ)^8393 := by
      have hnat : (10002757121167265749 : ℕ)^2048*10000000000000000^8393 ≤ 10000672702939731^8393*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002757121167265749 10000000000000000000 10000672702939731 10000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000672702939731/10000000000000000 : ℝ)) (X := (10002757121167265749/10000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046236734366967603/100000000000000000000 : ℝ) ≤ (5000564019342409/5000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (100046236734366967603/100000000000000000000 : ℝ)^2048 ≤ (5000564019342409/5000000000000000 : ℝ)^8393 := by
      have hnat : (100046236734366967603 : ℕ)^2048*5000000000000000^8393 ≤ 5000564019342409^8393*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046236734366967603 100000000000000000000 5000564019342409 5000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000564019342409/5000000000000000 : ℝ)) (X := (100046236734366967603/100000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016225564265319429/25000000000000000000 : ℝ) ≤ (2000316674885981/2000000000000000 : ℝ) ^ (8393/2048 : ℝ) := by
    have hpowers : (25016225564265319429/25000000000000000000 : ℝ)^2048 ≤ (2000316674885981/2000000000000000 : ℝ)^8393 := by
      have hnat : (25016225564265319429 : ℕ)^2048*2000000000000000^8393 ≤ 2000316674885981^8393*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016225564265319429 25000000000000000000 2000316674885981 2000000000000000 2048 8393 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000316674885981/2000000000000000 : ℝ)) (X := (25016225564265319429/25000000000000000000 : ℝ)) (by norm_num) 8393 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2757121167265749/20000000000000000000 : ℝ) ≤ ((26541378872515277333/26550000000000000000 : ℝ)+2*(455335745087/265500000000000 : ℝ)*(2857/25000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (26541378872515277333/26550000000000000000 : ℝ)+2*(455335745087/265500000000000 : ℝ)*(2857/25000 : ℝ)=(10000672702939731/10000000000000000 : ℝ) by norm_num, show 1+2*(2757121167265749/20000000000000000000 : ℝ)=(10002757121167265749/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16225564265319429/50000000000000000000 : ℝ)+(2757121167265749/20000000000000000000 : ℝ) ≤ ((26541378872515277333/26550000000000000000 : ℝ)+(455335745087/265500000000000 : ℝ)*((14083/100000 : ℝ)+(2857/25000 : ℝ)))^(8393/2048 : ℝ) := by
    rw [show (26541378872515277333/26550000000000000000 : ℝ)+(455335745087/265500000000000 : ℝ)*((14083/100000 : ℝ)+(2857/25000 : ℝ))=(5000564019342409/5000000000000000 : ℝ) by norm_num, show 1+(16225564265319429/50000000000000000000 : ℝ)+(2757121167265749/20000000000000000000 : ℝ)=(100046236734366967603/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16225564265319429/50000000000000000000 : ℝ) ≤ ((26541378872515277333/26550000000000000000 : ℝ)+2*(455335745087/265500000000000 : ℝ)*(14083/100000 : ℝ))^(8393/2048 : ℝ) := by
    rw [show (26541378872515277333/26550000000000000000 : ℝ)+2*(455335745087/265500000000000 : ℝ)*(14083/100000 : ℝ)=(2000316674885981/2000000000000000 : ℝ) by norm_num, show 1+2*(16225564265319429/50000000000000000000 : ℝ)=(25016225564265319429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26541378872515277333/26550000000000000000 : ℝ)*(X 1 0+X 2 0)+(455335745087/265500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (2857/25000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (26541378872515277333/26550000000000000000 : ℝ)) (alpha := (455335745087/265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26541378872515277333/26550000000000000000 : ℝ)*(X 0 1+X 2 1)+(455335745087/265500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (2857/25000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (26541378872515277333/26550000000000000000 : ℝ)) (alpha := (455335745087/265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26541378872515277333/26550000000000000000 : ℝ)*(X 0 2+X 1 2)+(455335745087/265500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8393/2048 : ℝ)) (lo := (2857/25000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (26541378872515277333/26550000000000000000 : ℝ)) (alpha := (455335745087/265500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138988641/10000000000 : ℝ)*X 0 0+(2695958963/5000000000 : ℝ)*X 0 1+(658335179/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344502567/10000000000 : ℝ)*X 1 0+(-2202495123/10000000000 : ℝ)*X 1 1+(105333641/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21378011/40000000 : ℝ)*X 2 0+(2633340847/5000000000 : ℝ)*X 2 1+(-2202495351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178214711/5000000000 : ℝ)*X 0 0+(846439557/2000000000 : ℝ)*X 0 1+(2242119001/5000000000 : ℝ)*X 0 2+(2178214711/5000000000 : ℝ)*X 1 0+(846439557/2000000000 : ℝ)*X 1 1+(2242119001/5000000000 : ℝ)*X 1 2+(2178214711/5000000000 : ℝ)*X 2 0+(846439557/2000000000 : ℝ)*X 2 1+(2242119001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069496559/5000000000 : ℝ)*X 0 0+(2633498463/5000000000 : ℝ)*X 0 1+(336975093/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312638179/10000000000 : ℝ)*X 1 0+(-415515123/2000000000 : ℝ)*X 1 1+(336975093/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656319089/5000000000 : ℝ)*X 2 0+(336975093/625000000 : ℝ)*X 2 1+(-415515123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435643859/1000000000 : ℝ)*X 0 0+(896720803/2000000000 : ℝ)*X 0 1+(2116417217/5000000000 : ℝ)*X 0 2+(435643859/1000000000 : ℝ)*X 1 0+(896720803/2000000000 : ℝ)*X 1 1+(2116417217/5000000000 : ℝ)*X 1 2+(435643859/1000000000 : ℝ)*X 2 0+(896720803/2000000000 : ℝ)*X 2 1+(2116417217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1201_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (547522665358580020326444361/147500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1407545057/100000000000000 : ℝ)*(base19) + (20182163/1250000000000 : ℝ)*(base23) + (440882159/100000000000000 : ℝ)*(upper3) + (35479721/100000000000000 : ℝ)*(upper4) + (35531303/50000000000000 : ℝ)*(upper5) + (5976344854167249/100000000000000 : ℝ)*(major0) + (5976344854167249/100000000000000 : ℝ)*(major1) + (23905379416669/400000000000 : ℝ)*(major2) + (1996241218600833/25000000000000 : ℝ)*(sp0) + (998127626238043/12500000000000 : ℝ)*(sp1) + (199625520071909/2500000000000 : ℝ)*(sp2) + (1983819634581811/50000000000000 : ℝ)*(sp3) + (14385761517/25000000000000 : ℝ)*(sp4) + (2789798753/10000000000000 : ℝ)*(sp7) + (3967667167151153/100000000000000 : ℝ)*(f.failure) + (39925112087247/500000000000 : ℝ)*(f.sum) + (23500885732987/26550000000000000000000000000 : ℝ)*base66 + (66495094905975666917/2655000000000000000000000000000000 : ℝ)*base67 + (156706712639688977/10620000000000000000000000000000 : ℝ)*base69 + (24706473866115666917/2655000000000000000000000000000000 : ℝ)*base71 + (160717619500987/26550000000000000000000000000 : ℝ)*base74 + (10634162927351023/10620000000000000000000000000000 : ℝ)*base76 + (3797491458015655639/885000000000000000000000000000000 : ℝ)*base77 + (4895779357244344361/885000000000000000000000000000000 : ℝ)*base80 + (21437720285021/4425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (21141773/2500000000000000000000 : ℝ)*base89 + (21141773/2500000000000000000000 : ℝ)*base91 + (3858227/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (572075949285789420552934973/73750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (699290919/50000000000000 : ℝ)*(base19) + (1519820027/100000000000000 : ℝ)*(base23) + (489072227/100000000000000 : ℝ)*(lower1) + (77725013/50000000000000 : ℝ)*(upper3) + (56027169/100000000000000 : ℝ)*(lower4) + (158524653/100000000000000 : ℝ)*(upper5) + (3003263111111243/50000000000000 : ℝ)*(major0) + (3003263111111243/50000000000000 : ℝ)*(major1) + (3003263111111243/50000000000000 : ℝ)*(major2) + (180153433/6250000000000 : ℝ)*(sp2) + (401267387539857/5000000000000 : ℝ)*(sp4) + (8025346352215301/100000000000000 : ℝ)*(sp5) + (1605068669704437/20000000000000 : ℝ)*(sp6) + (1993852217541199/50000000000000 : ℝ)*(sp7) + (1993852217541199/50000000000000 : ℝ)*(f.failure) + (401267387539857/5000000000000 : ℝ)*(f.sum) + (29893489021891/6637500000000000000000000000 : ℝ)*base65 + (136459018681001545081/1327500000000000000000000000000000 : ℝ)*base68 + (10013723914743454919/1327500000000000000000000000000000 : ℝ)*base69 + (127791367739149045081/1327500000000000000000000000000000 : ℝ)*base72 + (58868775973843/13275000000000000000000000000 : ℝ)*base74 + (108570213128223454919/1327500000000000000000000000000000 : ℝ)*base75 + (8366087991851545081/1327500000000000000000000000000000 : ℝ)*base78 + (14189774115581545081/1327500000000000000000000000000000 : ℝ)*base80 + (55032186463693/13275000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (4332659/1250000000000000000000 : ℝ)*base89 + (4332659/1250000000000000000000 : ℝ)*base91 + (4332659/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1201_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1201_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1201_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1201_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1201_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1201_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8393/2048 : ℝ) ≤ p) (hpb : p ≤ (4197/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37656541/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11429/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1201_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

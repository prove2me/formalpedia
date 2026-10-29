-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1584_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:30:49.99007+00:00
-- url     : https://prove2.me/submissions/5a5894c1-87b5-4b3f-820c-a794b3656c23

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
theorem support_rectangle_w1584_s0_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403014947/2500000000 : ℝ)*x 0 + (1171900421/2000000000 : ℝ)*x 1 + (2442461551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403014947/2500000000 : ℝ)^4665 ≤ (1929718189023/20000000000000 : ℝ)^3641 := by
    have hnat : (403014947 : ℕ)^4665*20000000000000^3641 ≤ 1929718189023^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403014947 2500000000 1929718189023 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1171900421/2000000000 : ℝ)^4665 ≤ (3151037345261/6250000000000 : ℝ)^3641 := by
    have hnat : (1171900421 : ℕ)^4665*6250000000000^3641 ≤ 3151037345261^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171900421 2000000000 3151037345261 6250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2442461551/5000000000 : ℝ)^4665 ≤ (19967405755533/50000000000000 : ℝ)^3641 := by
    have hnat : (2442461551 : ℕ)^4665*50000000000000^3641 ≤ 19967405755533^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2442461551 5000000000 19967405755533 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403014947/2500000000 : ℝ), (1171900421/2000000000 : ℝ), (2442461551/5000000000 : ℝ)] ![(1929718189023/20000000000000 : ℝ), (3151037345261/6250000000000 : ℝ), (19967405755533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403014947/2500000000 : ℝ)|^4665 ≤ (1929718189023/20000000000000 : ℝ)^3641
        have hw : |(-403014947/2500000000 : ℝ)|=(403014947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1171900421/2000000000 : ℝ)|^4665 ≤ (3151037345261/6250000000000 : ℝ)^3641
        have hw : |(1171900421/2000000000 : ℝ)|=(1171900421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2442461551/5000000000 : ℝ)|^4665 ≤ (19967405755533/50000000000000 : ℝ)^3641
        have hw : |(2442461551/5000000000 : ℝ)|=(2442461551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136562501/250000000 : ℝ)*x 0 + (-430697163/2000000000 : ℝ)*x 1 + (1221230757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136562501/250000000 : ℝ)^4665 ≤ (4608239617453/10000000000000 : ℝ)^3641 := by
    have hnat : (136562501 : ℕ)^4665*10000000000000^3641 ≤ 4608239617453^3641*250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136562501 250000000 4608239617453 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430697163/2000000000 : ℝ)^4665 ≤ (13982793074597/100000000000000 : ℝ)^3641 := by
    have hnat : (430697163 : ℕ)^4665*100000000000000^3641 ≤ 13982793074597^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430697163 2000000000 13982793074597 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221230757/2500000000 : ℝ)^4665 ≤ (39934810735969/100000000000000 : ℝ)^3641 := by
    have hnat : (1221230757 : ℕ)^4665*100000000000000^3641 ≤ 39934810735969^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221230757 2500000000 39934810735969 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136562501/250000000 : ℝ), (-430697163/2000000000 : ℝ), (1221230757/2500000000 : ℝ)] ![(4608239617453/10000000000000 : ℝ), (13982793074597/100000000000000 : ℝ), (39934810735969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136562501/250000000 : ℝ)|^4665 ≤ (4608239617453/10000000000000 : ℝ)^3641
        have hw : |(136562501/250000000 : ℝ)|=(136562501/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430697163/2000000000 : ℝ)|^4665 ≤ (13982793074597/100000000000000 : ℝ)^3641
        have hw : |(-430697163/2000000000 : ℝ)|=(430697163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1221230757/2500000000 : ℝ)|^4665 ≤ (39934810735969/100000000000000 : ℝ)^3641
        have hw : |(1221230757/2500000000 : ℝ)|=(1221230757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5462500113/10000000000 : ℝ)*x 0 + (122123073/250000000 : ℝ)*x 1 + (-67296433/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5462500113/10000000000 : ℝ)^4665 ≤ (46082396963567/100000000000000 : ℝ)^3641 := by
    have hnat : (5462500113 : ℕ)^4665*100000000000000^3641 ≤ 46082396963567^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462500113 10000000000 46082396963567 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122123073/250000000 : ℝ)^4665 ≤ (4991851200593/12500000000000 : ℝ)^3641 := by
    have hnat : (122123073 : ℕ)^4665*12500000000000^3641 ≤ 4991851200593^3641*250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122123073 250000000 4991851200593 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67296433/312500000 : ℝ)^4665 ≤ (6991396707843/50000000000000 : ℝ)^3641 := by
    have hnat : (67296433 : ℕ)^4665*50000000000000^3641 ≤ 6991396707843^3641*312500000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67296433 312500000 6991396707843 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5462500113/10000000000 : ℝ), (122123073/250000000 : ℝ), (-67296433/312500000 : ℝ)] ![(46082396963567/100000000000000 : ℝ), (4991851200593/12500000000000 : ℝ), (6991396707843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5462500113/10000000000 : ℝ)|^4665 ≤ (46082396963567/100000000000000 : ℝ)^3641
        have hw : |(5462500113/10000000000 : ℝ)|=(5462500113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(122123073/250000000 : ℝ)|^4665 ≤ (4991851200593/12500000000000 : ℝ)^3641
        have hw : |(122123073/250000000 : ℝ)|=(122123073/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67296433/312500000 : ℝ)|^4665 ≤ (6991396707843/50000000000000 : ℝ)^3641
        have hw : |(-67296433/312500000 : ℝ)|=(67296433/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (825251201/2000000000 : ℝ)*x 0 + (1547006287/5000000000 : ℝ)*x 1 + (5416524049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825251201/2000000000 : ℝ)^4665 ≤ (32168783778241/100000000000000 : ℝ)^3641 := by
    have hnat : (825251201 : ℕ)^4665*100000000000000^3641 ≤ 32168783778241^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825251201 2000000000 32168783778241 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1547006287/5000000000 : ℝ)^4665 ≤ (695161644877/3125000000000 : ℝ)^3641 := by
    have hnat : (1547006287 : ℕ)^4665*3125000000000^3641 ≤ 695161644877^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1547006287 5000000000 695161644877 3125000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416524049/10000000000 : ℝ)^4665 ≤ (45586043563879/100000000000000 : ℝ)^3641 := by
    have hnat : (5416524049 : ℕ)^4665*100000000000000^3641 ≤ 45586043563879^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416524049 10000000000 45586043563879 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(825251201/2000000000 : ℝ), (1547006287/5000000000 : ℝ), (5416524049/10000000000 : ℝ)] ![(32168783778241/100000000000000 : ℝ), (695161644877/3125000000000 : ℝ), (45586043563879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(825251201/2000000000 : ℝ)|^4665 ≤ (32168783778241/100000000000000 : ℝ)^3641
        have hw : |(825251201/2000000000 : ℝ)|=(825251201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1547006287/5000000000 : ℝ)|^4665 ≤ (695161644877/3125000000000 : ℝ)^3641
        have hw : |(1547006287/5000000000 : ℝ)|=(1547006287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416524049/10000000000 : ℝ)|^4665 ≤ (45586043563879/100000000000000 : ℝ)^3641
        have hw : |(5416524049/10000000000 : ℝ)|=(5416524049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-807504993/5000000000 : ℝ)*x 0 + (4909405953/10000000000 : ℝ)*x 1 + (233366231/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807504993/5000000000 : ℝ)^4665 ≤ (1934244105969/20000000000000 : ℝ)^3641 := by
    have hnat : (807504993 : ℕ)^4665*20000000000000^3641 ≤ 1934244105969^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807504993 5000000000 1934244105969 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4909405953/10000000000 : ℝ)^4665 ≤ (40191432677023/100000000000000 : ℝ)^3641 := by
    have hnat : (4909405953 : ℕ)^4665*100000000000000^3641 ≤ 40191432677023^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4909405953 10000000000 40191432677023 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233366231/400000000 : ℝ)^4665 ≤ (50137346776289/100000000000000 : ℝ)^3641 := by
    have hnat : (233366231 : ℕ)^4665*100000000000000^3641 ≤ 50137346776289^3641*400000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233366231 400000000 50137346776289 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-807504993/5000000000 : ℝ), (4909405953/10000000000 : ℝ), (233366231/400000000 : ℝ)] ![(1934244105969/20000000000000 : ℝ), (40191432677023/100000000000000 : ℝ), (50137346776289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-807504993/5000000000 : ℝ)|^4665 ≤ (1934244105969/20000000000000 : ℝ)^3641
        have hw : |(-807504993/5000000000 : ℝ)|=(807504993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4909405953/10000000000 : ℝ)|^4665 ≤ (40191432677023/100000000000000 : ℝ)^3641
        have hw : |(4909405953/10000000000 : ℝ)|=(4909405953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(233366231/400000000 : ℝ)|^4665 ≤ (50137346776289/100000000000000 : ℝ)^3641
        have hw : |(233366231/400000000 : ℝ)|=(233366231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (81188443/156250000 : ℝ)*x 0 + (-24085053/200000000 : ℝ)*x 1 + (5834155859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81188443/156250000 : ℝ)^4665 ≤ (10805627714549/25000000000000 : ℝ)^3641 := by
    have hnat : (81188443 : ℕ)^4665*25000000000000^3641 ≤ 10805627714549^3641*156250000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81188443 156250000 10805627714549 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24085053/200000000 : ℝ)^4665 ≤ (1328028283187/20000000000000 : ℝ)^3641 := by
    have hnat : (24085053 : ℕ)^4665*20000000000000^3641 ≤ 1328028283187^3641*200000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24085053 200000000 1328028283187 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5834155859/10000000000 : ℝ)^4665 ≤ (50137347701187/100000000000000 : ℝ)^3641 := by
    have hnat : (5834155859 : ℕ)^4665*100000000000000^3641 ≤ 50137347701187^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5834155859 10000000000 50137347701187 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81188443/156250000 : ℝ), (-24085053/200000000 : ℝ), (5834155859/10000000000 : ℝ)] ![(10805627714549/25000000000000 : ℝ), (1328028283187/20000000000000 : ℝ), (50137347701187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81188443/156250000 : ℝ)|^4665 ≤ (10805627714549/25000000000000 : ℝ)^3641
        have hw : |(81188443/156250000 : ℝ)|=(81188443/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24085053/200000000 : ℝ)|^4665 ≤ (1328028283187/20000000000000 : ℝ)^3641
        have hw : |(-24085053/200000000 : ℝ)|=(24085053/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5834155859/10000000000 : ℝ)|^4665 ≤ (50137347701187/100000000000000 : ℝ)^3641
        have hw : |(5834155859/10000000000 : ℝ)|=(5834155859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196060313/10000000000 : ℝ)*x 0 + (1458538939/2500000000 : ℝ)*x 1 + (-150531609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196060313/10000000000 : ℝ)^4665 ≤ (43222510442543/100000000000000 : ℝ)^3641 := by
    have hnat : (5196060313 : ℕ)^4665*100000000000000^3641 ≤ 43222510442543^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196060313 10000000000 43222510442543 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1458538939/2500000000 : ℝ)^4665 ≤ (25068673283543/50000000000000 : ℝ)^3641 := by
    have hnat : (1458538939 : ℕ)^4665*50000000000000^3641 ≤ 25068673283543^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458538939 2500000000 25068673283543 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150531609/1250000000 : ℝ)^4665 ≤ (207504468259/3125000000000 : ℝ)^3641 := by
    have hnat : (150531609 : ℕ)^4665*3125000000000^3641 ≤ 207504468259^3641*1250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150531609 1250000000 207504468259 3125000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196060313/10000000000 : ℝ), (1458538939/2500000000 : ℝ), (-150531609/1250000000 : ℝ)] ![(43222510442543/100000000000000 : ℝ), (25068673283543/50000000000000 : ℝ), (207504468259/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196060313/10000000000 : ℝ)|^4665 ≤ (43222510442543/100000000000000 : ℝ)^3641
        have hw : |(5196060313/10000000000 : ℝ)|=(5196060313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1458538939/2500000000 : ℝ)|^4665 ≤ (25068673283543/50000000000000 : ℝ)^3641
        have hw : |(1458538939/2500000000 : ℝ)|=(1458538939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150531609/1250000000 : ℝ)|^4665 ≤ (207504468259/3125000000000 : ℝ)^3641
        have hw : |(-150531609/1250000000 : ℝ)|=(150531609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s0_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2066643519/5000000000 : ℝ)*x 0 + (107163581/200000000 : ℝ)*x 1 + (3154414889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066643519/5000000000 : ℝ)^4665 ≤ (1007469736103/3125000000000 : ℝ)^3641 := by
    have hnat : (2066643519 : ℕ)^4665*3125000000000^3641 ≤ 1007469736103^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066643519 5000000000 1007469736103 3125000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107163581/200000000 : ℝ)^4665 ≤ (44957861126821/100000000000000 : ℝ)^3641 := by
    have hnat : (107163581 : ℕ)^4665*100000000000000^3641 ≤ 44957861126821^3641*200000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107163581 200000000 44957861126821 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154414889/10000000000 : ℝ)^4665 ≤ (570077682819/2500000000000 : ℝ)^3641 := by
    have hnat : (3154414889 : ℕ)^4665*2500000000000^3641 ≤ 570077682819^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154414889 10000000000 570077682819 2500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066643519/5000000000 : ℝ), (107163581/200000000 : ℝ), (3154414889/10000000000 : ℝ)] ![(1007469736103/3125000000000 : ℝ), (44957861126821/100000000000000 : ℝ), (570077682819/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066643519/5000000000 : ℝ)|^4665 ≤ (1007469736103/3125000000000 : ℝ)^3641
        have hw : |(2066643519/5000000000 : ℝ)|=(2066643519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107163581/200000000 : ℝ)|^4665 ≤ (44957861126821/100000000000000 : ℝ)^3641
        have hw : |(107163581/200000000 : ℝ)|=(107163581/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154414889/10000000000 : ℝ)|^4665 ≤ (570077682819/2500000000000 : ℝ)^3641
        have hw : |(3154414889/10000000000 : ℝ)|=(3154414889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3709/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3073/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4663/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4663 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4663*1^1024 ≤ 0^1024*1^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4663/1024 : ℝ) ≤ (1541332124344162269/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4663 ≤ (1541332124344162269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4663*100000000000000000000^1024 ≤ 1541332124344162269^1024*5^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1541332124344162269 100000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1541332124344162269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4663 := by
      have hnat : (1 : ℕ)^1024*1^4663 ≤ 1^4663*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101541332124344162269/100000000000000000000 : ℝ) ≤ (1003364609778741/1000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (101541332124344162269/100000000000000000000 : ℝ)^1024 ≤ (1003364609778741/1000000000000000 : ℝ)^4663 := by
      have hnat : (101541332124344162269 : ℕ)^1024*1000000000000000^4663 ≤ 1003364609778741^4663*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101541332124344162269 100000000000000000000 1003364609778741 1000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003364609778741/1000000000000000 : ℝ)) (X := (101541332124344162269/100000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51541332124344162269/50000000000000000000 : ℝ) ≤ (503364609778741/500000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (51541332124344162269/50000000000000000000 : ℝ)^1024 ≤ (503364609778741/500000000000000 : ℝ)^4663 := by
      have hnat : (51541332124344162269 : ℕ)^1024*500000000000000^4663 ≤ 503364609778741^4663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51541332124344162269 50000000000000000000 503364609778741 500000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (503364609778741/500000000000000 : ℝ)) (X := (51541332124344162269/50000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3364609778741/400000000000000 : ℝ)*(0 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3364609778741/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1541332124344162269/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3364609778741/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3364609778741/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1003364609778741/1000000000000000 : ℝ) by norm_num, show 1+(1541332124344162269/100000000000000000000 : ℝ)+(0 : ℝ)=(101541332124344162269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1541332124344162269/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3364609778741/400000000000000 : ℝ)*(2/5 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3364609778741/400000000000000 : ℝ)*(2/5 : ℝ)=(503364609778741/500000000000000 : ℝ) by norm_num, show 1+2*(1541332124344162269/100000000000000000000 : ℝ)=(51541332124344162269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3364609778741/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3364609778741/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3364609778741/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3364609778741/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3364609778741/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3364609778741/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-403014947/2500000000 : ℝ)*X 0 0+(1171900421/2000000000 : ℝ)*X 0 1+(2442461551/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((136562501/250000000 : ℝ)*X 1 0+(-430697163/2000000000 : ℝ)*X 1 1+(1221230757/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5462500113/10000000000 : ℝ)*X 2 0+(122123073/250000000 : ℝ)*X 2 1+(-67296433/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((825251201/2000000000 : ℝ)*X 0 0+(1547006287/5000000000 : ℝ)*X 0 1+(5416524049/10000000000 : ℝ)*X 0 2+(825251201/2000000000 : ℝ)*X 1 0+(1547006287/5000000000 : ℝ)*X 1 1+(5416524049/10000000000 : ℝ)*X 1 2+(825251201/2000000000 : ℝ)*X 2 0+(1547006287/5000000000 : ℝ)*X 2 1+(5416524049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-807504993/5000000000 : ℝ)*X 0 0+(4909405953/10000000000 : ℝ)*X 0 1+(233366231/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((81188443/156250000 : ℝ)*X 1 0+(-24085053/200000000 : ℝ)*X 1 1+(5834155859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196060313/10000000000 : ℝ)*X 2 0+(1458538939/2500000000 : ℝ)*X 2 1+(-150531609/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2066643519/5000000000 : ℝ)*X 0 0+(107163581/200000000 : ℝ)*X 0 1+(3154414889/10000000000 : ℝ)*X 0 2+(2066643519/5000000000 : ℝ)*X 1 0+(107163581/200000000 : ℝ)*X 1 1+(3154414889/10000000000 : ℝ)*X 1 2+(2066643519/5000000000 : ℝ)*X 2 0+(107163581/200000000 : ℝ)*X 2 1+(3154414889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1407668548215585438843/400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7940539/25000000000000 : ℝ)*(base1) + (624057261/100000000000000 : ℝ)*(base19) + (31888487/5000000000000 : ℝ)*(base23) + (40604487/50000000000000 : ℝ)*(upper3) + (72339461/100000000000000 : ℝ)*(upper5) + (14566589625447/2000000000000 : ℝ)*(major0) + (14566589625447/2000000000000 : ℝ)*(major1) + (14566589625447/2000000000000 : ℝ)*(major2) + (64130392356539/6250000000000 : ℝ)*(sp0) + (128260985717501/12500000000000 : ℝ)*(sp1) + (1026087872027529/100000000000000 : ℝ)*(sp2) + (430569299046713/100000000000000 : ℝ)*(sp3) + (2263854801/100000000000000 : ℝ)*(sp4) + (251158211/25000000000000 : ℝ)*(sp7) + (26910645965107/6250000000000 : ℝ)*(f.failure) + (1026088509797269/100000000000000 : ℝ)*(f.sum) + (457240833373/400000000000000000000000000 : ℝ)*base66 + (4664347845773/800000000000000000000000000 : ℝ)*base68 + (451641481427/800000000000000000000000000 : ℝ)*base69 + (3003777143373/800000000000000000000000000 : ℝ)*base72 + (180107154573/400000000000000000000000000 : ℝ)*base74 + (808082359373/800000000000000000000000000 : ℝ)*base76 + (1061385508973/800000000000000000000000000 : ℝ)*base78 + (2768188491373/800000000000000000000000000 : ℝ)*base80 + (942019050627/400000000000000000000000000 : ℝ)*base81 + (4573977/625000000000000000000 : ℝ)*base90 + (4573977/625000000000000000000 : ℝ)*base92 + (4573977/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19091904564746108037117/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (426349/100000000000 : ℝ)*(base19) + (416919489/100000000000000 : ℝ)*(base23) + (35685933/50000000000000 : ℝ)*(base32) + (70446751/100000000000000 : ℝ)*(upper3) + (1153543/10000000000000 : ℝ)*(upper5) + (383785522753807/50000000000000 : ℝ)*(major0) + (383785522753807/50000000000000 : ℝ)*(major1) + (383785522753807/50000000000000 : ℝ)*(major2) + (306160741/25000000000000 : ℝ)*(sp1) + (599517631/50000000000000 : ℝ)*(sp2) + (540686525940407/50000000000000 : ℝ)*(sp4) + (21627428017777/2000000000000 : ℝ)*(sp5) + (67585714745379/6250000000000 : ℝ)*(sp6) + (453768904122859/100000000000000 : ℝ)*(sp7) + (226884487747363/50000000000000 : ℝ)*(f.failure) + (540686525940407/50000000000000 : ℝ)*(f.sum) + (13867355036987/10000000000000000000000000000 : ℝ)*base65 + (209231491576987/20000000000000000000000000000 : ℝ)*base67 + (24901684603013/20000000000000000000000000000 : ℝ)*base70 + (110715377376987/20000000000000000000000000000 : ℝ)*base71 + (82207327516987/10000000000000000000000000000 : ℝ)*base73 + (71846610443013/20000000000000000000000000000 : ℝ)*base76 + (26066400183013/20000000000000000000000000000 : ℝ)*base78 + (37032617936987/20000000000000000000000000000 : ℝ)*base79 + (27581909706987/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24098807/5000000000000000000000 : ℝ)*base89 + (24098807/5000000000000000000000 : ℝ)*base91 + (24098807/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1584_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3709/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3073/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1584_s1_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-109197577/625000000 : ℝ)*x 0 + (34543923/62500000 : ℝ)*x 1 + (2565125853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109197577/625000000 : ℝ)^4665 ≤ (10696597134957/100000000000000 : ℝ)^3641 := by
    have hnat : (109197577 : ℕ)^4665*100000000000000^3641 ≤ 10696597134957^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109197577 625000000 10696597134957 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34543923/62500000 : ℝ)^4665 ≤ (9356202633137/20000000000000 : ℝ)^3641 := by
    have hnat : (34543923 : ℕ)^4665*20000000000000^3641 ≤ 9356202633137^3641*62500000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34543923 62500000 9356202633137 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565125853/5000000000 : ℝ)^4665 ≤ (42522389690957/100000000000000 : ℝ)^3641 := by
    have hnat : (2565125853 : ℕ)^4665*100000000000000^3641 ≤ 42522389690957^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565125853 5000000000 42522389690957 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-109197577/625000000 : ℝ), (34543923/62500000 : ℝ), (2565125853/5000000000 : ℝ)] ![(10696597134957/100000000000000 : ℝ), (9356202633137/20000000000000 : ℝ), (42522389690957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-109197577/625000000 : ℝ)|^4665 ≤ (10696597134957/100000000000000 : ℝ)^3641
        have hw : |(-109197577/625000000 : ℝ)|=(109197577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34543923/62500000 : ℝ)|^4665 ≤ (9356202633137/20000000000000 : ℝ)^3641
        have hw : |(34543923/62500000 : ℝ)|=(34543923/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565125853/5000000000 : ℝ)|^4665 ≤ (42522389690957/100000000000000 : ℝ)^3641
        have hw : |(2565125853/5000000000 : ℝ)|=(2565125853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343523253/2500000000 : ℝ)*x 0 + (-1954402583/10000000000 : ℝ)*x 1 + (205210053/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343523253/2500000000 : ℝ)^4665 ≤ (45129011921833/100000000000000 : ℝ)^3641 := by
    have hnat : (1343523253 : ℕ)^4665*100000000000000^3641 ≤ 45129011921833^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343523253 2500000000 45129011921833 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954402583/10000000000 : ℝ)^4665 ≤ (3087150606703/25000000000000 : ℝ)^3641 := by
    have hnat : (1954402583 : ℕ)^4665*25000000000000^3641 ≤ 3087150606703^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954402583 10000000000 3087150606703 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205210053/400000000 : ℝ)^4665 ≤ (5315298205609/12500000000000 : ℝ)^3641 := by
    have hnat : (205210053 : ℕ)^4665*12500000000000^3641 ≤ 5315298205609^3641*400000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205210053 400000000 5315298205609 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343523253/2500000000 : ℝ), (-1954402583/10000000000 : ℝ), (205210053/400000000 : ℝ)] ![(45129011921833/100000000000000 : ℝ), (3087150606703/25000000000000 : ℝ), (5315298205609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343523253/2500000000 : ℝ)|^4665 ≤ (45129011921833/100000000000000 : ℝ)^3641
        have hw : |(1343523253/2500000000 : ℝ)|=(1343523253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954402583/10000000000 : ℝ)|^4665 ≤ (3087150606703/25000000000000 : ℝ)^3641
        have hw : |(-1954402583/10000000000 : ℝ)|=(1954402583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205210053/400000000 : ℝ)|^4665 ≤ (5315298205609/12500000000000 : ℝ)^3641
        have hw : |(205210053/400000000 : ℝ)|=(205210053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687046311/5000000000 : ℝ)*x 0 + (5130251677/10000000000 : ℝ)*x 1 + (-977201319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687046311/5000000000 : ℝ)^4665 ≤ (4512900772573/10000000000000 : ℝ)^3641 := by
    have hnat : (2687046311 : ℕ)^4665*10000000000000^3641 ≤ 4512900772573^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687046311 5000000000 4512900772573 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130251677/10000000000 : ℝ)^4665 ≤ (42522389382987/100000000000000 : ℝ)^3641 := by
    have hnat : (5130251677 : ℕ)^4665*100000000000000^3641 ≤ 42522389382987^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130251677 10000000000 42522389382987 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (977201319/5000000000 : ℝ)^4665 ≤ (1543575359007/12500000000000 : ℝ)^3641 := by
    have hnat : (977201319 : ℕ)^4665*12500000000000^3641 ≤ 1543575359007^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977201319 5000000000 1543575359007 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687046311/5000000000 : ℝ), (5130251677/10000000000 : ℝ), (-977201319/5000000000 : ℝ)] ![(4512900772573/10000000000000 : ℝ), (42522389382987/100000000000000 : ℝ), (1543575359007/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687046311/5000000000 : ℝ)|^4665 ≤ (4512900772573/10000000000000 : ℝ)^3641
        have hw : |(2687046311/5000000000 : ℝ)|=(2687046311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130251677/10000000000 : ℝ)|^4665 ≤ (42522389382987/100000000000000 : ℝ)^3641
        have hw : |(5130251677/10000000000 : ℝ)|=(5130251677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-977201319/5000000000 : ℝ)|^4665 ≤ (1543575359007/12500000000000 : ℝ)^3641
        have hw : |(-977201319/5000000000 : ℝ)|=(977201319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4223370973/10000000000 : ℝ)*x 0 + (3771694537/10000000000 : ℝ)*x 1 + (943449761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4223370973/10000000000 : ℝ)^4665 ≤ (33142029706107/100000000000000 : ℝ)^3641 := by
    have hnat : (4223370973 : ℕ)^4665*100000000000000^3641 ≤ 33142029706107^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223370973 10000000000 33142029706107 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3771694537/10000000000 : ℝ)^4665 ≤ (2867088121613/10000000000000 : ℝ)^3641 := by
    have hnat : (3771694537 : ℕ)^4665*10000000000000^3641 ≤ 2867088121613^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3771694537 10000000000 2867088121613 10000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943449761/2000000000 : ℝ)^4665 ≤ (38187089058789/100000000000000 : ℝ)^3641 := by
    have hnat : (943449761 : ℕ)^4665*100000000000000^3641 ≤ 38187089058789^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943449761 2000000000 38187089058789 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4223370973/10000000000 : ℝ), (3771694537/10000000000 : ℝ), (943449761/2000000000 : ℝ)] ![(33142029706107/100000000000000 : ℝ), (2867088121613/10000000000000 : ℝ), (38187089058789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4223370973/10000000000 : ℝ)|^4665 ≤ (33142029706107/100000000000000 : ℝ)^3641
        have hw : |(4223370973/10000000000 : ℝ)|=(4223370973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3771694537/10000000000 : ℝ)|^4665 ≤ (2867088121613/10000000000000 : ℝ)^3641
        have hw : |(3771694537/10000000000 : ℝ)|=(3771694537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943449761/2000000000 : ℝ)|^4665 ≤ (38187089058789/100000000000000 : ℝ)^3641
        have hw : |(943449761/2000000000 : ℝ)|=(943449761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69894217/400000000 : ℝ)*x 0 + (5134267879/10000000000 : ℝ)*x 1 + (5522953453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69894217/400000000 : ℝ)^4665 ≤ (5349060214919/50000000000000 : ℝ)^3641 := by
    have hnat : (69894217 : ℕ)^4665*50000000000000^3641 ≤ 5349060214919^3641*400000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69894217 400000000 5349060214919 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134267879/10000000000 : ℝ)^4665 ≤ (42565044712749/100000000000000 : ℝ)^3641 := by
    have hnat : (5134267879 : ℕ)^4665*100000000000000^3641 ≤ 42565044712749^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134267879 10000000000 42565044712749 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522953453/10000000000 : ℝ)^4665 ≤ (46736834850727/100000000000000 : ℝ)^3641 := by
    have hnat : (5522953453 : ℕ)^4665*100000000000000^3641 ≤ 46736834850727^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522953453 10000000000 46736834850727 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69894217/400000000 : ℝ), (5134267879/10000000000 : ℝ), (5522953453/10000000000 : ℝ)] ![(5349060214919/50000000000000 : ℝ), (42565044712749/100000000000000 : ℝ), (46736834850727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69894217/400000000 : ℝ)|^4665 ≤ (5349060214919/50000000000000 : ℝ)^3641
        have hw : |(-69894217/400000000 : ℝ)|=(69894217/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134267879/10000000000 : ℝ)|^4665 ≤ (42565044712749/100000000000000 : ℝ)^3641
        have hw : |(5134267879/10000000000 : ℝ)|=(5134267879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522953453/10000000000 : ℝ)|^4665 ≤ (46736834850727/100000000000000 : ℝ)^3641
        have hw : |(5522953453/10000000000 : ℝ)|=(5522953453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268778029/10000000000 : ℝ)*x 0 + (-312340101/2000000000 : ℝ)*x 1 + (5522954187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268778029/10000000000 : ℝ)^4665 ≤ (549988000033/1250000000000 : ℝ)^3641 := by
    have hnat : (5268778029 : ℕ)^4665*1250000000000^3641 ≤ 549988000033^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268778029 10000000000 549988000033 1250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312340101/2000000000 : ℝ)^4665 ≤ (1852823434289/20000000000000 : ℝ)^3641 := by
    have hnat : (312340101 : ℕ)^4665*20000000000000^3641 ≤ 1852823434289^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312340101 2000000000 1852823434289 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522954187/10000000000 : ℝ)^4665 ≤ (46736842808929/100000000000000 : ℝ)^3641 := by
    have hnat : (5522954187 : ℕ)^4665*100000000000000^3641 ≤ 46736842808929^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522954187 10000000000 46736842808929 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268778029/10000000000 : ℝ), (-312340101/2000000000 : ℝ), (5522954187/10000000000 : ℝ)] ![(549988000033/1250000000000 : ℝ), (1852823434289/20000000000000 : ℝ), (46736842808929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268778029/10000000000 : ℝ)|^4665 ≤ (549988000033/1250000000000 : ℝ)^3641
        have hw : |(5268778029/10000000000 : ℝ)|=(5268778029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-312340101/2000000000 : ℝ)|^4665 ≤ (1852823434289/20000000000000 : ℝ)^3641
        have hw : |(-312340101/2000000000 : ℝ)|=(312340101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522954187/10000000000 : ℝ)|^4665 ≤ (46736842808929/100000000000000 : ℝ)^3641
        have hw : |(5522954187/10000000000 : ℝ)|=(5522954187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5268777117/10000000000 : ℝ)*x 0 + (5522954549/10000000000 : ℝ)*x 1 + (-195212659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268777117/10000000000 : ℝ)^4665 ≤ (43999030244679/100000000000000 : ℝ)^3641 := by
    have hnat : (5268777117 : ℕ)^4665*100000000000000^3641 ≤ 43999030244679^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268777117 10000000000 43999030244679 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522954549/10000000000 : ℝ)^4665 ≤ (46736846733819/100000000000000 : ℝ)^3641 := by
    have hnat : (5522954549 : ℕ)^4665*100000000000000^3641 ≤ 46736846733819^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522954549 10000000000 46736846733819 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195212659/1250000000 : ℝ)^4665 ≤ (9264123000963/100000000000000 : ℝ)^3641 := by
    have hnat : (195212659 : ℕ)^4665*100000000000000^3641 ≤ 9264123000963^3641*1250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195212659 1250000000 9264123000963 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268777117/10000000000 : ℝ), (5522954549/10000000000 : ℝ), (-195212659/1250000000 : ℝ)] ![(43999030244679/100000000000000 : ℝ), (46736846733819/100000000000000 : ℝ), (9264123000963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268777117/10000000000 : ℝ)|^4665 ≤ (43999030244679/100000000000000 : ℝ)^3641
        have hw : |(5268777117/10000000000 : ℝ)|=(5268777117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522954549/10000000000 : ℝ)|^4665 ≤ (46736846733819/100000000000000 : ℝ)^3641
        have hw : |(5522954549/10000000000 : ℝ)|=(5522954549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195212659/1250000000 : ℝ)|^4665 ≤ (9264123000963/100000000000000 : ℝ)^3641
        have hw : |(-195212659/1250000000 : ℝ)|=(195212659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s1_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65997389/156250000 : ℝ)*x 0 + (941535781/2000000000 : ℝ)*x 1 + (3781402581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65997389/156250000 : ℝ)^4665 ≤ (4143334259909/12500000000000 : ℝ)^3641 := by
    have hnat : (65997389 : ℕ)^4665*12500000000000^3641 ≤ 4143334259909^3641*156250000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65997389 156250000 4143334259909 12500000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (941535781/2000000000 : ℝ)^4665 ≤ (38087859247091/100000000000000 : ℝ)^3641 := by
    have hnat : (941535781 : ℕ)^4665*100000000000000^3641 ≤ 38087859247091^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941535781 2000000000 38087859247091 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3781402581/10000000000 : ℝ)^4665 ≤ (5753093331731/20000000000000 : ℝ)^3641 := by
    have hnat : (3781402581 : ℕ)^4665*20000000000000^3641 ≤ 5753093331731^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781402581 10000000000 5753093331731 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65997389/156250000 : ℝ), (941535781/2000000000 : ℝ), (3781402581/10000000000 : ℝ)] ![(4143334259909/12500000000000 : ℝ), (38087859247091/100000000000000 : ℝ), (5753093331731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65997389/156250000 : ℝ)|^4665 ≤ (4143334259909/12500000000000 : ℝ)^3641
        have hw : |(65997389/156250000 : ℝ)|=(65997389/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(941535781/2000000000 : ℝ)|^4665 ≤ (38087859247091/100000000000000 : ℝ)^3641
        have hw : |(941535781/2000000000 : ℝ)|=(941535781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3781402581/10000000000 : ℝ)|^4665 ≤ (5753093331731/20000000000000 : ℝ)^3641
        have hw : |(3781402581/10000000000 : ℝ)|=(3781402581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3073/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3709/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3073/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3709/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3073/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3709/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3073/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3709/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3073/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3709/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3073/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3709/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3073/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3709/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3709/100000 : ℝ) ^ (4663/1024 : ℝ) ≤ (30535792316289/100000000000000000000 : ℝ) := by
    have hpowers : (3709/100000 : ℝ)^4663 ≤ (30535792316289/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3709 : ℕ)^4663*100000000000000000000^1024 ≤ 30535792316289^1024*100000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3709 100000 30535792316289 100000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3709/100000 : ℝ)) (X := (30535792316289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3073/12500 : ℝ) ^ (4663/1024 : ℝ) ≤ (83980381657596177/50000000000000000000 : ℝ) := by
    have hpowers : (3073/12500 : ℝ)^4663 ≤ (83980381657596177/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3073 : ℕ)^4663*50000000000000000000^1024 ≤ 83980381657596177^1024*12500^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3073 12500 83980381657596177 50000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3073/12500 : ℝ)) (X := (83980381657596177/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000030535792316289/50000000000000000000 : ℝ) ≤ (1000000134113849/1000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (50000030535792316289/50000000000000000000 : ℝ)^1024 ≤ (1000000134113849/1000000000000000 : ℝ)^4663 := by
      have hnat : (50000030535792316289 : ℕ)^1024*1000000000000000^4663 ≤ 1000000134113849^4663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000030535792316289 50000000000000000000 1000000134113849 1000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000134113849/1000000000000000 : ℝ)) (X := (50000030535792316289/50000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100167991299107508643/100000000000000000000 : ℝ) ≤ (5001843345928027/5000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (100167991299107508643/100000000000000000000 : ℝ)^1024 ≤ (5001843345928027/5000000000000000 : ℝ)^4663 := by
      have hnat : (100167991299107508643 : ℕ)^1024*5000000000000000^4663 ≤ 5001843345928027^4663*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100167991299107508643 100000000000000000000 5001843345928027 5000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001843345928027/5000000000000000 : ℝ)) (X := (100167991299107508643/100000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25083980381657596177/25000000000000000000 : ℝ) ≤ (5003686021286809/5000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (25083980381657596177/25000000000000000000 : ℝ)^1024 ≤ (5003686021286809/5000000000000000 : ℝ)^4663 := by
      have hnat : (25083980381657596177 : ℕ)^1024*5000000000000000^4663 ≤ 5003686021286809^4663*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25083980381657596177 25000000000000000000 5003686021286809 5000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003686021286809/5000000000000000 : ℝ)) (X := (25083980381657596177/25000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30535792316289/100000000000000000000 : ℝ) ≤ ((104361345032321544499/104375000000000000000 : ℝ)+2*(921337679391/521875000000000 : ℝ)*(3709/100000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (104361345032321544499/104375000000000000000 : ℝ)+2*(921337679391/521875000000000 : ℝ)*(3709/100000 : ℝ)=(1000000134113849/1000000000000000 : ℝ) by norm_num, show 1+2*(30535792316289/100000000000000000000 : ℝ)=(50000030535792316289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83980381657596177/50000000000000000000 : ℝ)+(30535792316289/100000000000000000000 : ℝ) ≤ ((104361345032321544499/104375000000000000000 : ℝ)+(921337679391/521875000000000 : ℝ)*((3073/12500 : ℝ)+(3709/100000 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (104361345032321544499/104375000000000000000 : ℝ)+(921337679391/521875000000000 : ℝ)*((3073/12500 : ℝ)+(3709/100000 : ℝ))=(5001843345928027/5000000000000000 : ℝ) by norm_num, show 1+(83980381657596177/50000000000000000000 : ℝ)+(30535792316289/100000000000000000000 : ℝ)=(100167991299107508643/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83980381657596177/50000000000000000000 : ℝ) ≤ ((104361345032321544499/104375000000000000000 : ℝ)+2*(921337679391/521875000000000 : ℝ)*(3073/12500 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (104361345032321544499/104375000000000000000 : ℝ)+2*(921337679391/521875000000000 : ℝ)*(3073/12500 : ℝ)=(5003686021286809/5000000000000000 : ℝ) by norm_num, show 1+2*(83980381657596177/50000000000000000000 : ℝ)=(25083980381657596177/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (104361345032321544499/104375000000000000000 : ℝ)*(X 1 0+X 2 0)+(921337679391/521875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (3709/100000 : ℝ)) (hi := (3073/12500 : ℝ)) (c := (104361345032321544499/104375000000000000000 : ℝ)) (alpha := (921337679391/521875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (104361345032321544499/104375000000000000000 : ℝ)*(X 0 1+X 2 1)+(921337679391/521875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (3709/100000 : ℝ)) (hi := (3073/12500 : ℝ)) (c := (104361345032321544499/104375000000000000000 : ℝ)) (alpha := (921337679391/521875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (104361345032321544499/104375000000000000000 : ℝ)*(X 0 2+X 1 2)+(921337679391/521875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (3709/100000 : ℝ)) (hi := (3073/12500 : ℝ)) (c := (104361345032321544499/104375000000000000000 : ℝ)) (alpha := (921337679391/521875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-109197577/625000000 : ℝ)*X 0 0+(34543923/62500000 : ℝ)*X 0 1+(2565125853/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343523253/2500000000 : ℝ)*X 1 0+(-1954402583/10000000000 : ℝ)*X 1 1+(205210053/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687046311/5000000000 : ℝ)*X 2 0+(5130251677/10000000000 : ℝ)*X 2 1+(-977201319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4223370973/10000000000 : ℝ)*X 0 0+(3771694537/10000000000 : ℝ)*X 0 1+(943449761/2000000000 : ℝ)*X 0 2+(4223370973/10000000000 : ℝ)*X 1 0+(3771694537/10000000000 : ℝ)*X 1 1+(943449761/2000000000 : ℝ)*X 1 2+(4223370973/10000000000 : ℝ)*X 2 0+(3771694537/10000000000 : ℝ)*X 2 1+(943449761/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-69894217/400000000 : ℝ)*X 0 0+(5134267879/10000000000 : ℝ)*X 0 1+(5522953453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5268778029/10000000000 : ℝ)*X 1 0+(-312340101/2000000000 : ℝ)*X 1 1+(5522954187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5268777117/10000000000 : ℝ)*X 2 0+(5522954549/10000000000 : ℝ)*X 2 1+(-195212659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((65997389/156250000 : ℝ)*X 0 0+(941535781/2000000000 : ℝ)*X 0 1+(3781402581/10000000000 : ℝ)*X 0 2+(65997389/156250000 : ℝ)*X 1 0+(941535781/2000000000 : ℝ)*X 1 1+(3781402581/10000000000 : ℝ)*X 1 2+(65997389/156250000 : ℝ)*X 2 0+(941535781/2000000000 : ℝ)*X 2 1+(3781402581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1904543116284231016990420443/260937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (270587489/12500000000000 : ℝ)*(base19) + (233832967/12500000000000 : ℝ)*(base23) + (252564609/100000000000000 : ℝ)*(upper3) + (1866379/3125000000000 : ℝ)*(upper4) + (105224839/100000000000000 : ℝ)*(upper5) + (178897480119519/10000000000000 : ℝ)*(major0) + (178897480119519/10000000000000 : ℝ)*(major1) + (1788974801195191/100000000000000 : ℝ)*(major2) + (252033383494311/10000000000000 : ℝ)*(sp0) + (504069927434437/20000000000000 : ℝ)*(sp1) + (2520349931208361/100000000000000 : ℝ)*(sp2) + (528794332650491/50000000000000 : ℝ)*(sp3) + (4491732247/25000000000000 : ℝ)*(sp4) + (2222980591/25000000000000 : ℝ)*(sp7) + (528798778611673/50000000000000 : ℝ)*(f.failure) + (78760993808503/3125000000000 : ℝ)*(f.sum) + (97219132500899/13046875000000000000000000000 : ℝ)*base65 + (15521616974891904019/1043750000000000000000000000000000 : ℝ)*base68 + (48130799902725695691/10437500000000000000000000000000000 : ℝ)*base70 + (3325424155816904019/1043750000000000000000000000000000 : ℝ)*base72 + (166997533157183/104375000000000000000000000000 : ℝ)*base74 + (6368043755586804309/10437500000000000000000000000000000 : ℝ)*base75 + (9132009664242224019/1043750000000000000000000000000000 : ℝ)*base78 + (6249635567323474019/1043750000000000000000000000000000 : ℝ)*base80 + (278109706733/5218750000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (36917397/5000000000000000000000 : ℝ)*base89 + (36917397/5000000000000000000000 : ℝ)*base91 + (13082603/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46872099129334667033566970979/5218750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31572399/2000000000000 : ℝ)*(base19) + (1387864123/100000000000000 : ℝ)*(base23) + (115681/80000000000 : ℝ)*(upper2) + (45520587/12500000000000 : ℝ)*(upper3) + (129665313/100000000000000 : ℝ)*(upper5) + (1826179328381831/100000000000000 : ℝ)*(major0) + (1826179328381831/100000000000000 : ℝ)*(major1) + (1826179328381831/100000000000000 : ℝ)*(major2) + (6766333963/50000000000000 : ℝ)*(sp1) + (501537461/4000000000000 : ℝ)*(sp2) + (1286383202956773/50000000000000 : ℝ)*(sp4) + (257275129462567/10000000000000 : ℝ)*(sp5) + (2572752479612899/100000000000000 : ℝ)*(sp6) + (539795975733721/50000000000000 : ℝ)*(sp7) + (539795975733721/50000000000000 : ℝ)*(f.failure) + (1286383202956773/50000000000000 : ℝ)*(f.sum) + (24259355091717/52187500000000000000000000000 : ℝ)*base65 + (76688565627813797669/10437500000000000000000000000000000 : ℝ)*base67 + (64089018957063797669/10437500000000000000000000000000000 : ℝ)*base69 + (35241152614688797669/10437500000000000000000000000000000 : ℝ)*base71 + (122966280110467/52187500000000000000000000000 : ℝ)*base73 + (122846842729938797669/10437500000000000000000000000000000 : ℝ)*base75 + (25027921183626297669/10437500000000000000000000000000000 : ℝ)*base77 + (27093312251938797669/10437500000000000000000000000000000 : ℝ)*base79 + (6038982320713/3261718750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (804331/5000000000000000000000 : ℝ)*base90 + (804331/5000000000000000000000 : ℝ)*base92 + (804331/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1584_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3073/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3709/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1584_s2_0 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-352906841/2000000000 : ℝ)*x 0 + (5438018053/10000000000 : ℝ)*x 1 + (5207924157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352906841/2000000000 : ℝ)^4665 ≤ (2166612545549/20000000000000 : ℝ)^3641 := by
    have hnat : (352906841 : ℕ)^4665*20000000000000^3641 ≤ 2166612545549^3641*2000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352906841 2000000000 2166612545549 20000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438018053/10000000000 : ℝ)^4665 ≤ (45817943999993/100000000000000 : ℝ)^3641 := by
    have hnat : (5438018053 : ℕ)^4665*100000000000000^3641 ≤ 45817943999993^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438018053 10000000000 45817943999993 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5207924157/10000000000 : ℝ)^4665 ≤ (2167449663153/5000000000000 : ℝ)^3641 := by
    have hnat : (5207924157 : ℕ)^4665*5000000000000^3641 ≤ 2167449663153^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5207924157 10000000000 2167449663153 5000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352906841/2000000000 : ℝ), (5438018053/10000000000 : ℝ), (5207924157/10000000000 : ℝ)] ![(2166612545549/20000000000000 : ℝ), (45817943999993/100000000000000 : ℝ), (2167449663153/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352906841/2000000000 : ℝ)|^4665 ≤ (2166612545549/20000000000000 : ℝ)^3641
        have hw : |(-352906841/2000000000 : ℝ)|=(352906841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438018053/10000000000 : ℝ)|^4665 ≤ (45817943999993/100000000000000 : ℝ)^3641
        have hw : |(5438018053/10000000000 : ℝ)|=(5438018053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5207924157/10000000000 : ℝ)|^4665 ≤ (2167449663153/5000000000000 : ℝ)^3641
        have hw : |(5207924157/10000000000 : ℝ)|=(5207924157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_1 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351023111/10000000000 : ℝ)*x 0 + (-1882560811/10000000000 : ℝ)*x 1 + (520792481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351023111/10000000000 : ℝ)^4665 ≤ (22440473649689/50000000000000 : ℝ)^3641 := by
    have hnat : (5351023111 : ℕ)^4665*50000000000000^3641 ≤ 22440473649689^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351023111 10000000000 22440473649689 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882560811/10000000000 : ℝ)^4665 ≤ (2942513115607/25000000000000 : ℝ)^3641 := by
    have hnat : (1882560811 : ℕ)^4665*25000000000000^3641 ≤ 2942513115607^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882560811 10000000000 2942513115607 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520792481/1000000000 : ℝ)^4665 ≤ (2709312514191/6250000000000 : ℝ)^3641 := by
    have hnat : (520792481 : ℕ)^4665*6250000000000^3641 ≤ 2709312514191^3641*1000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520792481 1000000000 2709312514191 6250000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351023111/10000000000 : ℝ), (-1882560811/10000000000 : ℝ), (520792481/1000000000 : ℝ)] ![(22440473649689/50000000000000 : ℝ), (2942513115607/25000000000000 : ℝ), (2709312514191/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351023111/10000000000 : ℝ)|^4665 ≤ (22440473649689/50000000000000 : ℝ)^3641
        have hw : |(5351023111/10000000000 : ℝ)|=(5351023111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882560811/10000000000 : ℝ)|^4665 ≤ (2942513115607/25000000000000 : ℝ)^3641
        have hw : |(-1882560811/10000000000 : ℝ)|=(1882560811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520792481/1000000000 : ℝ)|^4665 ≤ (2709312514191/6250000000000 : ℝ)^3641
        have hw : |(520792481/1000000000 : ℝ)|=(520792481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_2 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337755881/2500000000 : ℝ)*x 0 + (162747613/312500000 : ℝ)*x 1 + (-941280923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337755881/2500000000 : ℝ)^4665 ≤ (44880951737571/100000000000000 : ℝ)^3641 := by
    have hnat : (1337755881 : ℕ)^4665*100000000000000^3641 ≤ 44880951737571^3641*2500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337755881 2500000000 44880951737571 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162747613/312500000 : ℝ)^4665 ≤ (43348987493501/100000000000000 : ℝ)^3641 := by
    have hnat : (162747613 : ℕ)^4665*100000000000000^3641 ≤ 43348987493501^3641*312500000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162747613 312500000 43348987493501 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (941280923/5000000000 : ℝ)^4665 ≤ (11770060753311/100000000000000 : ℝ)^3641 := by
    have hnat : (941280923 : ℕ)^4665*100000000000000^3641 ≤ 11770060753311^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      941280923 5000000000 11770060753311 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337755881/2500000000 : ℝ), (162747613/312500000 : ℝ), (-941280923/5000000000 : ℝ)] ![(44880951737571/100000000000000 : ℝ), (43348987493501/100000000000000 : ℝ), (11770060753311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337755881/2500000000 : ℝ)|^4665 ≤ (44880951737571/100000000000000 : ℝ)^3641
        have hw : |(1337755881/2500000000 : ℝ)|=(1337755881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162747613/312500000 : ℝ)|^4665 ≤ (43348987493501/100000000000000 : ℝ)^3641
        have hw : |(162747613/312500000 : ℝ)|=(162747613/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-941280923/5000000000 : ℝ)|^4665 ≤ (11770060753311/100000000000000 : ℝ)^3641
        have hw : |(-941280923/5000000000 : ℝ)|=(941280923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_3 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117994297/5000000000 : ℝ)*x 0 + (1984462507/5000000000 : ℝ)*x 1 + (2258629237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117994297/5000000000 : ℝ)^4665 ≤ (5198272503/15625000000 : ℝ)^3641 := by
    have hnat : (2117994297 : ℕ)^4665*15625000000^3641 ≤ 5198272503^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117994297 5000000000 5198272503 15625000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984462507/5000000000 : ℝ)^4665 ≤ (30605754452259/100000000000000 : ℝ)^3641 := by
    have hnat : (1984462507 : ℕ)^4665*100000000000000^3641 ≤ 30605754452259^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984462507 5000000000 30605754452259 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2258629237/5000000000 : ℝ)^4665 ≤ (564457836269/1562500000000 : ℝ)^3641 := by
    have hnat : (2258629237 : ℕ)^4665*1562500000000^3641 ≤ 564457836269^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258629237 5000000000 564457836269 1562500000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117994297/5000000000 : ℝ), (1984462507/5000000000 : ℝ), (2258629237/5000000000 : ℝ)] ![(5198272503/15625000000 : ℝ), (30605754452259/100000000000000 : ℝ), (564457836269/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117994297/5000000000 : ℝ)|^4665 ≤ (5198272503/15625000000 : ℝ)^3641
        have hw : |(2117994297/5000000000 : ℝ)|=(2117994297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1984462507/5000000000 : ℝ)|^4665 ≤ (30605754452259/100000000000000 : ℝ)^3641
        have hw : |(1984462507/5000000000 : ℝ)|=(1984462507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2258629237/5000000000 : ℝ)|^4665 ≤ (564457836269/1562500000000 : ℝ)^3641
        have hw : |(2258629237/5000000000 : ℝ)|=(2258629237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_4 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-220571473/1250000000 : ℝ)*x 0 + (41674263/80000000 : ℝ)*x 1 + (217465931/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220571473/1250000000 : ℝ)^4665 ≤ (5416679161911/50000000000000 : ℝ)^3641 := by
    have hnat : (220571473 : ℕ)^4665*50000000000000^3641 ≤ 5416679161911^3641*1250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220571473 1250000000 5416679161911 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41674263/80000000 : ℝ)^4665 ≤ (43363484004077/100000000000000 : ℝ)^3641 := by
    have hnat : (41674263 : ℕ)^4665*100000000000000^3641 ≤ 43363484004077^3641*80000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41674263 80000000 43363484004077 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217465931/400000000 : ℝ)^4665 ≤ (22901578829393/50000000000000 : ℝ)^3641 := by
    have hnat : (217465931 : ℕ)^4665*50000000000000^3641 ≤ 22901578829393^3641*400000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217465931 400000000 22901578829393 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220571473/1250000000 : ℝ), (41674263/80000000 : ℝ), (217465931/400000000 : ℝ)] ![(5416679161911/50000000000000 : ℝ), (43363484004077/100000000000000 : ℝ), (22901578829393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220571473/1250000000 : ℝ)|^4665 ≤ (5416679161911/50000000000000 : ℝ)^3641
        have hw : |(-220571473/1250000000 : ℝ)|=(220571473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41674263/80000000 : ℝ)|^4665 ≤ (43363484004077/100000000000000 : ℝ)^3641
        have hw : |(41674263/80000000 : ℝ)|=(41674263/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217465931/400000000 : ℝ)|^4665 ≤ (22901578829393/50000000000000 : ℝ)^3641
        have hw : |(217465931/400000000 : ℝ)|=(217465931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_5 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290043667/10000000000 : ℝ)*x 0 + (-1653837867/10000000000 : ℝ)*x 1 + (84947647/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290043667/10000000000 : ℝ)^4665 ≤ (44226701122739/100000000000000 : ℝ)^3641 := by
    have hnat : (5290043667 : ℕ)^4665*100000000000000^3641 ≤ 44226701122739^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290043667 10000000000 44226701122739 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1653837867/10000000000 : ℝ)^4665 ≤ (9970128965183/100000000000000 : ℝ)^3641 := by
    have hnat : (1653837867 : ℕ)^4665*100000000000000^3641 ≤ 9970128965183^3641*10000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1653837867 10000000000 9970128965183 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84947647/156250000 : ℝ)^4665 ≤ (11450792472187/25000000000000 : ℝ)^3641 := by
    have hnat : (84947647 : ℕ)^4665*25000000000000^3641 ≤ 11450792472187^3641*156250000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84947647 156250000 11450792472187 25000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290043667/10000000000 : ℝ), (-1653837867/10000000000 : ℝ), (84947647/156250000 : ℝ)] ![(44226701122739/100000000000000 : ℝ), (9970128965183/100000000000000 : ℝ), (11450792472187/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290043667/10000000000 : ℝ)|^4665 ≤ (44226701122739/100000000000000 : ℝ)^3641
        have hw : |(5290043667/10000000000 : ℝ)|=(5290043667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1653837867/10000000000 : ℝ)|^4665 ≤ (9970128965183/100000000000000 : ℝ)^3641
        have hw : |(-1653837867/10000000000 : ℝ)|=(1653837867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84947647/156250000 : ℝ)|^4665 ≤ (11450792472187/25000000000000 : ℝ)^3641
        have hw : |(84947647/156250000 : ℝ)|=(84947647/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_6 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330627773/625000000 : ℝ)*x 0 + (679581309/1250000000 : ℝ)*x 1 + (-103364713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330627773/625000000 : ℝ)^4665 ≤ (44226708631603/100000000000000 : ℝ)^3641 := by
    have hnat : (330627773 : ℕ)^4665*100000000000000^3641 ≤ 44226708631603^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330627773 625000000 44226708631603 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679581309/1250000000 : ℝ)^4665 ≤ (45803181373901/100000000000000 : ℝ)^3641 := by
    have hnat : (679581309 : ℕ)^4665*100000000000000^3641 ≤ 45803181373901^3641*1250000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679581309 1250000000 45803181373901 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103364713/625000000 : ℝ)^4665 ≤ (4985054986011/50000000000000 : ℝ)^3641 := by
    have hnat : (103364713 : ℕ)^4665*50000000000000^3641 ≤ 4985054986011^3641*625000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103364713 625000000 4985054986011 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330627773/625000000 : ℝ), (679581309/1250000000 : ℝ), (-103364713/625000000 : ℝ)] ![(44226708631603/100000000000000 : ℝ), (45803181373901/100000000000000 : ℝ), (4985054986011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330627773/625000000 : ℝ)|^4665 ≤ (44226708631603/100000000000000 : ℝ)^3641
        have hw : |(330627773/625000000 : ℝ)|=(330627773/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679581309/1250000000 : ℝ)|^4665 ≤ (45803181373901/100000000000000 : ℝ)^3641
        have hw : |(679581309/1250000000 : ℝ)|=(679581309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103364713/625000000 : ℝ)|^4665 ≤ (4985054986011/50000000000000 : ℝ)^3641
        have hw : |(-103364713/625000000 : ℝ)|=(103364713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1584_s2_7 (p : ℝ) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118039829/5000000000 : ℝ)*x 0 + (225701107/500000000 : ℝ)*x 1 + (1986093921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118039829/5000000000 : ℝ)^4665 ≤ (16634930186557/50000000000000 : ℝ)^3641 := by
    have hnat : (2118039829 : ℕ)^4665*50000000000000^3641 ≤ 16634930186557^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118039829 5000000000 16634930186557 50000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225701107/500000000 : ℝ)^4665 ≤ (36092144379827/100000000000000 : ℝ)^3641 := by
    have hnat : (225701107 : ℕ)^4665*100000000000000^3641 ≤ 36092144379827^3641*500000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225701107 500000000 36092144379827 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1986093921/5000000000 : ℝ)^4665 ≤ (30637995232153/100000000000000 : ℝ)^3641 := by
    have hnat : (1986093921 : ℕ)^4665*100000000000000^3641 ≤ 30637995232153^3641*5000000000^4665 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986093921 5000000000 30637995232153 100000000000000 4665 3641 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4665/1024 : ℝ)) 4665 3641 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118039829/5000000000 : ℝ), (225701107/500000000 : ℝ), (1986093921/5000000000 : ℝ)] ![(16634930186557/50000000000000 : ℝ), (36092144379827/100000000000000 : ℝ), (30637995232153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118039829/5000000000 : ℝ)|^4665 ≤ (16634930186557/50000000000000 : ℝ)^3641
        have hw : |(2118039829/5000000000 : ℝ)|=(2118039829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225701107/500000000 : ℝ)|^4665 ≤ (36092144379827/100000000000000 : ℝ)^3641
        have hw : |(225701107/500000000 : ℝ)|=(225701107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1986093921/5000000000 : ℝ)|^4665 ≤ (30637995232153/100000000000000 : ℝ)^3641
        have hw : |(1986093921/5000000000 : ℝ)|=(1986093921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1584_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (681/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (493/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9223/100000 : ℝ) ^ (4663/1024 : ℝ) ≤ (483356166371279/25000000000000000000 : ℝ) := by
    have hpowers : (9223/100000 : ℝ)^4663 ≤ (483356166371279/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9223 : ℕ)^4663*25000000000000000000^1024 ≤ 483356166371279^1024*100000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9223 100000 483356166371279 25000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9223/100000 : ℝ)) (X := (483356166371279/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/10000 : ℝ) ^ (4663/1024 : ℝ) ≤ (36953102818672831/100000000000000000000 : ℝ) := by
    have hpowers : (1763/10000 : ℝ)^4663 ≤ (36953102818672831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1763 : ℕ)^4663*100000000000000000000^1024 ≤ 36953102818672831^1024*10000^4663 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 10000 36953102818672831 100000000000000000000 4663 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/10000 : ℝ)) (X := (36953102818672831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500483356166371279/12500000000000000000 : ℝ) ≤ (10000084915161299/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (12500483356166371279/12500000000000000000 : ℝ)^1024 ≤ (10000084915161299/10000000000000000 : ℝ)^4663 := by
      have hnat : (12500483356166371279 : ℕ)^1024*10000000000000000^4663 ≤ 10000084915161299^4663*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500483356166371279 12500000000000000000 10000084915161299 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084915161299/10000000000000000 : ℝ)) (X := (12500483356166371279/12500000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038886527484157947/100000000000000000000 : ℝ) ≤ (5000426911467717/5000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (100038886527484157947/100000000000000000000 : ℝ)^1024 ≤ (5000426911467717/5000000000000000 : ℝ)^4663 := by
      have hnat : (100038886527484157947 : ℕ)^1024*5000000000000000^4663 ≤ 5000426911467717^4663*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038886527484157947 100000000000000000000 5000426911467717 5000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000426911467717/5000000000000000 : ℝ)) (X := (100038886527484157947/100000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036953102818672831/50000000000000000000 : ℝ) ≤ (10001622730709569/10000000000000000 : ℝ) ^ (4663/1024 : ℝ) := by
    have hpowers : (50036953102818672831/50000000000000000000 : ℝ)^1024 ≤ (10001622730709569/10000000000000000 : ℝ)^4663 := by
      have hnat : (50036953102818672831 : ℕ)^1024*10000000000000000^4663 ≤ 10001622730709569^4663*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036953102818672831 50000000000000000000 10001622730709569 10000000000000000 1024 4663 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001622730709569/10000000000000000 : ℝ)) (X := (50036953102818672831/50000000000000000000 : ℝ)) (by norm_num) 4663 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(483356166371279/25000000000000000000 : ℝ) ≤ ((84056530608959346483/84070000000000000000 : ℝ)+2*(153781554827/168140000000000 : ℝ)*(9223/100000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (84056530608959346483/84070000000000000000 : ℝ)+2*(153781554827/168140000000000 : ℝ)*(9223/100000 : ℝ)=(10000084915161299/10000000000000000 : ℝ) by norm_num, show 1+2*(483356166371279/25000000000000000000 : ℝ)=(12500483356166371279/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36953102818672831/100000000000000000000 : ℝ)+(483356166371279/25000000000000000000 : ℝ) ≤ ((84056530608959346483/84070000000000000000 : ℝ)+(153781554827/168140000000000 : ℝ)*((1763/10000 : ℝ)+(9223/100000 : ℝ)))^(4663/1024 : ℝ) := by
    rw [show (84056530608959346483/84070000000000000000 : ℝ)+(153781554827/168140000000000 : ℝ)*((1763/10000 : ℝ)+(9223/100000 : ℝ))=(5000426911467717/5000000000000000 : ℝ) by norm_num, show 1+(36953102818672831/100000000000000000000 : ℝ)+(483356166371279/25000000000000000000 : ℝ)=(100038886527484157947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36953102818672831/100000000000000000000 : ℝ) ≤ ((84056530608959346483/84070000000000000000 : ℝ)+2*(153781554827/168140000000000 : ℝ)*(1763/10000 : ℝ))^(4663/1024 : ℝ) := by
    rw [show (84056530608959346483/84070000000000000000 : ℝ)+2*(153781554827/168140000000000 : ℝ)*(1763/10000 : ℝ)=(10001622730709569/10000000000000000 : ℝ) by norm_num, show 1+2*(36953102818672831/100000000000000000000 : ℝ)=(50036953102818672831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84056530608959346483/84070000000000000000 : ℝ)*(X 1 0+X 2 0)+(153781554827/168140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (9223/100000 : ℝ)) (hi := (1763/10000 : ℝ)) (c := (84056530608959346483/84070000000000000000 : ℝ)) (alpha := (153781554827/168140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84056530608959346483/84070000000000000000 : ℝ)*(X 0 1+X 2 1)+(153781554827/168140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (9223/100000 : ℝ)) (hi := (1763/10000 : ℝ)) (c := (84056530608959346483/84070000000000000000 : ℝ)) (alpha := (153781554827/168140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84056530608959346483/84070000000000000000 : ℝ)*(X 0 2+X 1 2)+(153781554827/168140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4663/1024 : ℝ)) (lo := (9223/100000 : ℝ)) (hi := (1763/10000 : ℝ)) (c := (84056530608959346483/84070000000000000000 : ℝ)) (alpha := (153781554827/168140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-352906841/2000000000 : ℝ)*X 0 0+(5438018053/10000000000 : ℝ)*X 0 1+(5207924157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351023111/10000000000 : ℝ)*X 1 0+(-1882560811/10000000000 : ℝ)*X 1 1+(520792481/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337755881/2500000000 : ℝ)*X 2 0+(162747613/312500000 : ℝ)*X 2 1+(-941280923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2117994297/5000000000 : ℝ)*X 0 0+(1984462507/5000000000 : ℝ)*X 0 1+(2258629237/5000000000 : ℝ)*X 0 2+(2117994297/5000000000 : ℝ)*X 1 0+(1984462507/5000000000 : ℝ)*X 1 1+(2258629237/5000000000 : ℝ)*X 1 2+(2117994297/5000000000 : ℝ)*X 2 0+(1984462507/5000000000 : ℝ)*X 2 1+(2258629237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-220571473/1250000000 : ℝ)*X 0 0+(41674263/80000000 : ℝ)*X 0 1+(217465931/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290043667/10000000000 : ℝ)*X 1 0+(-1653837867/10000000000 : ℝ)*X 1 1+(84947647/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330627773/625000000 : ℝ)*X 2 0+(679581309/1250000000 : ℝ)*X 2 1+(-103364713/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2118039829/5000000000 : ℝ)*X 0 0+(225701107/500000000 : ℝ)*X 0 1+(1986093921/5000000000 : ℝ)*X 0 2+(2118039829/5000000000 : ℝ)*X 1 0+(225701107/500000000 : ℝ)*X 1 1+(1986093921/5000000000 : ℝ)*X 1 2+(2118039829/5000000000 : ℝ)*X 2 0+(225701107/500000000 : ℝ)*X 2 1+(1986093921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1584_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3680526066162950636049069363/525437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122017483/25000000000000 : ℝ)*(base19) + (77498437/12500000000000 : ℝ)*(base23) + (7312587/100000000000000 : ℝ)*(upper2) + (11178743/100000000000000 : ℝ)*(lower5) + (771227326252787/25000000000000 : ℝ)*(major0) + (771227326252787/25000000000000 : ℝ)*(major1) + (771227326252787/25000000000000 : ℝ)*(major2) + (2173036915347443/50000000000000 : ℝ)*(sp0) + (1086523994076577/25000000000000 : ℝ)*(sp1) + (2173038392958441/50000000000000 : ℝ)*(sp2) + (22796432548263/1250000000000 : ℝ)*(sp3) + (11316840677/50000000000000 : ℝ)*(sp4) + (19058471861/100000000000000 : ℝ)*(sp6) + (7308295389/100000000000000 : ℝ)*(sp7) + (1823721912156429/100000000000000 : ℝ)*(f.failure) + (54326205804703/1250000000000 : ℝ)*(f.sum) + (355907617987/1050875000000000000000000000 : ℝ)*base66 + (6730684325872101879/2101750000000000000000000000000000 : ℝ)*base68 + (30090757510960601879/2101750000000000000000000000000000 : ℝ)*base70 + (14632007861890601879/2101750000000000000000000000000000 : ℝ)*base72 + (1282981590993/2101750000000000000000000000 : ℝ)*base73 + (27091930227809601879/2101750000000000000000000000000000 : ℝ)*base76 + (14924530739860398121/2101750000000000000000000000000000 : ℝ)*base77 + (14052054779465101879/2101750000000000000000000000000000 : ℝ)*base80 + (2383778693307/840700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (51202681/10000000000000000000000 : ℝ)*base89 + (51202681/10000000000000000000000 : ℝ)*base91 + (51202681/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18192844525015417941554459409/2101750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3114127/50000000000000 : ℝ)*(base8) + (370426997/50000000000000 : ℝ)*(base15) + (240569673/100000000000000 : ℝ)*(lower2) + (17378729/50000000000000 : ℝ)*(lower4) + (3121899385508041/100000000000000 : ℝ)*(major0) + (3121899385508041/100000000000000 : ℝ)*(major1) + (1560949692754021/50000000000000 : ℝ)*(major2) + (33790233/781250000000 : ℝ)*(sp1) + (8947689833/20000000000000 : ℝ)*(sp2) + (770866883/25000000000000 : ℝ)*(sp3) + (1099552236354923/25000000000000 : ℝ)*(sp4) + (137443871426379/3125000000000 : ℝ)*(sp5) + (4398164213198781/100000000000000 : ℝ)*(sp6) + (369117289473147/20000000000000 : ℝ)*(sp7) + (1845589530833267/100000000000000 : ℝ)*(f.failure) + (2199104475823973/50000000000000 : ℝ)*(f.sum) + (112313387258899/16814000000000000000000000000 : ℝ)*base66 + (23714009835467430197/8407000000000000000000000000000000 : ℝ)*base68 + (29519887854675791857/4203500000000000000000000000000000 : ℝ)*base70 + (30729446456877430197/8407000000000000000000000000000000 : ℝ)*base72 + (18837601997271/16814000000000000000000000000 : ℝ)*base74 + (29733579792250208143/4203500000000000000000000000000000 : ℝ)*base75 + (60928223340686930197/8407000000000000000000000000000000 : ℝ)*base78 + (21681422663084930197/8407000000000000000000000000000000 : ℝ)*base80 + (4081716697307/8407000000000000000000000000 : ℝ)*base81 + (6912263/10000000000000000000000 : ℝ)*base89 + (6912263/10000000000000000000000 : ℝ)*base91 + (93087737/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1584_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (493/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1584_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1584_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (493/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1584_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1584_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1584_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4663/1024 : ℝ) ≤ p) (hpb : p ≤ (4665/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169154589/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (681/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (493/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1584_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

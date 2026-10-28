-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:02.821963+00:00
-- url     : https://prove2.me/submissions/6e34ac87-fe9c-46c3-aca4-2d403349ed16

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
theorem support_rectangle_w1228_s3_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123462137/10000000000 : ℝ)*x 0 + (5420900821/10000000000 : ℝ)*x 1 + (13098811/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123462137/10000000000 : ℝ)^8421 ≤ (12905844547303/100000000000000 : ℝ)^6373 := by
    have hnat : (2123462137 : ℕ)^8421*100000000000000^6373 ≤ 12905844547303^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123462137 10000000000 12905844547303 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420900821/10000000000 : ℝ)^8421 ≤ (1391437893793/3125000000000 : ℝ)^6373 := by
    have hnat : (5420900821 : ℕ)^8421*3125000000000^6373 ≤ 1391437893793^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420900821 10000000000 1391437893793 3125000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13098811/25000000 : ℝ)^8421 ≤ (42568142836977/100000000000000 : ℝ)^6373 := by
    have hnat : (13098811 : ℕ)^8421*100000000000000^6373 ≤ 42568142836977^6373*25000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13098811 25000000 42568142836977 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123462137/10000000000 : ℝ), (5420900821/10000000000 : ℝ), (13098811/25000000 : ℝ)] ![(12905844547303/100000000000000 : ℝ), (1391437893793/3125000000000 : ℝ), (42568142836977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123462137/10000000000 : ℝ)|^8421 ≤ (12905844547303/100000000000000 : ℝ)^6373
        have hw : |(-2123462137/10000000000 : ℝ)|=(2123462137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420900821/10000000000 : ℝ)|^8421 ≤ (1391437893793/3125000000000 : ℝ)^6373
        have hw : |(5420900821/10000000000 : ℝ)|=(5420900821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13098811/25000000 : ℝ)|^8421 ≤ (42568142836977/100000000000000 : ℝ)^6373
        have hw : |(13098811/25000000 : ℝ)|=(13098811/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (107036019/200000000 : ℝ)*x 0 + (-2216013319/10000000000 : ℝ)*x 1 + (261976229/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107036019/200000000 : ℝ)^8421 ≤ (43777590968449/100000000000000 : ℝ)^6373 := by
    have hnat : (107036019 : ℕ)^8421*100000000000000^6373 ≤ 43777590968449^6373*200000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107036019 200000000 43777590968449 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216013319/10000000000 : ℝ)^8421 ≤ (3413566061033/25000000000000 : ℝ)^6373 := by
    have hnat : (2216013319 : ℕ)^8421*25000000000000^6373 ≤ 3413566061033^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216013319 10000000000 3413566061033 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261976229/500000000 : ℝ)^8421 ≤ (10642036192331/25000000000000 : ℝ)^6373 := by
    have hnat : (261976229 : ℕ)^8421*25000000000000^6373 ≤ 10642036192331^6373*500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261976229 500000000 10642036192331 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107036019/200000000 : ℝ), (-2216013319/10000000000 : ℝ), (261976229/500000000 : ℝ)] ![(43777590968449/100000000000000 : ℝ), (3413566061033/25000000000000 : ℝ), (10642036192331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107036019/200000000 : ℝ)|^8421 ≤ (43777590968449/100000000000000 : ℝ)^6373
        have hw : |(107036019/200000000 : ℝ)|=(107036019/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2216013319/10000000000 : ℝ)|^8421 ≤ (3413566061033/25000000000000 : ℝ)^6373
        have hw : |(-2216013319/10000000000 : ℝ)|=(2216013319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261976229/500000000 : ℝ)|^8421 ≤ (10642036192331/25000000000000 : ℝ)^6373
        have hw : |(261976229/500000000 : ℝ)|=(261976229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351800829/10000000000 : ℝ)*x 0 + (5239524983/10000000000 : ℝ)*x 1 + (-554003237/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351800829/10000000000 : ℝ)^8421 ≤ (21888794830301/50000000000000 : ℝ)^6373 := by
    have hnat : (5351800829 : ℕ)^8421*50000000000000^6373 ≤ 21888794830301^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351800829 10000000000 21888794830301 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239524983/10000000000 : ℝ)^8421 ≤ (21284074547817/50000000000000 : ℝ)^6373 := by
    have hnat : (5239524983 : ℕ)^8421*50000000000000^6373 ≤ 21284074547817^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239524983 10000000000 21284074547817 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554003237/2500000000 : ℝ)^8421 ≤ (6827130611779/50000000000000 : ℝ)^6373 := by
    have hnat : (554003237 : ℕ)^8421*50000000000000^6373 ≤ 6827130611779^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554003237 2500000000 6827130611779 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351800829/10000000000 : ℝ), (5239524983/10000000000 : ℝ), (-554003237/2500000000 : ℝ)] ![(21888794830301/50000000000000 : ℝ), (21284074547817/50000000000000 : ℝ), (6827130611779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351800829/10000000000 : ℝ)|^8421 ≤ (21888794830301/50000000000000 : ℝ)^6373
        have hw : |(5351800829/10000000000 : ℝ)|=(5351800829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239524983/10000000000 : ℝ)|^8421 ≤ (21284074547817/50000000000000 : ℝ)^6373
        have hw : |(5239524983/10000000000 : ℝ)|=(5239524983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554003237/2500000000 : ℝ)|^8421 ≤ (6827130611779/50000000000000 : ℝ)^6373
        have hw : |(-554003237/2500000000 : ℝ)|=(554003237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350928971/10000000000 : ℝ)*x 0 + (4171228441/10000000000 : ℝ)*x 1 + (2269083883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350928971/10000000000 : ℝ)^8421 ≤ (16649770604973/50000000000000 : ℝ)^6373 := by
    have hnat : (4350928971 : ℕ)^8421*50000000000000^6373 ≤ 16649770604973^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350928971 10000000000 16649770604973 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171228441/10000000000 : ℝ)^8421 ≤ (31494421211159/100000000000000 : ℝ)^6373 := by
    have hnat : (4171228441 : ℕ)^8421*100000000000000^6373 ≤ 31494421211159^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171228441 10000000000 31494421211159 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269083883/5000000000 : ℝ)^8421 ≤ (17603018781023/50000000000000 : ℝ)^6373 := by
    have hnat : (2269083883 : ℕ)^8421*50000000000000^6373 ≤ 17603018781023^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269083883 5000000000 17603018781023 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350928971/10000000000 : ℝ), (4171228441/10000000000 : ℝ), (2269083883/5000000000 : ℝ)] ![(16649770604973/50000000000000 : ℝ), (31494421211159/100000000000000 : ℝ), (17603018781023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350928971/10000000000 : ℝ)|^8421 ≤ (16649770604973/50000000000000 : ℝ)^6373
        have hw : |(4350928971/10000000000 : ℝ)|=(4350928971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171228441/10000000000 : ℝ)|^8421 ≤ (31494421211159/100000000000000 : ℝ)^6373
        have hw : |(4171228441/10000000000 : ℝ)|=(4171228441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2269083883/5000000000 : ℝ)|^8421 ≤ (17603018781023/50000000000000 : ℝ)^6373
        have hw : |(2269083883/5000000000 : ℝ)|=(2269083883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061738439/5000000000 : ℝ)*x 0 + (2620094827/5000000000 : ℝ)*x 1 + (5420231869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061738439/5000000000 : ℝ)^8421 ≤ (6452981465117/50000000000000 : ℝ)^6373 := by
    have hnat : (1061738439 : ℕ)^8421*50000000000000^6373 ≤ 6452981465117^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061738439 5000000000 6452981465117 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620094827/5000000000 : ℝ)^8421 ≤ (21287642328809/50000000000000 : ℝ)^6373 := by
    have hnat : (2620094827 : ℕ)^8421*50000000000000^6373 ≤ 21287642328809^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620094827 5000000000 21287642328809 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420231869/10000000000 : ℝ)^8421 ≤ (22259376201921/50000000000000 : ℝ)^6373 := by
    have hnat : (5420231869 : ℕ)^8421*50000000000000^6373 ≤ 22259376201921^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420231869 10000000000 22259376201921 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061738439/5000000000 : ℝ), (2620094827/5000000000 : ℝ), (5420231869/10000000000 : ℝ)] ![(6452981465117/50000000000000 : ℝ), (21287642328809/50000000000000 : ℝ), (22259376201921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061738439/5000000000 : ℝ)|^8421 ≤ (6452981465117/50000000000000 : ℝ)^6373
        have hw : |(-1061738439/5000000000 : ℝ)|=(1061738439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620094827/5000000000 : ℝ)|^8421 ≤ (21287642328809/50000000000000 : ℝ)^6373
        have hw : |(2620094827/5000000000 : ℝ)|=(2620094827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420231869/10000000000 : ℝ)|^8421 ≤ (22259376201921/50000000000000 : ℝ)^6373
        have hw : |(5420231869/10000000000 : ℝ)|=(5420231869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652785293/5000000000 : ℝ)*x 0 + (-508826611/2500000000 : ℝ)*x 1 + (2710116069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652785293/5000000000 : ℝ)^8421 ≤ (2704912364377/6250000000000 : ℝ)^6373 := by
    have hnat : (2652785293 : ℕ)^8421*6250000000000^6373 ≤ 2704912364377^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652785293 5000000000 2704912364377 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508826611/2500000000 : ℝ)^8421 ≤ (12202646829611/100000000000000 : ℝ)^6373 := by
    have hnat : (508826611 : ℕ)^8421*100000000000000^6373 ≤ 12202646829611^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508826611 2500000000 12202646829611 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710116069/5000000000 : ℝ)^8421 ≤ (8903751064653/20000000000000 : ℝ)^6373 := by
    have hnat : (2710116069 : ℕ)^8421*20000000000000^6373 ≤ 8903751064653^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710116069 5000000000 8903751064653 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652785293/5000000000 : ℝ), (-508826611/2500000000 : ℝ), (2710116069/5000000000 : ℝ)] ![(2704912364377/6250000000000 : ℝ), (12202646829611/100000000000000 : ℝ), (8903751064653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652785293/5000000000 : ℝ)|^8421 ≤ (2704912364377/6250000000000 : ℝ)^6373
        have hw : |(2652785293/5000000000 : ℝ)|=(2652785293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508826611/2500000000 : ℝ)|^8421 ≤ (12202646829611/100000000000000 : ℝ)^6373
        have hw : |(-508826611/2500000000 : ℝ)|=(508826611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710116069/5000000000 : ℝ)|^8421 ≤ (8903751064653/20000000000000 : ℝ)^6373
        have hw : |(2710116069/5000000000 : ℝ)|=(2710116069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305571379/10000000000 : ℝ)*x 0 + (5420232027/10000000000 : ℝ)*x 1 + (-1017652759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305571379/10000000000 : ℝ)^8421 ≤ (5409825797179/12500000000000 : ℝ)^6373 := by
    have hnat : (5305571379 : ℕ)^8421*12500000000000^6373 ≤ 5409825797179^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305571379 10000000000 5409825797179 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420232027/10000000000 : ℝ)^8421 ≤ (11129688529649/25000000000000 : ℝ)^6373 := by
    have hnat : (5420232027 : ℕ)^8421*25000000000000^6373 ≤ 11129688529649^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420232027 10000000000 11129688529649 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017652759/5000000000 : ℝ)^8421 ≤ (2440527898737/20000000000000 : ℝ)^6373 := by
    have hnat : (1017652759 : ℕ)^8421*20000000000000^6373 ≤ 2440527898737^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017652759 5000000000 2440527898737 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305571379/10000000000 : ℝ), (5420232027/10000000000 : ℝ), (-1017652759/5000000000 : ℝ)] ![(5409825797179/12500000000000 : ℝ), (11129688529649/25000000000000 : ℝ), (2440527898737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305571379/10000000000 : ℝ)|^8421 ≤ (5409825797179/12500000000000 : ℝ)^6373
        have hw : |(5305571379/10000000000 : ℝ)|=(5305571379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420232027/10000000000 : ℝ)|^8421 ≤ (11129688529649/25000000000000 : ℝ)^6373
        have hw : |(5420232027/10000000000 : ℝ)|=(5420232027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017652759/5000000000 : ℝ)|^8421 ≤ (2440527898737/20000000000000 : ℝ)^6373
        have hw : |(-1017652759/5000000000 : ℝ)|=(1017652759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s3_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350958297/10000000000 : ℝ)*x 0 + (4536822871/10000000000 : ℝ)*x 1 + (417258041/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350958297/10000000000 : ℝ)^8421 ≤ (8324959445343/25000000000000 : ℝ)^6373 := by
    have hnat : (4350958297 : ℕ)^8421*25000000000000^6373 ≤ 8324959445343^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350958297 10000000000 8324959445343 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4536822871/10000000000 : ℝ)^8421 ≤ (35192252013647/100000000000000 : ℝ)^6373 := by
    have hnat : (4536822871 : ℕ)^8421*100000000000000^6373 ≤ 35192252013647^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536822871 10000000000 35192252013647 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417258041/1000000000 : ℝ)^8421 ≤ (15753955090041/50000000000000 : ℝ)^6373 := by
    have hnat : (417258041 : ℕ)^8421*50000000000000^6373 ≤ 15753955090041^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417258041 1000000000 15753955090041 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350958297/10000000000 : ℝ), (4536822871/10000000000 : ℝ), (417258041/1000000000 : ℝ)] ![(8324959445343/25000000000000 : ℝ), (35192252013647/100000000000000 : ℝ), (15753955090041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350958297/10000000000 : ℝ)|^8421 ≤ (8324959445343/25000000000000 : ℝ)^6373
        have hw : |(4350958297/10000000000 : ℝ)|=(4350958297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4536822871/10000000000 : ℝ)|^8421 ≤ (35192252013647/100000000000000 : ℝ)^6373
        have hw : |(4536822871/10000000000 : ℝ)|=(4536822871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417258041/1000000000 : ℝ)|^8421 ≤ (15753955090041/50000000000000 : ℝ)^6373
        have hw : |(417258041/1000000000 : ℝ)|=(417258041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (87/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7357/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (813/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (813/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (813/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (813/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (813/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (813/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4721/50000 : ℝ) ^ (2105/512 : ℝ) ≤ (1222311158567607/20000000000000000000 : ℝ) := by
    have hpowers : (4721/50000 : ℝ)^2105 ≤ (1222311158567607/20000000000000000000 : ℝ)^512 := by
      have hnat : (4721 : ℕ)^2105*20000000000000000000^512 ≤ 1222311158567607^512*50000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4721 50000 1222311158567607 20000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4721/50000 : ℝ)) (X := (1222311158567607/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (813/5000 : ℝ) ^ (2105/512 : ℝ) ≤ (3568927382441063/6250000000000000000 : ℝ) := by
    have hpowers : (813/5000 : ℝ)^2105 ≤ (3568927382441063/6250000000000000000 : ℝ)^512 := by
      have hnat : (813 : ℕ)^2105*6250000000000000000^512 ≤ 3568927382441063^512*5000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813 5000 3568927382441063 6250000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (813/5000 : ℝ)) (X := (3568927382441063/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001222311158567607/10000000000000000000 : ℝ) ≤ (500014864474363/500000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (10001222311158567607/10000000000000000000 : ℝ)^512 ≤ (500014864474363/500000000000000 : ℝ)^2105 := by
      have hnat : (10001222311158567607 : ℕ)^512*500000000000000^2105 ≤ 500014864474363^2105*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001222311158567607 10000000000000000000 500014864474363 500000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014864474363/500000000000000 : ℝ)) (X := (10001222311158567607/10000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100063214393911895043/100000000000000000000 : ℝ) ≤ (2500384299653927/2500000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (100063214393911895043/100000000000000000000 : ℝ)^512 ≤ (2500384299653927/2500000000000000 : ℝ)^2105 := by
      have hnat : (100063214393911895043 : ℕ)^512*2500000000000000^2105 ≤ 2500384299653927^2105*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100063214393911895043 100000000000000000000 2500384299653927 2500000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500384299653927/2500000000000000 : ℝ)) (X := (100063214393911895043/100000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3128568927382441063/3125000000000000000 : ℝ) ≤ (2500694276936039/2500000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (3128568927382441063/3125000000000000000 : ℝ)^512 ≤ (2500694276936039/2500000000000000 : ℝ)^2105 := by
      have hnat : (3128568927382441063 : ℕ)^512*2500000000000000^2105 ≤ 2500694276936039^2105*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128568927382441063 3125000000000000000 2500694276936039 2500000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500694276936039/2500000000000000 : ℝ)) (X := (3128568927382441063/3125000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1222311158567607/20000000000000000000 : ℝ) ≤ ((8519826559467815831/8522500000000000000 : ℝ)+2*(4843395033/2663281250000 : ℝ)*(4721/50000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (8519826559467815831/8522500000000000000 : ℝ)+2*(4843395033/2663281250000 : ℝ)*(4721/50000 : ℝ)=(500014864474363/500000000000000 : ℝ) by norm_num, show 1+2*(1222311158567607/20000000000000000000 : ℝ)=(10001222311158567607/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3568927382441063/6250000000000000000 : ℝ)+(1222311158567607/20000000000000000000 : ℝ) ≤ ((8519826559467815831/8522500000000000000 : ℝ)+(4843395033/2663281250000 : ℝ)*((813/5000 : ℝ)+(4721/50000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (8519826559467815831/8522500000000000000 : ℝ)+(4843395033/2663281250000 : ℝ)*((813/5000 : ℝ)+(4721/50000 : ℝ))=(2500384299653927/2500000000000000 : ℝ) by norm_num, show 1+(3568927382441063/6250000000000000000 : ℝ)+(1222311158567607/20000000000000000000 : ℝ)=(100063214393911895043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3568927382441063/6250000000000000000 : ℝ) ≤ ((8519826559467815831/8522500000000000000 : ℝ)+2*(4843395033/2663281250000 : ℝ)*(813/5000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (8519826559467815831/8522500000000000000 : ℝ)+2*(4843395033/2663281250000 : ℝ)*(813/5000 : ℝ)=(2500694276936039/2500000000000000 : ℝ) by norm_num, show 1+2*(3568927382441063/6250000000000000000 : ℝ)=(3128568927382441063/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8519826559467815831/8522500000000000000 : ℝ)*(X 1 0+X 2 0)+(4843395033/2663281250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (4721/50000 : ℝ)) (hi := (813/5000 : ℝ)) (c := (8519826559467815831/8522500000000000000 : ℝ)) (alpha := (4843395033/2663281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8519826559467815831/8522500000000000000 : ℝ)*(X 0 1+X 2 1)+(4843395033/2663281250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (4721/50000 : ℝ)) (hi := (813/5000 : ℝ)) (c := (8519826559467815831/8522500000000000000 : ℝ)) (alpha := (4843395033/2663281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8519826559467815831/8522500000000000000 : ℝ)*(X 0 2+X 1 2)+(4843395033/2663281250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (4721/50000 : ℝ)) (hi := (813/5000 : ℝ)) (c := (8519826559467815831/8522500000000000000 : ℝ)) (alpha := (4843395033/2663281250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2123462137/10000000000 : ℝ)*X 0 0+(5420900821/10000000000 : ℝ)*X 0 1+(13098811/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107036019/200000000 : ℝ)*X 1 0+(-2216013319/10000000000 : ℝ)*X 1 1+(261976229/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351800829/10000000000 : ℝ)*X 2 0+(5239524983/10000000000 : ℝ)*X 2 1+(-554003237/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350928971/10000000000 : ℝ)*X 0 0+(4171228441/10000000000 : ℝ)*X 0 1+(2269083883/5000000000 : ℝ)*X 0 2+(4350928971/10000000000 : ℝ)*X 1 0+(4171228441/10000000000 : ℝ)*X 1 1+(2269083883/5000000000 : ℝ)*X 1 2+(4350928971/10000000000 : ℝ)*X 2 0+(4171228441/10000000000 : ℝ)*X 2 1+(2269083883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1061738439/5000000000 : ℝ)*X 0 0+(2620094827/5000000000 : ℝ)*X 0 1+(5420231869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652785293/5000000000 : ℝ)*X 1 0+(-508826611/2500000000 : ℝ)*X 1 1+(2710116069/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305571379/10000000000 : ℝ)*X 2 0+(5420232027/10000000000 : ℝ)*X 2 1+(-1017652759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350958297/10000000000 : ℝ)*X 0 0+(4536822871/10000000000 : ℝ)*X 0 1+(417258041/1000000000 : ℝ)*X 0 2+(4350958297/10000000000 : ℝ)*X 1 0+(4536822871/10000000000 : ℝ)*X 1 1+(417258041/1000000000 : ℝ)*X 1 2+(4350958297/10000000000 : ℝ)*X 2 0+(4536822871/10000000000 : ℝ)*X 2 1+(417258041/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1275306760383045502125275547/213062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356927737/50000000000000 : ℝ)*(base19) + (72554647/20000000000000 : ℝ)*(base23) + (70023359/50000000000000 : ℝ)*(lower2) + (14190959/25000000000000 : ℝ)*(upper5) + (2059677958000093/50000000000000 : ℝ)*(major0) + (2059677958000093/50000000000000 : ℝ)*(major1) + (2059677958000093/50000000000000 : ℝ)*(major2) + (5513419822061581/100000000000000 : ℝ)*(sp0) + (22053773622221/400000000000 : ℝ)*(sp1) + (275672391888349/5000000000000 : ℝ)*(sp2) + (2725254834183573/100000000000000 : ℝ)*(sp3) + (14189239317/50000000000000 : ℝ)*(sp4) + (408112949/10000000000000 : ℝ)*(sp5) + (4298878299/50000000000000 : ℝ)*(sp7) + (2725263431940171/100000000000000 : ℝ)*(f.failure) + (1102689640108043/20000000000000 : ℝ)*(f.sum) + (35960809424341/4261250000000000000000000000 : ℝ)*base65 + (1325094654365832531/60875000000000000000000000000000 : ℝ)*base68 + (204310008824832531/60875000000000000000000000000000 : ℝ)*base70 + (176577744211707531/60875000000000000000000000000000 : ℝ)*base72 + (52577214642181/17045000000000000000000000000 : ℝ)*base74 + (464010750129582531/60875000000000000000000000000000 : ℝ)*base76 + (118390849069207531/60875000000000000000000000000000 : ℝ)*base78 + (116126328410957531/60875000000000000000000000000000 : ℝ)*base80 + (6376841318527/8522500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8328887/2500000000000000000000 : ℝ)*base90 + (8328887/2500000000000000000000 : ℝ)*base92 + (8328887/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2106673184317303839182651697/213062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (347180381/50000000000000 : ℝ)*(base19) + (975114561/50000000000000 : ℝ)*(base23) + (2019519/625000000000 : ℝ)*(upper3) + (200863/625000000000 : ℝ)*(lower4) + (10899821/25000000000000 : ℝ)*(upper5) + (2074920827210829/50000000000000 : ℝ)*(major0) + (2074920827210829/50000000000000 : ℝ)*(major1) + (2074920827210829/50000000000000 : ℝ)*(major2) + (1996145353/25000000000000 : ℝ)*(sp1) + (24944360127/50000000000000 : ℝ)*(sp2) + (2777125470455553/50000000000000 : ℝ)*(sp4) + (1388560565492233/25000000000000 : ℝ)*(sp5) + (5554199101961729/100000000000000 : ℝ)*(sp6) + (1372716019173049/50000000000000 : ℝ)*(sp7) + (1372716019173049/50000000000000 : ℝ)*(f.failure) + (2777125470455553/50000000000000 : ℝ)*(f.sum) + (29404149427841/8522500000000000000000000000 : ℝ)*base65 + (380929469384859443/60875000000000000000000000000000 : ℝ)*base68 + (559236764640359443/60875000000000000000000000000000 : ℝ)*base70 + (286580369326140557/60875000000000000000000000000000 : ℝ)*base71 + (38388205375549/8522500000000000000000000000 : ℝ)*base74 + (372460483014609443/60875000000000000000000000000000 : ℝ)*base76 + (144601474615734443/60875000000000000000000000000000 : ℝ)*base78 + (849335832994265557/60875000000000000000000000000000 : ℝ)*base79 + (6698036071539/8522500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11960547/1250000000000000000000 : ℝ)*base89 + (11960547/1250000000000000000000 : ℝ)*base91 + (11960547/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1228_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (87/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1228_s4_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1062921069/5000000000 : ℝ)*x 0 + (2699033881/5000000000 : ℝ)*x 1 + (210431931/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062921069/5000000000 : ℝ)^8421 ≤ (6462480712937/50000000000000 : ℝ)^6373 := by
    have hnat : (1062921069 : ℕ)^8421*50000000000000^6373 ≤ 6462480712937^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062921069 5000000000 6462480712937 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699033881/5000000000 : ℝ)^8421 ≤ (22139183138027/50000000000000 : ℝ)^6373 := by
    have hnat : (2699033881 : ℕ)^8421*50000000000000^6373 ≤ 22139183138027^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699033881 5000000000 22139183138027 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210431931/400000000 : ℝ)^8421 ≤ (42796672283409/100000000000000 : ℝ)^6373 := by
    have hnat : (210431931 : ℕ)^8421*100000000000000^6373 ≤ 42796672283409^6373*400000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210431931 400000000 42796672283409 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1062921069/5000000000 : ℝ), (2699033881/5000000000 : ℝ), (210431931/400000000 : ℝ)] ![(6462480712937/50000000000000 : ℝ), (22139183138027/50000000000000 : ℝ), (42796672283409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1062921069/5000000000 : ℝ)|^8421 ≤ (6462480712937/50000000000000 : ℝ)^6373
        have hw : |(-1062921069/5000000000 : ℝ)|=(1062921069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699033881/5000000000 : ℝ)|^8421 ≤ (22139183138027/50000000000000 : ℝ)^6373
        have hw : |(2699033881/5000000000 : ℝ)|=(2699033881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210431931/400000000 : ℝ)|^8421 ≤ (42796672283409/100000000000000 : ℝ)^6373
        have hw : |(210431931/400000000 : ℝ)|=(210431931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346052713/10000000000 : ℝ)*x 0 + (-2195544079/10000000000 : ℝ)*x 1 + (1052159641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346052713/10000000000 : ℝ)^8421 ≤ (43715470982869/100000000000000 : ℝ)^6373 := by
    have hnat : (5346052713 : ℕ)^8421*100000000000000^6373 ≤ 43715470982869^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346052713 10000000000 43715470982869 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195544079/10000000000 : ℝ)^8421 ≤ (337196436751/2500000000000 : ℝ)^6373 := by
    have hnat : (2195544079 : ℕ)^8421*2500000000000^6373 ≤ 337196436751^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195544079 10000000000 337196436751 2500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052159641/2000000000 : ℝ)^8421 ≤ (21398335765481/50000000000000 : ℝ)^6373 := by
    have hnat : (1052159641 : ℕ)^8421*50000000000000^6373 ≤ 21398335765481^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052159641 2000000000 21398335765481 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346052713/10000000000 : ℝ), (-2195544079/10000000000 : ℝ), (1052159641/2000000000 : ℝ)] ![(43715470982869/100000000000000 : ℝ), (337196436751/2500000000000 : ℝ), (21398335765481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346052713/10000000000 : ℝ)|^8421 ≤ (43715470982869/100000000000000 : ℝ)^6373
        have hw : |(5346052713/10000000000 : ℝ)|=(5346052713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195544079/10000000000 : ℝ)|^8421 ≤ (337196436751/2500000000000 : ℝ)^6373
        have hw : |(-2195544079/10000000000 : ℝ)|=(2195544079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052159641/2000000000 : ℝ)|^8421 ≤ (21398335765481/50000000000000 : ℝ)^6373
        have hw : |(1052159641/2000000000 : ℝ)|=(1052159641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133651311/250000000 : ℝ)*x 0 + (20549993/39062500 : ℝ)*x 1 + (-2195544439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133651311/250000000 : ℝ)^8421 ≤ (69944748853/160000000000 : ℝ)^6373 := by
    have hnat : (133651311 : ℕ)^8421*160000000000^6373 ≤ 69944748853^6373*250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133651311 250000000 69944748853 160000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20549993/39062500 : ℝ)^8421 ≤ (42796671563209/100000000000000 : ℝ)^6373 := by
    have hnat : (20549993 : ℕ)^8421*100000000000000^6373 ≤ 42796671563209^6373*39062500^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20549993 39062500 42796671563209 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195544439/10000000000 : ℝ)^8421 ≤ (13487860392329/100000000000000 : ℝ)^6373 := by
    have hnat : (2195544439 : ℕ)^8421*100000000000000^6373 ≤ 13487860392329^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195544439 10000000000 13487860392329 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133651311/250000000 : ℝ), (20549993/39062500 : ℝ), (-2195544439/10000000000 : ℝ)] ![(69944748853/160000000000 : ℝ), (42796671563209/100000000000000 : ℝ), (13487860392329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133651311/250000000 : ℝ)|^8421 ≤ (69944748853/160000000000 : ℝ)^6373
        have hw : |(133651311/250000000 : ℝ)|=(133651311/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20549993/39062500 : ℝ)|^8421 ≤ (42796671563209/100000000000000 : ℝ)^6373
        have hw : |(20549993/39062500 : ℝ)|=(20549993/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195544439/10000000000 : ℝ)|^8421 ≤ (13487860392329/100000000000000 : ℝ)^6373
        have hw : |(-2195544439/10000000000 : ℝ)|=(2195544439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (544044437/1250000000 : ℝ)*x 0 + (4215661629/10000000000 : ℝ)*x 1 + (1123342459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544044437/1250000000 : ℝ)^8421 ≤ (2082123017767/6250000000000 : ℝ)^6373 := by
    have hnat : (544044437 : ℕ)^8421*6250000000000^6373 ≤ 2082123017767^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544044437 1250000000 2082123017767 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4215661629/10000000000 : ℝ)^8421 ≤ (1996154829221/6250000000000 : ℝ)^6373 := by
    have hnat : (4215661629 : ℕ)^8421*6250000000000^6373 ≤ 1996154829221^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215661629 10000000000 1996154829221 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123342459/2500000000 : ℝ)^8421 ≤ (34747554428223/100000000000000 : ℝ)^6373 := by
    have hnat : (1123342459 : ℕ)^8421*100000000000000^6373 ≤ 34747554428223^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123342459 2500000000 34747554428223 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544044437/1250000000 : ℝ), (4215661629/10000000000 : ℝ), (1123342459/2500000000 : ℝ)] ![(2082123017767/6250000000000 : ℝ), (1996154829221/6250000000000 : ℝ), (34747554428223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544044437/1250000000 : ℝ)|^8421 ≤ (2082123017767/6250000000000 : ℝ)^6373
        have hw : |(544044437/1250000000 : ℝ)|=(544044437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4215661629/10000000000 : ℝ)|^8421 ≤ (1996154829221/6250000000000 : ℝ)^6373
        have hw : |(4215661629/10000000000 : ℝ)|=(4215661629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123342459/2500000000 : ℝ)|^8421 ≤ (34747554428223/100000000000000 : ℝ)^6373
        have hw : |(1123342459/2500000000 : ℝ)|=(1123342459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42516973/200000000 : ℝ)*x 0 + (5261179831/10000000000 : ℝ)*x 1 + (1349421129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42516973/200000000 : ℝ)^8421 ≤ (12925013741641/100000000000000 : ℝ)^6373 := by
    have hnat : (42516973 : ℕ)^8421*100000000000000^6373 ≤ 12925013741641^6373*200000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42516973 200000000 12925013741641 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261179831/10000000000 : ℝ)^8421 ≤ (21400386885723/50000000000000 : ℝ)^6373 := by
    have hnat : (5261179831 : ℕ)^8421*50000000000000^6373 ≤ 21400386885723^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261179831 10000000000 21400386885723 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349421129/2500000000 : ℝ)^8421 ≤ (442742124751/1000000000000 : ℝ)^6373 := by
    have hnat : (1349421129 : ℕ)^8421*1000000000000^6373 ≤ 442742124751^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349421129 2500000000 442742124751 1000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42516973/200000000 : ℝ), (5261179831/10000000000 : ℝ), (1349421129/2500000000 : ℝ)] ![(12925013741641/100000000000000 : ℝ), (21400386885723/50000000000000 : ℝ), (442742124751/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42516973/200000000 : ℝ)|^8421 ≤ (12925013741641/100000000000000 : ℝ)^6373
        have hw : |(-42516973/200000000 : ℝ)|=(42516973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261179831/10000000000 : ℝ)|^8421 ≤ (21400386885723/50000000000000 : ℝ)^6373
        have hw : |(5261179831/10000000000 : ℝ)|=(5261179831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349421129/2500000000 : ℝ)|^8421 ≤ (442742124751/1000000000000 : ℝ)^6373
        have hw : |(1349421129/2500000000 : ℝ)|=(1349421129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663882831/1250000000 : ℝ)*x 0 + (-257332273/1250000000 : ℝ)*x 1 + (539768451/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663882831/1250000000 : ℝ)^8421 ≤ (43337804205717/100000000000000 : ℝ)^6373 := by
    have hnat : (663882831 : ℕ)^8421*100000000000000^6373 ≤ 43337804205717^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663882831 1250000000 43337804205717 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257332273/1250000000 : ℝ)^8421 ≤ (6193991685593/50000000000000 : ℝ)^6373 := by
    have hnat : (257332273 : ℕ)^8421*50000000000000^6373 ≤ 6193991685593^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257332273 1250000000 6193991685593 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539768451/1000000000 : ℝ)^8421 ≤ (4427421241007/10000000000000 : ℝ)^6373 := by
    have hnat : (539768451 : ℕ)^8421*10000000000000^6373 ≤ 4427421241007^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539768451 1000000000 4427421241007 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663882831/1250000000 : ℝ), (-257332273/1250000000 : ℝ), (539768451/1000000000 : ℝ)] ![(43337804205717/100000000000000 : ℝ), (6193991685593/50000000000000 : ℝ), (4427421241007/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663882831/1250000000 : ℝ)|^8421 ≤ (43337804205717/100000000000000 : ℝ)^6373
        have hw : |(663882831/1250000000 : ℝ)|=(663882831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257332273/1250000000 : ℝ)|^8421 ≤ (6193991685593/50000000000000 : ℝ)^6373
        have hw : |(-257332273/1250000000 : ℝ)|=(257332273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539768451/1000000000 : ℝ)|^8421 ≤ (4427421241007/10000000000000 : ℝ)^6373
        have hw : |(539768451/1000000000 : ℝ)|=(539768451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311062033/10000000000 : ℝ)*x 0 + (337355333/625000000 : ℝ)*x 1 + (-2058657903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311062033/10000000000 : ℝ)^8421 ≤ (43337797574697/100000000000000 : ℝ)^6373 := by
    have hnat : (5311062033 : ℕ)^8421*100000000000000^6373 ≤ 43337797574697^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311062033 10000000000 43337797574697 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337355333/625000000 : ℝ)^8421 ≤ (44274221275839/100000000000000 : ℝ)^6373 := by
    have hnat : (337355333 : ℕ)^8421*100000000000000^6373 ≤ 44274221275839^6373*625000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337355333 625000000 44274221275839 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2058657903/10000000000 : ℝ)^8421 ≤ (12387981136881/100000000000000 : ℝ)^6373 := by
    have hnat : (2058657903 : ℕ)^8421*100000000000000^6373 ≤ 12387981136881^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058657903 10000000000 12387981136881 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311062033/10000000000 : ℝ), (337355333/625000000 : ℝ), (-2058657903/10000000000 : ℝ)] ![(43337797574697/100000000000000 : ℝ), (44274221275839/100000000000000 : ℝ), (12387981136881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311062033/10000000000 : ℝ)|^8421 ≤ (43337797574697/100000000000000 : ℝ)^6373
        have hw : |(5311062033/10000000000 : ℝ)|=(5311062033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337355333/625000000 : ℝ)|^8421 ≤ (44274221275839/100000000000000 : ℝ)^6373
        have hw : |(337355333/625000000 : ℝ)|=(337355333/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2058657903/10000000000 : ℝ)|^8421 ≤ (12387981136881/100000000000000 : ℝ)^6373
        have hw : |(-2058657903/10000000000 : ℝ)|=(2058657903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s4_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870473737/2000000000 : ℝ)*x 0 + (112314957/250000000 : ℝ)*x 1 + (4216435797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870473737/2000000000 : ℝ)^8421 ≤ (8328525419379/25000000000000 : ℝ)^6373 := by
    have hnat : (870473737 : ℕ)^8421*25000000000000^6373 ≤ 8328525419379^6373*2000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870473737 2000000000 8328525419379 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112314957/250000000 : ℝ)^8421 ≤ (1085614711841/3125000000000 : ℝ)^6373 := by
    have hnat : (112314957 : ℕ)^8421*3125000000000^6373 ≤ 1085614711841^6373*250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112314957 250000000 1085614711841 3125000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216435797/10000000000 : ℝ)^8421 ≤ (31946227526969/100000000000000 : ℝ)^6373 := by
    have hnat : (4216435797 : ℕ)^8421*100000000000000^6373 ≤ 31946227526969^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216435797 10000000000 31946227526969 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870473737/2000000000 : ℝ), (112314957/250000000 : ℝ), (4216435797/10000000000 : ℝ)] ![(8328525419379/25000000000000 : ℝ), (1085614711841/3125000000000 : ℝ), (31946227526969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870473737/2000000000 : ℝ)|^8421 ≤ (8328525419379/25000000000000 : ℝ)^6373
        have hw : |(870473737/2000000000 : ℝ)|=(870473737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112314957/250000000 : ℝ)|^8421 ≤ (1085614711841/3125000000000 : ℝ)^6373
        have hw : |(112314957/250000000 : ℝ)|=(112314957/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216435797/10000000000 : ℝ)|^8421 ≤ (31946227526969/100000000000000 : ℝ)^6373
        have hw : |(4216435797/10000000000 : ℝ)|=(4216435797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (87/800 : ℝ)*pair X i i ≤ pair X i h) :
    (11329/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (87/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (87/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (87/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7357/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (87/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (87/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7357/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (87/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (87/800 : ℝ) ^ (2105/512 : ℝ) ≤ (10925580954648209/100000000000000000000 : ℝ) := by
    have hpowers : (87/800 : ℝ)^2105 ≤ (10925580954648209/100000000000000000000 : ℝ)^512 := by
      have hnat : (87 : ℕ)^2105*100000000000000000000^512 ≤ 10925580954648209^512*800^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87 800 10925580954648209 100000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87/800 : ℝ)) (X := (10925580954648209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7357/50000 : ℝ) ^ (2105/512 : ℝ) ≤ (18933810940738331/50000000000000000000 : ℝ) := by
    have hpowers : (7357/50000 : ℝ)^2105 ≤ (18933810940738331/50000000000000000000 : ℝ)^512 := by
      have hnat : (7357 : ℕ)^2105*50000000000000000000^512 ≤ 18933810940738331^512*50000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7357 50000 18933810940738331 50000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7357/50000 : ℝ)) (X := (18933810940738331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010925580954648209/50000000000000000000 : ℝ) ≤ (1000053144275499/1000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (50010925580954648209/50000000000000000000 : ℝ)^512 ≤ (1000053144275499/1000000000000000 : ℝ)^2105 := by
      have hnat : (50010925580954648209 : ℕ)^512*1000000000000000^2105 ≤ 1000053144275499^2105*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010925580954648209 50000000000000000000 1000053144275499 1000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053144275499/1000000000000000 : ℝ)) (X := (50010925580954648209/50000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048793202836124871/100000000000000000000 : ℝ) ≤ (625074161249463/625000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (100048793202836124871/100000000000000000000 : ℝ)^512 ≤ (625074161249463/625000000000000 : ℝ)^2105 := by
      have hnat : (100048793202836124871 : ℕ)^512*625000000000000^2105 ≤ 625074161249463^2105*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048793202836124871 100000000000000000000 625074161249463 625000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074161249463/625000000000000 : ℝ)) (X := (100048793202836124871/100000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018933810940738331/25000000000000000000 : ℝ) ≤ (5000920858613913/5000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (25018933810940738331/25000000000000000000 : ℝ)^512 ≤ (5000920858613913/5000000000000000 : ℝ)^2105 := by
      have hnat : (25018933810940738331 : ℕ)^512*5000000000000000^2105 ≤ 5000920858613913^2105*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018933810940738331 25000000000000000000 5000920858613913 5000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000920858613913/5000000000000000 : ℝ)) (X := (25018933810940738331/25000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10925580954648209/100000000000000000000 : ℝ) ≤ ((3837779097384431511/3839000000000000000 : ℝ)+2*(327568618209/191950000000000 : ℝ)*(87/800 : ℝ))^(2105/512 : ℝ) := by
    rw [show (3837779097384431511/3839000000000000000 : ℝ)+2*(327568618209/191950000000000 : ℝ)*(87/800 : ℝ)=(1000053144275499/1000000000000000 : ℝ) by norm_num, show 1+2*(10925580954648209/100000000000000000000 : ℝ)=(50010925580954648209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18933810940738331/50000000000000000000 : ℝ)+(10925580954648209/100000000000000000000 : ℝ) ≤ ((3837779097384431511/3839000000000000000 : ℝ)+(327568618209/191950000000000 : ℝ)*((7357/50000 : ℝ)+(87/800 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (3837779097384431511/3839000000000000000 : ℝ)+(327568618209/191950000000000 : ℝ)*((7357/50000 : ℝ)+(87/800 : ℝ))=(625074161249463/625000000000000 : ℝ) by norm_num, show 1+(18933810940738331/50000000000000000000 : ℝ)+(10925580954648209/100000000000000000000 : ℝ)=(100048793202836124871/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18933810940738331/50000000000000000000 : ℝ) ≤ ((3837779097384431511/3839000000000000000 : ℝ)+2*(327568618209/191950000000000 : ℝ)*(7357/50000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (3837779097384431511/3839000000000000000 : ℝ)+2*(327568618209/191950000000000 : ℝ)*(7357/50000 : ℝ)=(5000920858613913/5000000000000000 : ℝ) by norm_num, show 1+2*(18933810940738331/50000000000000000000 : ℝ)=(25018933810940738331/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3837779097384431511/3839000000000000000 : ℝ)*(X 1 0+X 2 0)+(327568618209/191950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (87/800 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (3837779097384431511/3839000000000000000 : ℝ)) (alpha := (327568618209/191950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3837779097384431511/3839000000000000000 : ℝ)*(X 0 1+X 2 1)+(327568618209/191950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (87/800 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (3837779097384431511/3839000000000000000 : ℝ)) (alpha := (327568618209/191950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3837779097384431511/3839000000000000000 : ℝ)*(X 0 2+X 1 2)+(327568618209/191950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (87/800 : ℝ)) (hi := (7357/50000 : ℝ)) (c := (3837779097384431511/3839000000000000000 : ℝ)) (alpha := (327568618209/191950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1062921069/5000000000 : ℝ)*X 0 0+(2699033881/5000000000 : ℝ)*X 0 1+(210431931/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346052713/10000000000 : ℝ)*X 1 0+(-2195544079/10000000000 : ℝ)*X 1 1+(1052159641/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133651311/250000000 : ℝ)*X 2 0+(20549993/39062500 : ℝ)*X 2 1+(-2195544439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544044437/1250000000 : ℝ)*X 0 0+(4215661629/10000000000 : ℝ)*X 0 1+(1123342459/2500000000 : ℝ)*X 0 2+(544044437/1250000000 : ℝ)*X 1 0+(4215661629/10000000000 : ℝ)*X 1 1+(1123342459/2500000000 : ℝ)*X 1 2+(544044437/1250000000 : ℝ)*X 2 0+(4215661629/10000000000 : ℝ)*X 2 1+(1123342459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42516973/200000000 : ℝ)*X 0 0+(5261179831/10000000000 : ℝ)*X 0 1+(1349421129/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663882831/1250000000 : ℝ)*X 1 0+(-257332273/1250000000 : ℝ)*X 1 1+(539768451/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311062033/10000000000 : ℝ)*X 2 0+(337355333/625000000 : ℝ)*X 2 1+(-2058657903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870473737/2000000000 : ℝ)*X 0 0+(112314957/250000000 : ℝ)*X 0 1+(4216435797/10000000000 : ℝ)*X 0 2+(870473737/2000000000 : ℝ)*X 1 0+(112314957/250000000 : ℝ)*X 1 1+(4216435797/10000000000 : ℝ)*X 1 2+(870473737/2000000000 : ℝ)*X 2 0+(112314957/250000000 : ℝ)*X 2 1+(4216435797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177402794837981329968134829/191950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (241779727/25000000000000 : ℝ)*(base19) + (248942987/25000000000000 : ℝ)*(base23) + (234823393/100000000000000 : ℝ)*(upper2) + (132942623/100000000000000 : ℝ)*(upper3) + (5442962891612313/100000000000000 : ℝ)*(major0) + (5442962891612313/100000000000000 : ℝ)*(major1) + (5442962891612313/100000000000000 : ℝ)*(major2) + (7284976815684253/100000000000000 : ℝ)*(sp0) + (7284995894375901/100000000000000 : ℝ)*(sp1) + (910623746408409/12500000000000 : ℝ)*(sp2) + (3600916103748529/100000000000000 : ℝ)*(sp3) + (5011452639/25000000000000 : ℝ)*(sp4) + (5894455587/100000000000000 : ℝ)*(sp6) + (12787174161/100000000000000 : ℝ)*(sp7) + (360092889092269/10000000000000 : ℝ)*(f.failure) + (910624607686851/12500000000000 : ℝ)*(f.sum) + (39572971855609/19195000000000000000000000000 : ℝ)*base65 + (5045380724586565057/383900000000000000000000000000000 : ℝ)*base68 + (2591431417723665057/383900000000000000000000000000000 : ℝ)*base70 + (2509298335318665057/383900000000000000000000000000000 : ℝ)*base72 + (18123649692911/4798750000000000000000000000 : ℝ)*base73 + (2460307775256265057/383900000000000000000000000000000 : ℝ)*base76 + (2978435981953134943/383900000000000000000000000000000 : ℝ)*base77 + (2955199584882434943/383900000000000000000000000000000 : ℝ)*base79 + (12419333630553/9597500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1110207/250000000000000000000 : ℝ)*base89 + (1110207/250000000000000000000 : ℝ)*base91 + (1110207/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1270328962176131584968289143/191950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (756997777/50000000000000 : ℝ)*(base19) + (1260993179/100000000000000 : ℝ)*(base23) + (190524763/100000000000000 : ℝ)*(upper2) + (572258693/100000000000000 : ℝ)*(upper3) + (133185673/100000000000000 : ℝ)*(upper5) + (5473392458541829/100000000000000 : ℝ)*(major0) + (5473392458541829/100000000000000 : ℝ)*(major1) + (5473392458541829/100000000000000 : ℝ)*(major2) + (2194054243/25000000000000 : ℝ)*(sp1) + (8936398019/20000000000000 : ℝ)*(sp2) + (228928886275517/3125000000000 : ℝ)*(sp4) + (7325714070604019/100000000000000 : ℝ)*(sp5) + (7325678417833269/100000000000000 : ℝ)*(sp6) + (3621060335666437/100000000000000 : ℝ)*(sp7) + (3621060335666437/100000000000000 : ℝ)*(f.failure) + (228928886275517/3125000000000 : ℝ)*(f.sum) + (99719549323247/19195000000000000000000000000 : ℝ)*base65 + (2427553618890793619/383900000000000000000000000000000 : ℝ)*base67 + (1367691597048306381/383900000000000000000000000000000 : ℝ)*base70 + (966545285621693619/383900000000000000000000000000000 : ℝ)*base71 + (1448848979851/9597500000000000000000000000 : ℝ)*base73 + (3679824648687706381/383900000000000000000000000000000 : ℝ)*base76 + (3502615432318593619/383900000000000000000000000000000 : ℝ)*base77 + (1161680634831593619/383900000000000000000000000000000 : ℝ)*base79 + (44428756223507/19195000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3217511/2500000000000000000000 : ℝ)*base89 + (3217511/2500000000000000000000 : ℝ)*base91 + (3217511/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1228_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (87/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1228_s5_0 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132894601/625000000 : ℝ)*x 0 + (26963737/50000000 : ℝ)*x 1 + (5265808859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132894601/625000000 : ℝ)^8421 ≤ (323218732361/2500000000000 : ℝ)^6373 := by
    have hnat : (132894601 : ℕ)^8421*2500000000000^6373 ≤ 323218732361^6373*625000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132894601 625000000 323218732361 2500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26963737/50000000 : ℝ)^8421 ≤ (5527588769879/12500000000000 : ℝ)^6373 := by
    have hnat : (26963737 : ℕ)^8421*12500000000000^6373 ≤ 5527588769879^6373*50000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26963737 50000000 5527588769879 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265808859/10000000000 : ℝ)^8421 ≤ (21425270268213/50000000000000 : ℝ)^6373 := by
    have hnat : (5265808859 : ℕ)^8421*50000000000000^6373 ≤ 21425270268213^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265808859 10000000000 21425270268213 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132894601/625000000 : ℝ), (26963737/50000000 : ℝ), (5265808859/10000000000 : ℝ)] ![(323218732361/2500000000000 : ℝ), (5527588769879/12500000000000 : ℝ), (21425270268213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132894601/625000000 : ℝ)|^8421 ≤ (323218732361/2500000000000 : ℝ)^6373
        have hw : |(-132894601/625000000 : ℝ)|=(132894601/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26963737/50000000 : ℝ)|^8421 ≤ (5527588769879/12500000000000 : ℝ)^6373
        have hw : |(26963737/50000000 : ℝ)|=(26963737/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265808859/10000000000 : ℝ)|^8421 ≤ (21425270268213/50000000000000 : ℝ)^6373
        have hw : |(5265808859/10000000000 : ℝ)|=(5265808859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_1 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534470801/1000000000 : ℝ)*x 0 + (-1095347999/5000000000 : ℝ)*x 1 + (2632904429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534470801/1000000000 : ℝ)^8421 ≤ (43700942157821/100000000000000 : ℝ)^6373 := by
    have hnat : (534470801 : ℕ)^8421*100000000000000^6373 ≤ 43700942157821^6373*1000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534470801 1000000000 43700942157821 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095347999/5000000000 : ℝ)^8421 ≤ (1344851730013/10000000000000 : ℝ)^6373 := by
    have hnat : (1095347999 : ℕ)^8421*10000000000000^6373 ≤ 1344851730013^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095347999 5000000000 1344851730013 10000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632904429/5000000000 : ℝ)^8421 ≤ (42850540525673/100000000000000 : ℝ)^6373 := by
    have hnat : (2632904429 : ℕ)^8421*100000000000000^6373 ≤ 42850540525673^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632904429 5000000000 42850540525673 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534470801/1000000000 : ℝ), (-1095347999/5000000000 : ℝ), (2632904429/5000000000 : ℝ)] ![(43700942157821/100000000000000 : ℝ), (1344851730013/10000000000000 : ℝ), (42850540525673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534470801/1000000000 : ℝ)|^8421 ≤ (43700942157821/100000000000000 : ℝ)^6373
        have hw : |(534470801/1000000000 : ℝ)|=(534470801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1095347999/5000000000 : ℝ)|^8421 ≤ (1344851730013/10000000000000 : ℝ)^6373
        have hw : |(-1095347999/5000000000 : ℝ)|=(1095347999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632904429/5000000000 : ℝ)|^8421 ≤ (42850540525673/100000000000000 : ℝ)^6373
        have hw : |(2632904429/5000000000 : ℝ)|=(2632904429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_2 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344708011/10000000000 : ℝ)*x 0 + (658226107/1250000000 : ℝ)*x 1 + (-2190695999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344708011/10000000000 : ℝ)^8421 ≤ (349607537349/800000000000 : ℝ)^6373 := by
    have hnat : (5344708011 : ℕ)^8421*800000000000^6373 ≤ 349607537349^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344708011 10000000000 349607537349 800000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658226107/1250000000 : ℝ)^8421 ≤ (5356317563021/12500000000000 : ℝ)^6373 := by
    have hnat : (658226107 : ℕ)^8421*12500000000000^6373 ≤ 5356317563021^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658226107 1250000000 5356317563021 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190695999/10000000000 : ℝ)^8421 ≤ (13448517308241/100000000000000 : ℝ)^6373 := by
    have hnat : (2190695999 : ℕ)^8421*100000000000000^6373 ≤ 13448517308241^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190695999 10000000000 13448517308241 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344708011/10000000000 : ℝ), (658226107/1250000000 : ℝ), (-2190695999/10000000000 : ℝ)] ![(349607537349/800000000000 : ℝ), (5356317563021/12500000000000 : ℝ), (13448517308241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344708011/10000000000 : ℝ)|^8421 ≤ (349607537349/800000000000 : ℝ)^6373
        have hw : |(5344708011/10000000000 : ℝ)|=(5344708011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658226107/1250000000 : ℝ)|^8421 ≤ (5356317563021/12500000000000 : ℝ)^6373
        have hw : |(658226107/1250000000 : ℝ)|=(658226107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190695999/10000000000 : ℝ)|^8421 ≤ (13448517308241/100000000000000 : ℝ)^6373
        have hw : |(-2190695999/10000000000 : ℝ)|=(2190695999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_3 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176316423/5000000000 : ℝ)*x 0 + (4226076211/10000000000 : ℝ)*x 1 + (2241442043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176316423/5000000000 : ℝ)^8421 ≤ (6663354684637/20000000000000 : ℝ)^6373 := by
    have hnat : (2176316423 : ℕ)^8421*20000000000000^6373 ≤ 6663354684637^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176316423 5000000000 6663354684637 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226076211/10000000000 : ℝ)^8421 ≤ (8010694197231/25000000000000 : ℝ)^6373 := by
    have hnat : (4226076211 : ℕ)^8421*25000000000000^6373 ≤ 8010694197231^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226076211 10000000000 8010694197231 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241442043/5000000000 : ℝ)^8421 ≤ (8660112442037/25000000000000 : ℝ)^6373 := by
    have hnat : (2241442043 : ℕ)^8421*25000000000000^6373 ≤ 8660112442037^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241442043 5000000000 8660112442037 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176316423/5000000000 : ℝ), (4226076211/10000000000 : ℝ), (2241442043/5000000000 : ℝ)] ![(6663354684637/20000000000000 : ℝ), (8010694197231/25000000000000 : ℝ), (8660112442037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176316423/5000000000 : ℝ)|^8421 ≤ (6663354684637/20000000000000 : ℝ)^6373
        have hw : |(2176316423/5000000000 : ℝ)|=(2176316423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226076211/10000000000 : ℝ)|^8421 ≤ (8010694197231/25000000000000 : ℝ)^6373
        have hw : |(4226076211/10000000000 : ℝ)|=(4226076211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241442043/5000000000 : ℝ)|^8421 ≤ (8660112442037/25000000000000 : ℝ)^6373
        have hw : |(2241442043/5000000000 : ℝ)|=(2241442043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_4 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2126318511/10000000000 : ℝ)*x 0 + (2633067607/5000000000 : ℝ)*x 1 + (2696209949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126318511/10000000000 : ℝ)^8421 ≤ (2585757724487/20000000000000 : ℝ)^6373 := by
    have hnat : (2126318511 : ℕ)^8421*20000000000000^6373 ≤ 2585757724487^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126318511 10000000000 2585757724487 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633067607/5000000000 : ℝ)^8421 ≤ (42854049715721/100000000000000 : ℝ)^6373 := by
    have hnat : (2633067607 : ℕ)^8421*100000000000000^6373 ≤ 42854049715721^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633067607 5000000000 42854049715721 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696209949/5000000000 : ℝ)^8421 ≤ (44217161656641/100000000000000 : ℝ)^6373 := by
    have hnat : (2696209949 : ℕ)^8421*100000000000000^6373 ≤ 44217161656641^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696209949 5000000000 44217161656641 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2126318511/10000000000 : ℝ), (2633067607/5000000000 : ℝ), (2696209949/5000000000 : ℝ)] ![(2585757724487/20000000000000 : ℝ), (42854049715721/100000000000000 : ℝ), (44217161656641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2126318511/10000000000 : ℝ)|^8421 ≤ (2585757724487/20000000000000 : ℝ)^6373
        have hw : |(-2126318511/10000000000 : ℝ)|=(2126318511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633067607/5000000000 : ℝ)|^8421 ≤ (42854049715721/100000000000000 : ℝ)^6373
        have hw : |(2633067607/5000000000 : ℝ)|=(2633067607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696209949/5000000000 : ℝ)|^8421 ≤ (44217161656641/100000000000000 : ℝ)^6373
        have hw : |(2696209949/5000000000 : ℝ)|=(2696209949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_5 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265617507/500000000 : ℝ)*x 0 + (-25801063/125000000 : ℝ)*x 1 + (5392419867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265617507/500000000 : ℝ)^8421 ≤ (2709480417109/6250000000000 : ℝ)^6373 := by
    have hnat : (265617507 : ℕ)^8421*6250000000000^6373 ≤ 2709480417109^6373*500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265617507 500000000 2709480417109 6250000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25801063/125000000 : ℝ)^8421 ≤ (2486230399337/20000000000000 : ℝ)^6373 := by
    have hnat : (25801063 : ℕ)^8421*20000000000000^6373 ≤ 2486230399337^6373*125000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25801063 125000000 2486230399337 20000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392419867/10000000000 : ℝ)^8421 ≤ (22108580660379/50000000000000 : ℝ)^6373 := by
    have hnat : (5392419867 : ℕ)^8421*50000000000000^6373 ≤ 22108580660379^6373*10000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392419867 10000000000 22108580660379 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265617507/500000000 : ℝ), (-25801063/125000000 : ℝ), (5392419867/10000000000 : ℝ)] ![(2709480417109/6250000000000 : ℝ), (2486230399337/20000000000000 : ℝ), (22108580660379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265617507/500000000 : ℝ)|^8421 ≤ (2709480417109/6250000000000 : ℝ)^6373
        have hw : |(265617507/500000000 : ℝ)|=(265617507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25801063/125000000 : ℝ)|^8421 ≤ (2486230399337/20000000000000 : ℝ)^6373
        have hw : |(-25801063/125000000 : ℝ)|=(25801063/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392419867/10000000000 : ℝ)|^8421 ≤ (22108580660379/50000000000000 : ℝ)^6373
        have hw : |(5392419867/10000000000 : ℝ)|=(5392419867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_6 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (21249401/40000000 : ℝ)*x 0 + (337026237/625000000 : ℝ)*x 1 + (-2015708/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21249401/40000000 : ℝ)^8421 ≤ (1354740245621/3125000000000 : ℝ)^6373 := by
    have hnat : (21249401 : ℕ)^8421*3125000000000^6373 ≤ 1354740245621^6373*40000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21249401 40000000 1354740245621 3125000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337026237/625000000 : ℝ)^8421 ≤ (5527145063517/12500000000000 : ℝ)^6373 := by
    have hnat : (337026237 : ℕ)^8421*12500000000000^6373 ≤ 5527145063517^6373*625000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337026237 625000000 5527145063517 12500000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015708/9765625 : ℝ)^8421 ≤ (12431151614701/100000000000000 : ℝ)^6373 := by
    have hnat : (2015708 : ℕ)^8421*100000000000000^6373 ≤ 12431151614701^6373*9765625^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015708 9765625 12431151614701 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21249401/40000000 : ℝ), (337026237/625000000 : ℝ), (-2015708/9765625 : ℝ)] ![(1354740245621/3125000000000 : ℝ), (5527145063517/12500000000000 : ℝ), (12431151614701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21249401/40000000 : ℝ)|^8421 ≤ (1354740245621/3125000000000 : ℝ)^6373
        have hw : |(21249401/40000000 : ℝ)|=(21249401/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337026237/625000000 : ℝ)|^8421 ≤ (5527145063517/12500000000000 : ℝ)^6373
        have hw : |(337026237/625000000 : ℝ)|=(337026237/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015708/9765625 : ℝ)|^8421 ≤ (12431151614701/100000000000000 : ℝ)^6373
        have hw : |(-2015708/9765625 : ℝ)|=(2015708/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1228_s5_7 (p : ℝ) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176321407/5000000000 : ℝ)*x 0 + (560277991/1250000000 : ℝ)*x 1 + (1056684727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176321407/5000000000 : ℝ)^8421 ≤ (16658437120681/50000000000000 : ℝ)^6373 := by
    have hnat : (2176321407 : ℕ)^8421*50000000000000^6373 ≤ 16658437120681^6373*5000000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176321407 5000000000 16658437120681 50000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560277991/1250000000 : ℝ)^8421 ≤ (8658427350939/25000000000000 : ℝ)^6373 := by
    have hnat : (560277991 : ℕ)^8421*25000000000000^6373 ≤ 8658427350939^6373*1250000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560277991 1250000000 8658427350939 25000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056684727/2500000000 : ℝ)^8421 ≤ (32049416336929/100000000000000 : ℝ)^6373 := by
    have hnat : (1056684727 : ℕ)^8421*100000000000000^6373 ≤ 32049416336929^6373*2500000000^8421 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056684727 2500000000 32049416336929 100000000000000 8421 6373 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8421/2048 : ℝ)) 8421 6373 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176321407/5000000000 : ℝ), (560277991/1250000000 : ℝ), (1056684727/2500000000 : ℝ)] ![(16658437120681/50000000000000 : ℝ), (8658427350939/25000000000000 : ℝ), (32049416336929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176321407/5000000000 : ℝ)|^8421 ≤ (16658437120681/50000000000000 : ℝ)^6373
        have hw : |(2176321407/5000000000 : ℝ)|=(2176321407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560277991/1250000000 : ℝ)|^8421 ≤ (8658427350939/25000000000000 : ℝ)^6373
        have hw : |(560277991/1250000000 : ℝ)|=(560277991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056684727/2500000000 : ℝ)|^8421 ≤ (32049416336929/100000000000000 : ℝ)^6373
        have hw : |(1056684727/2500000000 : ℝ)|=(1056684727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1228_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2287/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3531/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11329/100000 : ℝ) ^ (2105/512 : ℝ) ≤ (1292621064297109/10000000000000000000 : ℝ) := by
    have hpowers : (11329/100000 : ℝ)^2105 ≤ (1292621064297109/10000000000000000000 : ℝ)^512 := by
      have hnat : (11329 : ℕ)^2105*10000000000000000000^512 ≤ 1292621064297109^512*100000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11329 100000 1292621064297109 10000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11329/100000 : ℝ)) (X := (1292621064297109/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (2105/512 : ℝ) ≤ (33059797453468017/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^2105 ≤ (33059797453468017/100000000000000000000 : ℝ)^512 := by
      have hnat : (3559 : ℕ)^2105*100000000000000000000^512 ≤ 33059797453468017^512*25000^2105 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 33059797453468017 100000000000000000000 2105 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (33059797453468017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001292621064297109/5000000000000000000 : ℝ) ≤ (10000628747985001/10000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (5001292621064297109/5000000000000000000 : ℝ)^512 ≤ (10000628747985001/10000000000000000 : ℝ)^2105 := by
      have hnat : (5001292621064297109 : ℕ)^512*10000000000000000^2105 ≤ 10000628747985001^2105*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001292621064297109 5000000000000000000 10000628747985001 10000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000628747985001/10000000000000000 : ℝ)) (X := (5001292621064297109/5000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045986008096439107/100000000000000000000 : ℝ) ≤ (5000559162478649/5000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (100045986008096439107/100000000000000000000 : ℝ)^512 ≤ (5000559162478649/5000000000000000 : ℝ)^2105 := by
      have hnat : (100045986008096439107 : ℕ)^512*5000000000000000^2105 ≤ 5000559162478649^2105*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045986008096439107 100000000000000000000 5000559162478649 5000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000559162478649/5000000000000000 : ℝ)) (X := (100045986008096439107/100000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033059797453468017/50000000000000000000 : ℝ) ≤ (2000321580385919/2000000000000000 : ℝ) ^ (2105/512 : ℝ) := by
    have hpowers : (50033059797453468017/50000000000000000000 : ℝ)^512 ≤ (2000321580385919/2000000000000000 : ℝ)^2105 := by
      have hnat : (50033059797453468017 : ℕ)^512*2000000000000000^2105 ≤ 2000321580385919^2105*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033059797453468017 50000000000000000000 2000321580385919 2000000000000000 512 2105 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000321580385919/2000000000000000 : ℝ)) (X := (50033059797453468017/50000000000000000000 : ℝ)) (by norm_num) 2105 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1292621064297109/10000000000000000000 : ℝ) ≤ ((9686911645118030827/9690000000000000000 : ℝ)+2*(163192324099/96900000000000 : ℝ)*(11329/100000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (9686911645118030827/9690000000000000000 : ℝ)+2*(163192324099/96900000000000 : ℝ)*(11329/100000 : ℝ)=(10000628747985001/10000000000000000 : ℝ) by norm_num, show 1+2*(1292621064297109/10000000000000000000 : ℝ)=(5001292621064297109/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33059797453468017/100000000000000000000 : ℝ)+(1292621064297109/10000000000000000000 : ℝ) ≤ ((9686911645118030827/9690000000000000000 : ℝ)+(163192324099/96900000000000 : ℝ)*((3559/25000 : ℝ)+(11329/100000 : ℝ)))^(2105/512 : ℝ) := by
    rw [show (9686911645118030827/9690000000000000000 : ℝ)+(163192324099/96900000000000 : ℝ)*((3559/25000 : ℝ)+(11329/100000 : ℝ))=(5000559162478649/5000000000000000 : ℝ) by norm_num, show 1+(33059797453468017/100000000000000000000 : ℝ)+(1292621064297109/10000000000000000000 : ℝ)=(100045986008096439107/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33059797453468017/100000000000000000000 : ℝ) ≤ ((9686911645118030827/9690000000000000000 : ℝ)+2*(163192324099/96900000000000 : ℝ)*(3559/25000 : ℝ))^(2105/512 : ℝ) := by
    rw [show (9686911645118030827/9690000000000000000 : ℝ)+2*(163192324099/96900000000000 : ℝ)*(3559/25000 : ℝ)=(2000321580385919/2000000000000000 : ℝ) by norm_num, show 1+2*(33059797453468017/100000000000000000000 : ℝ)=(50033059797453468017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9686911645118030827/9690000000000000000 : ℝ)*(X 1 0+X 2 0)+(163192324099/96900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11329/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (9686911645118030827/9690000000000000000 : ℝ)) (alpha := (163192324099/96900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9686911645118030827/9690000000000000000 : ℝ)*(X 0 1+X 2 1)+(163192324099/96900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11329/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (9686911645118030827/9690000000000000000 : ℝ)) (alpha := (163192324099/96900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9686911645118030827/9690000000000000000 : ℝ)*(X 0 2+X 1 2)+(163192324099/96900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2105/512 : ℝ)) (lo := (11329/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (9686911645118030827/9690000000000000000 : ℝ)) (alpha := (163192324099/96900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-132894601/625000000 : ℝ)*X 0 0+(26963737/50000000 : ℝ)*X 0 1+(5265808859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534470801/1000000000 : ℝ)*X 1 0+(-1095347999/5000000000 : ℝ)*X 1 1+(2632904429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344708011/10000000000 : ℝ)*X 2 0+(658226107/1250000000 : ℝ)*X 2 1+(-2190695999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2176316423/5000000000 : ℝ)*X 0 0+(4226076211/10000000000 : ℝ)*X 0 1+(2241442043/5000000000 : ℝ)*X 0 2+(2176316423/5000000000 : ℝ)*X 1 0+(4226076211/10000000000 : ℝ)*X 1 1+(2241442043/5000000000 : ℝ)*X 1 2+(2176316423/5000000000 : ℝ)*X 2 0+(4226076211/10000000000 : ℝ)*X 2 1+(2241442043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2126318511/10000000000 : ℝ)*X 0 0+(2633067607/5000000000 : ℝ)*X 0 1+(2696209949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265617507/500000000 : ℝ)*X 1 0+(-25801063/125000000 : ℝ)*X 1 1+(5392419867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((21249401/40000000 : ℝ)*X 2 0+(337026237/625000000 : ℝ)*X 2 1+(-2015708/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176321407/5000000000 : ℝ)*X 0 0+(560277991/1250000000 : ℝ)*X 0 1+(1056684727/2500000000 : ℝ)*X 0 2+(2176321407/5000000000 : ℝ)*X 1 0+(560277991/1250000000 : ℝ)*X 1 1+(1056684727/2500000000 : ℝ)*X 1 2+(2176321407/5000000000 : ℝ)*X 2 0+(560277991/1250000000 : ℝ)*X 2 1+(1056684727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1228_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (812164248734124098059364043/80750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1946126243/100000000000000 : ℝ)*(base19) + (1814735461/100000000000000 : ℝ)*(base23) + (7101233/10000000000000 : ℝ)*(lower2) + (5065557/2000000000000 : ℝ)*(upper3) + (9613313/6250000000000 : ℝ)*(upper5) + (5885975764174191/100000000000000 : ℝ)*(major0) + (5885975764174191/100000000000000 : ℝ)*(major1) + (5885975764174191/100000000000000 : ℝ)*(major2) + (7877883300557559/100000000000000 : ℝ)*(sp0) + (393896702830341/5000000000000 : ℝ)*(sp1) + (3938967093998801/50000000000000 : ℝ)*(sp2) + (3893986954192149/100000000000000 : ℝ)*(sp3) + (3293885969/6250000000000 : ℝ)*(sp4) + (14118082223/50000000000000 : ℝ)*(sp7) + (778803038071319/20000000000000 : ℝ)*(f.failure) + (7877936002733063/100000000000000 : ℝ)*(f.sum) + (2936428552153/1615000000000000000000000000 : ℝ)*base65 + (1967543020299895319/323000000000000000000000000000000 : ℝ)*base67 + (920133108056104681/323000000000000000000000000000000 : ℝ)*base70 + (181863516954895319/323000000000000000000000000000000 : ℝ)*base71 + (683680972701/807500000000000000000000000 : ℝ)*base74 + (3375825746742895319/323000000000000000000000000000000 : ℝ)*base75 + (445573177648895319/323000000000000000000000000000000 : ℝ)*base77 + (1758184479811895319/323000000000000000000000000000000 : ℝ)*base79 + (6017570491143/1615000000000000000000000000 : ℝ)*base81 + (4377357/500000000000000000000 : ℝ)*base89 + (4377357/500000000000000000000 : ℝ)*base91 + (4377357/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32512888657335025854230089/10093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249954583/100000000000000 : ℝ)*(base19) + (10820227/2000000000000 : ℝ)*(base23) + (1277879/25000000000000 : ℝ)*(upper3) + (5998429/12500000000000 : ℝ)*(lower4) + (22078039/100000000000000 : ℝ)*(upper5) + (369773194339093/6250000000000 : ℝ)*(major0) + (369773194339093/6250000000000 : ℝ)*(major1) + (369773194339093/6250000000000 : ℝ)*(major2) + (6753705313/100000000000000 : ℝ)*(sp1) + (12788546211/100000000000000 : ℝ)*(sp2) + (3959309058296097/50000000000000 : ℝ)*(sp4) + (3959305556466149/50000000000000 : ℝ)*(sp5) + (7918604787034633/100000000000000 : ℝ)*(sp6) + (3914123994889073/100000000000000 : ℝ)*(sp7) + (3914123994889073/100000000000000 : ℝ)*(f.failure) + (3959309058296097/50000000000000 : ℝ)*(f.sum) + (213561711247/302812500000000000000000000 : ℝ)*base65 + (151580751714669911/60562500000000000000000000000000 : ℝ)*base67 + (440283991796919911/60562500000000000000000000000000 : ℝ)*base69 + (451160989512080089/60562500000000000000000000000000 : ℝ)*base72 + (8900869150031/2422500000000000000000000000 : ℝ)*base73 + (137401802043669911/60562500000000000000000000000000 : ℝ)*base75 + (432394228490142589/60562500000000000000000000000000 : ℝ)*base78 + (592065050996919911/60562500000000000000000000000000 : ℝ)*base79 + (1532058196957/4845000000000000000000000000 : ℝ)*base81 + (8635019/2500000000000000000000 : ℝ)*base89 + (8635019/2500000000000000000000 : ℝ)*base91 + (8635019/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1228_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1228_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1228_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1228_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1228_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1228_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2105/512 : ℝ) ≤ p) (hpb : p ≤ (8421/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37788603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (813/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2287/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1228_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

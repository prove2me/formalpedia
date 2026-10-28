-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:09:45.357488+00:00
-- url     : https://prove2.me/submissions/03512f07-c7b2-44b6-90dc-289840532ce8

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
theorem support_rectangle_w1019_s5_0 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-111341887/500000000 : ℝ)*x 0 + (5398379921/10000000000 : ℝ)*x 1 + (5260530541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111341887/500000000 : ℝ)^2053 ≤ (3379846261211/25000000000000 : ℝ)^1541 := by
    have hnat : (111341887 : ℕ)^2053*25000000000000^1541 ≤ 3379846261211^1541*500000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111341887 500000000 3379846261211 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398379921/10000000000 : ℝ)^2053 ≤ (2199264691969/5000000000000 : ℝ)^1541 := by
    have hnat : (5398379921 : ℕ)^2053*5000000000000^1541 ≤ 2199264691969^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398379921 10000000000 2199264691969 5000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260530541/10000000000 : ℝ)^2053 ≤ (8499064221527/20000000000000 : ℝ)^1541 := by
    have hnat : (5260530541 : ℕ)^2053*20000000000000^1541 ≤ 8499064221527^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260530541 10000000000 8499064221527 20000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111341887/500000000 : ℝ), (5398379921/10000000000 : ℝ), (5260530541/10000000000 : ℝ)] ![(3379846261211/25000000000000 : ℝ), (2199264691969/5000000000000 : ℝ), (8499064221527/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111341887/500000000 : ℝ)|^2053 ≤ (3379846261211/25000000000000 : ℝ)^1541
        have hw : |(-111341887/500000000 : ℝ)|=(111341887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398379921/10000000000 : ℝ)|^2053 ≤ (2199264691969/5000000000000 : ℝ)^1541
        have hw : |(5398379921/10000000000 : ℝ)|=(5398379921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260530541/10000000000 : ℝ)|^2053 ≤ (8499064221527/20000000000000 : ℝ)^1541
        have hw : |(5260530541/10000000000 : ℝ)|=(5260530541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_1 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345864609/10000000000 : ℝ)*x 0 + (-2296839789/10000000000 : ℝ)*x 1 + (5260530591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345864609/10000000000 : ℝ)^2053 ≤ (43416162675571/100000000000000 : ℝ)^1541 := by
    have hnat : (5345864609 : ℕ)^2053*100000000000000^1541 ≤ 43416162675571^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345864609 10000000000 43416162675571 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296839789/10000000000 : ℝ)^2053 ≤ (7044257828617/50000000000000 : ℝ)^1541 := by
    have hnat : (2296839789 : ℕ)^2053*50000000000000^1541 ≤ 7044257828617^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296839789 10000000000 7044257828617 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260530591/10000000000 : ℝ)^2053 ≤ (42495321645741/100000000000000 : ℝ)^1541 := by
    have hnat : (5260530591 : ℕ)^2053*100000000000000^1541 ≤ 42495321645741^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260530591 10000000000 42495321645741 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345864609/10000000000 : ℝ), (-2296839789/10000000000 : ℝ), (5260530591/10000000000 : ℝ)] ![(43416162675571/100000000000000 : ℝ), (7044257828617/50000000000000 : ℝ), (42495321645741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345864609/10000000000 : ℝ)|^2053 ≤ (43416162675571/100000000000000 : ℝ)^1541
        have hw : |(5345864609/10000000000 : ℝ)|=(5345864609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2296839789/10000000000 : ℝ)|^2053 ≤ (7044257828617/50000000000000 : ℝ)^1541
        have hw : |(-2296839789/10000000000 : ℝ)|=(2296839789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260530591/10000000000 : ℝ)|^2053 ≤ (42495321645741/100000000000000 : ℝ)^1541
        have hw : |(5260530591/10000000000 : ℝ)|=(5260530591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_2 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5345864361/10000000000 : ℝ)*x 0 + (1052106053/2000000000 : ℝ)*x 1 + (-1148420273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345864361/10000000000 : ℝ)^2053 ≤ (43416159992257/100000000000000 : ℝ)^1541 := by
    have hnat : (5345864361 : ℕ)^2053*100000000000000^1541 ≤ 43416159992257^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345864361 10000000000 43416159992257 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052106053/2000000000 : ℝ)^2053 ≤ (42495318137289/100000000000000 : ℝ)^1541 := by
    have hnat : (1052106053 : ℕ)^2053*100000000000000^1541 ≤ 42495318137289^1541*2000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052106053 2000000000 42495318137289 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148420273/5000000000 : ℝ)^2053 ≤ (14088521843331/100000000000000 : ℝ)^1541 := by
    have hnat : (1148420273 : ℕ)^2053*100000000000000^1541 ≤ 14088521843331^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148420273 5000000000 14088521843331 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345864361/10000000000 : ℝ), (1052106053/2000000000 : ℝ), (-1148420273/5000000000 : ℝ)] ![(43416159992257/100000000000000 : ℝ), (42495318137289/100000000000000 : ℝ), (14088521843331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345864361/10000000000 : ℝ)|^2053 ≤ (43416159992257/100000000000000 : ℝ)^1541
        have hw : |(5345864361/10000000000 : ℝ)|=(5345864361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052106053/2000000000 : ℝ)|^2053 ≤ (42495318137289/100000000000000 : ℝ)^1541
        have hw : |(1052106053/2000000000 : ℝ)|=(1052106053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1148420273/5000000000 : ℝ)|^2053 ≤ (14088521843331/100000000000000 : ℝ)^1541
        have hw : |(-1148420273/5000000000 : ℝ)|=(1148420273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_3 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4382131629/10000000000 : ℝ)*x 0 + (4250402371/10000000000 : ℝ)*x 1 + (4518048313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4382131629/10000000000 : ℝ)^2053 ≤ (6662922398609/20000000000000 : ℝ)^1541 := by
    have hnat : (4382131629 : ℕ)^2053*20000000000000^1541 ≤ 6662922398609^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4382131629 10000000000 6662922398609 20000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4250402371/10000000000 : ℝ)^2053 ≤ (499798893831/1562500000000 : ℝ)^1541 := by
    have hnat : (4250402371 : ℕ)^2053*1562500000000^1541 ≤ 499798893831^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250402371 10000000000 499798893831 1562500000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518048313/10000000000 : ℝ)^2053 ≤ (6939651756191/20000000000000 : ℝ)^1541 := by
    have hnat : (4518048313 : ℕ)^2053*20000000000000^1541 ≤ 6939651756191^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518048313 10000000000 6939651756191 20000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4382131629/10000000000 : ℝ), (4250402371/10000000000 : ℝ), (4518048313/10000000000 : ℝ)] ![(6662922398609/20000000000000 : ℝ), (499798893831/1562500000000 : ℝ), (6939651756191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4382131629/10000000000 : ℝ)|^2053 ≤ (6662922398609/20000000000000 : ℝ)^1541
        have hw : |(4382131629/10000000000 : ℝ)|=(4382131629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4250402371/10000000000 : ℝ)|^2053 ≤ (499798893831/1562500000000 : ℝ)^1541
        have hw : |(4250402371/10000000000 : ℝ)|=(4250402371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518048313/10000000000 : ℝ)|^2053 ≤ (6939651756191/20000000000000 : ℝ)^1541
        have hw : |(4518048313/10000000000 : ℝ)|=(4518048313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_4 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1113422081/5000000000 : ℝ)*x 0 + (5260891833/10000000000 : ℝ)*x 1 + (5398016927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1113422081/5000000000 : ℝ)^2053 ≤ (1689929623453/12500000000000 : ℝ)^1541 := by
    have hnat : (1113422081 : ℕ)^2053*12500000000000^1541 ≤ 1689929623453^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113422081 5000000000 1689929623453 12500000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260891833/10000000000 : ℝ)^2053 ≤ (21249604710149/50000000000000 : ℝ)^1541 := by
    have hnat : (5260891833 : ℕ)^2053*50000000000000^1541 ≤ 21249604710149^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260891833 10000000000 21249604710149 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398016927/10000000000 : ℝ)^2053 ≤ (43981353578673/100000000000000 : ℝ)^1541 := by
    have hnat : (5398016927 : ℕ)^2053*100000000000000^1541 ≤ 43981353578673^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398016927 10000000000 43981353578673 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1113422081/5000000000 : ℝ), (5260891833/10000000000 : ℝ), (5398016927/10000000000 : ℝ)] ![(1689929623453/12500000000000 : ℝ), (21249604710149/50000000000000 : ℝ), (43981353578673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1113422081/5000000000 : ℝ)|^2053 ≤ (1689929623453/12500000000000 : ℝ)^1541
        have hw : |(-1113422081/5000000000 : ℝ)|=(1113422081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260891833/10000000000 : ℝ)|^2053 ≤ (21249604710149/50000000000000 : ℝ)^1541
        have hw : |(5260891833/10000000000 : ℝ)|=(5260891833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398016927/10000000000 : ℝ)|^2053 ≤ (43981353578673/100000000000000 : ℝ)^1541
        have hw : |(5398016927/10000000000 : ℝ)|=(5398016927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_5 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5311275301/10000000000 : ℝ)*x 0 + (-107967721/500000000 : ℝ)*x 1 + (2699008517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311275301/10000000000 : ℝ)^2053 ≤ (43042315655877/100000000000000 : ℝ)^1541 := by
    have hnat : (5311275301 : ℕ)^2053*100000000000000^1541 ≤ 43042315655877^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311275301 10000000000 43042315655877 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107967721/500000000 : ℝ)^2053 ≤ (12976329589423/100000000000000 : ℝ)^1541 := by
    have hnat : (107967721 : ℕ)^2053*100000000000000^1541 ≤ 12976329589423^1541*500000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107967721 500000000 12976329589423 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699008517/5000000000 : ℝ)^2053 ≤ (21990677370067/50000000000000 : ℝ)^1541 := by
    have hnat : (2699008517 : ℕ)^2053*50000000000000^1541 ≤ 21990677370067^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699008517 5000000000 21990677370067 50000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311275301/10000000000 : ℝ), (-107967721/500000000 : ℝ), (2699008517/5000000000 : ℝ)] ![(43042315655877/100000000000000 : ℝ), (12976329589423/100000000000000 : ℝ), (21990677370067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311275301/10000000000 : ℝ)|^2053 ≤ (43042315655877/100000000000000 : ℝ)^1541
        have hw : |(5311275301/10000000000 : ℝ)|=(5311275301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107967721/500000000 : ℝ)|^2053 ≤ (12976329589423/100000000000000 : ℝ)^1541
        have hw : |(-107967721/500000000 : ℝ)|=(107967721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699008517/5000000000 : ℝ)|^2053 ≤ (21990677370067/50000000000000 : ℝ)^1541
        have hw : |(2699008517/5000000000 : ℝ)|=(2699008517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_6 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062255077/2000000000 : ℝ)*x 0 + (1349504281/2500000000 : ℝ)*x 1 + (-1079677093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062255077/2000000000 : ℝ)^2053 ≤ (1345072392587/3125000000000 : ℝ)^1541 := by
    have hnat : (1062255077 : ℕ)^2053*3125000000000^1541 ≤ 1345072392587^1541*2000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062255077 2000000000 1345072392587 3125000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349504281/2500000000 : ℝ)^2053 ≤ (43981355717063/100000000000000 : ℝ)^1541 := by
    have hnat : (1349504281 : ℕ)^2053*100000000000000^1541 ≤ 43981355717063^1541*2500000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349504281 2500000000 43981355717063 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079677093/5000000000 : ℝ)^2053 ≤ (519053108641/4000000000000 : ℝ)^1541 := by
    have hnat : (1079677093 : ℕ)^2053*4000000000000^1541 ≤ 519053108641^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079677093 5000000000 519053108641 4000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062255077/2000000000 : ℝ), (1349504281/2500000000 : ℝ), (-1079677093/5000000000 : ℝ)] ![(1345072392587/3125000000000 : ℝ), (43981355717063/100000000000000 : ℝ), (519053108641/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062255077/2000000000 : ℝ)|^2053 ≤ (1345072392587/3125000000000 : ℝ)^1541
        have hw : |(1062255077/2000000000 : ℝ)|=(1062255077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349504281/2500000000 : ℝ)|^2053 ≤ (43981355717063/100000000000000 : ℝ)^1541
        have hw : |(1349504281/2500000000 : ℝ)|=(1349504281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079677093/5000000000 : ℝ)|^2053 ≤ (519053108641/4000000000000 : ℝ)^1541
        have hw : |(-1079677093/5000000000 : ℝ)|=(1079677093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1019_s5_7 (p : ℝ) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2191071589/5000000000 : ℝ)*x 0 + (4517347683/10000000000 : ℝ)*x 1 + (4251105657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191071589/5000000000 : ℝ)^2053 ≤ (33314728964589/100000000000000 : ℝ)^1541 := by
    have hnat : (2191071589 : ℕ)^2053*100000000000000^1541 ≤ 33314728964589^1541*5000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191071589 5000000000 33314728964589 100000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517347683/10000000000 : ℝ)^2053 ≤ (8672772601713/25000000000000 : ℝ)^1541 := by
    have hnat : (4517347683 : ℕ)^2053*25000000000000^1541 ≤ 8672772601713^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517347683 10000000000 8672772601713 25000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4251105657/10000000000 : ℝ)^2053 ≤ (6398836121323/20000000000000 : ℝ)^1541 := by
    have hnat : (4251105657 : ℕ)^2053*20000000000000^1541 ≤ 6398836121323^1541*10000000000^2053 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251105657 10000000000 6398836121323 20000000000000 2053 1541 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2053/512 : ℝ)) 2053 1541 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2191071589/5000000000 : ℝ), (4517347683/10000000000 : ℝ), (4251105657/10000000000 : ℝ)] ![(33314728964589/100000000000000 : ℝ), (8672772601713/25000000000000 : ℝ), (6398836121323/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2191071589/5000000000 : ℝ)|^2053 ≤ (33314728964589/100000000000000 : ℝ)^1541
        have hw : |(2191071589/5000000000 : ℝ)|=(2191071589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517347683/10000000000 : ℝ)|^2053 ≤ (8672772601713/25000000000000 : ℝ)^1541
        have hw : |(4517347683/10000000000 : ℝ)|=(4517347683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4251105657/10000000000 : ℝ)|^2053 ≤ (6398836121323/20000000000000 : ℝ)^1541
        have hw : |(4251105657/10000000000 : ℝ)|=(4251105657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1019_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3563/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11121/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3563/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10919/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3563/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10919/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3563/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10919/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3563/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10919/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3563/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10919/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3563/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10919/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10919/100000 : ℝ) ^ (8211/2048 : ℝ) ≤ (1740677712947563/12500000000000000000 : ℝ) := by
    have hpowers : (10919/100000 : ℝ)^8211 ≤ (1740677712947563/12500000000000000000 : ℝ)^2048 := by
      have hnat : (10919 : ℕ)^8211*12500000000000000000^2048 ≤ 1740677712947563^2048*100000^8211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10919 100000 1740677712947563 12500000000000000000 8211 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10919/100000 : ℝ)) (X := (1740677712947563/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3563/25000 : ℝ) ^ (8211/2048 : ℝ) ≤ (40518510303296821/100000000000000000000 : ℝ) := by
    have hpowers : (3563/25000 : ℝ)^8211 ≤ (40518510303296821/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3563 : ℕ)^8211*100000000000000000000^2048 ≤ 40518510303296821^2048*25000^8211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3563 25000 40518510303296821 100000000000000000000 8211 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3563/25000 : ℝ)) (X := (40518510303296821/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251740677712947563/6250000000000000000 : ℝ) ≤ (250017364683513/250000000000000 : ℝ) ^ (8211/2048 : ℝ) := by
    have hpowers : (6251740677712947563/6250000000000000000 : ℝ)^2048 ≤ (250017364683513/250000000000000 : ℝ)^8211 := by
      have hnat : (6251740677712947563 : ℕ)^2048*250000000000000^8211 ≤ 250017364683513^8211*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251740677712947563 6250000000000000000 250017364683513 250000000000000 2048 8211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017364683513/250000000000000 : ℝ)) (X := (6251740677712947563/6250000000000000000 : ℝ)) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002177757280275093/4000000000000000000 : ℝ) ≤ (1250169708923727/1250000000000000 : ℝ) ^ (8211/2048 : ℝ) := by
    have hpowers : (4002177757280275093/4000000000000000000 : ℝ)^2048 ≤ (1250169708923727/1250000000000000 : ℝ)^8211 := by
      have hnat : (4002177757280275093 : ℕ)^2048*1250000000000000^8211 ≤ 1250169708923727^8211*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002177757280275093 4000000000000000000 1250169708923727 1250000000000000 2048 8211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250169708923727/1250000000000000 : ℝ)) (X := (4002177757280275093/4000000000000000000 : ℝ)) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040518510303296821/50000000000000000000 : ℝ) ≤ (1250252594429889/1250000000000000 : ℝ) ^ (8211/2048 : ℝ) := by
    have hpowers : (50040518510303296821/50000000000000000000 : ℝ)^2048 ≤ (1250252594429889/1250000000000000 : ℝ)^8211 := by
      have hnat : (50040518510303296821 : ℕ)^2048*1250000000000000^8211 ≤ 1250252594429889^8211*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040518510303296821 50000000000000000000 1250252594429889 1250000000000000 2048 8211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250252594429889/1250000000000000 : ℝ)) (X := (50040518510303296821/50000000000000000000 : ℝ)) (by norm_num) 8211 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1740677712947563/12500000000000000000 : ℝ) ≤ ((1388243109589059463/1388750000000000000 : ℝ)+2*(13814251027/6943750000000 : ℝ)*(10919/100000 : ℝ))^(8211/2048 : ℝ) := by
    rw [show (1388243109589059463/1388750000000000000 : ℝ)+2*(13814251027/6943750000000 : ℝ)*(10919/100000 : ℝ)=(250017364683513/250000000000000 : ℝ) by norm_num, show 1+2*(1740677712947563/12500000000000000000 : ℝ)=(6251740677712947563/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40518510303296821/100000000000000000000 : ℝ)+(1740677712947563/12500000000000000000 : ℝ) ≤ ((1388243109589059463/1388750000000000000 : ℝ)+(13814251027/6943750000000 : ℝ)*((3563/25000 : ℝ)+(10919/100000 : ℝ)))^(8211/2048 : ℝ) := by
    rw [show (1388243109589059463/1388750000000000000 : ℝ)+(13814251027/6943750000000 : ℝ)*((3563/25000 : ℝ)+(10919/100000 : ℝ))=(1250169708923727/1250000000000000 : ℝ) by norm_num, show 1+(40518510303296821/100000000000000000000 : ℝ)+(1740677712947563/12500000000000000000 : ℝ)=(4002177757280275093/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40518510303296821/100000000000000000000 : ℝ) ≤ ((1388243109589059463/1388750000000000000 : ℝ)+2*(13814251027/6943750000000 : ℝ)*(3563/25000 : ℝ))^(8211/2048 : ℝ) := by
    rw [show (1388243109589059463/1388750000000000000 : ℝ)+2*(13814251027/6943750000000 : ℝ)*(3563/25000 : ℝ)=(1250252594429889/1250000000000000 : ℝ) by norm_num, show 1+2*(40518510303296821/100000000000000000000 : ℝ)=(50040518510303296821/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1388243109589059463/1388750000000000000 : ℝ)*(X 1 0+X 2 0)+(13814251027/6943750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8211/2048 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (3563/25000 : ℝ)) (c := (1388243109589059463/1388750000000000000 : ℝ)) (alpha := (13814251027/6943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1388243109589059463/1388750000000000000 : ℝ)*(X 0 1+X 2 1)+(13814251027/6943750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8211/2048 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (3563/25000 : ℝ)) (c := (1388243109589059463/1388750000000000000 : ℝ)) (alpha := (13814251027/6943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1388243109589059463/1388750000000000000 : ℝ)*(X 0 2+X 1 2)+(13814251027/6943750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8211/2048 : ℝ)) (lo := (10919/100000 : ℝ)) (hi := (3563/25000 : ℝ)) (c := (1388243109589059463/1388750000000000000 : ℝ)) (alpha := (13814251027/6943750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-111341887/500000000 : ℝ)*X 0 0+(5398379921/10000000000 : ℝ)*X 0 1+(5260530541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345864609/10000000000 : ℝ)*X 1 0+(-2296839789/10000000000 : ℝ)*X 1 1+(5260530591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345864361/10000000000 : ℝ)*X 2 0+(1052106053/2000000000 : ℝ)*X 2 1+(-1148420273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4382131629/10000000000 : ℝ)*X 0 0+(4250402371/10000000000 : ℝ)*X 0 1+(4518048313/10000000000 : ℝ)*X 0 2+(4382131629/10000000000 : ℝ)*X 1 0+(4250402371/10000000000 : ℝ)*X 1 1+(4518048313/10000000000 : ℝ)*X 1 2+(4382131629/10000000000 : ℝ)*X 2 0+(4250402371/10000000000 : ℝ)*X 2 1+(4518048313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1113422081/5000000000 : ℝ)*X 0 0+(5260891833/10000000000 : ℝ)*X 0 1+(5398016927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311275301/10000000000 : ℝ)*X 1 0+(-107967721/500000000 : ℝ)*X 1 1+(2699008517/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062255077/2000000000 : ℝ)*X 2 0+(1349504281/2500000000 : ℝ)*X 2 1+(-1079677093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2191071589/5000000000 : ℝ)*X 0 0+(4517347683/10000000000 : ℝ)*X 0 1+(4251105657/10000000000 : ℝ)*X 0 2+(2191071589/5000000000 : ℝ)*X 1 0+(4517347683/10000000000 : ℝ)*X 1 1+(4251105657/10000000000 : ℝ)*X 1 2+(2191071589/5000000000 : ℝ)*X 2 0+(4517347683/10000000000 : ℝ)*X 2 1+(4251105657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1019_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4029326596491325311327/5555000000000000000000000000 : ℝ) := by norm_num
    linear_combination (347455011/25000000000000 : ℝ)*(base19) + (1303555523/100000000000000 : ℝ)*(base23) + (49675829/25000000000000 : ℝ)*(lower4) + (197592727/50000000000000 : ℝ)*(lower5) + (1373843785577031/25000000000000 : ℝ)*(major0) + (1373843785577031/25000000000000 : ℝ)*(major1) + (1373843785577031/25000000000000 : ℝ)*(major2) + (290174882064793/4000000000000 : ℝ)*(sp0) + (7254421210300669/100000000000000 : ℝ)*(sp1) + (7254402530611439/100000000000000 : ℝ)*(sp2) + (373630185256051/10000000000000 : ℝ)*(sp3) + (50548500887/100000000000000 : ℝ)*(sp4) + (15012763/80000000000 : ℝ)*(sp6) + (25807756643/100000000000000 : ℝ)*(sp7) + (3736327660317153/100000000000000 : ℝ)*(f.failure) + (906802825015089/12500000000000 : ℝ)*(f.sum) + (10630267804591/2777500000000000000000000000 : ℝ)*base66 + (75124099808238103/34718750000000000000000000000000 : ℝ)*base67 + (406907877140113103/34718750000000000000000000000000 : ℝ)*base69 + (145137156238324397/34718750000000000000000000000000 : ℝ)*base72 + (10608946292511/2777500000000000000000000000 : ℝ)*base74 + (49580351589730647/34718750000000000000000000000000 : ℝ)*base76 + (112374662259824397/34718750000000000000000000000000 : ℝ)*base78 + (113674874935456853/34718750000000000000000000000000 : ℝ)*base79 + (6023230808717/5555000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (110987199/10000000000000000000000 : ℝ)*base89 + (110987199/10000000000000000000000 : ℝ)*base91 + (110987199/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (315944391423353229679958313/69437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (314945071/100000000000000 : ℝ)*(base19) + (795434349/100000000000000 : ℝ)*(base23) + (5870379/5000000000000 : ℝ)*(upper2) + (14932063/20000000000000 : ℝ)*(upper3) + (5524300753852061/100000000000000 : ℝ)*(major0) + (5524300753852061/100000000000000 : ℝ)*(major1) + (5524300753852061/100000000000000 : ℝ)*(major2) + (1078708287/10000000000000 : ℝ)*(sp1) + (16457177687/50000000000000 : ℝ)*(sp2) + (5775835409/100000000000000 : ℝ)*(sp3) + (7292607056097987/100000000000000 : ℝ)*(sp4) + (3646297977035023/50000000000000 : ℝ)*(sp5) + (911571668288533/12500000000000 : ℝ)*(sp6) + (1877994262051119/50000000000000 : ℝ)*(sp7) + (234749643746103/6250000000000 : ℝ)*(f.failure) + (7292607056097987/100000000000000 : ℝ)*(f.sum) + (22997024550647/5555000000000000000000000000 : ℝ)*base65 + (2068593013250503243/138875000000000000000000000000000 : ℝ)*base67 + (3055009380082003243/138875000000000000000000000000000 : ℝ)*base69 + (2731810596387128243/138875000000000000000000000000000 : ℝ)*base71 + (9640654755013/5555000000000000000000000000 : ℝ)*base74 + (2662324515690128243/138875000000000000000000000000000 : ℝ)*base75 + (1685550513692378243/138875000000000000000000000000000 : ℝ)*base77 + (1167146128759878243/138875000000000000000000000000000 : ℝ)*base79 + (6426979809727/5555000000000000000000000000 : ℝ)*base81 + (5865049/625000000000000000000 : ℝ)*base89 + (5865049/625000000000000000000 : ℝ)*base91 + (5865049/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1019_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3563/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1019_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8211/2048 : ℝ) ≤ p) (hpb : p ≤ (2053/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147079583/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3563/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10919/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11121/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1019_s5 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

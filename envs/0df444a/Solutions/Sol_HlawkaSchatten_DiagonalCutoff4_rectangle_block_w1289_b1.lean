-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1289_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:10.82399+00:00
-- url     : https://prove2.me/submissions/6bcbf13a-1b35-4ab9-9952-db7212c96aff

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
theorem support_rectangle_w1289_s3_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104413199/500000000 : ℝ)*x 0 + (169828843/312500000 : ℝ)*x 1 + (2612658453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104413199/500000000 : ℝ)^4249 ≤ (12700010462853/100000000000000 : ℝ)^3225 := by
    have hnat : (104413199 : ℕ)^4249*100000000000000^3225 ≤ 12700010462853^3225*500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104413199 500000000 12700010462853 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169828843/312500000 : ℝ)^4249 ≤ (11194638121399/25000000000000 : ℝ)^3225 := by
    have hnat : (169828843 : ℕ)^4249*25000000000000^3225 ≤ 11194638121399^3225*312500000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169828843 312500000 11194638121399 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612658453/5000000000 : ℝ)^4249 ≤ (8504287407779/20000000000000 : ℝ)^3225 := by
    have hnat : (2612658453 : ℕ)^4249*20000000000000^3225 ≤ 8504287407779^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612658453 5000000000 8504287407779 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104413199/500000000 : ℝ), (169828843/312500000 : ℝ), (2612658453/5000000000 : ℝ)] ![(12700010462853/100000000000000 : ℝ), (11194638121399/25000000000000 : ℝ), (8504287407779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104413199/500000000 : ℝ)|^4249 ≤ (12700010462853/100000000000000 : ℝ)^3225
        have hw : |(-104413199/500000000 : ℝ)|=(104413199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169828843/312500000 : ℝ)|^4249 ≤ (11194638121399/25000000000000 : ℝ)^3225
        have hw : |(169828843/312500000 : ℝ)|=(169828843/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612658453/5000000000 : ℝ)|^4249 ≤ (8504287407779/20000000000000 : ℝ)^3225
        have hw : |(2612658453/5000000000 : ℝ)|=(2612658453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535466609/1000000000 : ℝ)*x 0 + (-219534271/1000000000 : ℝ)*x 1 + (5225316957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535466609/1000000000 : ℝ)^4249 ≤ (43913663730349/100000000000000 : ℝ)^3225 := by
    have hnat : (535466609 : ℕ)^4249*100000000000000^3225 ≤ 43913663730349^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535466609 1000000000 43913663730349 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219534271/1000000000 : ℝ)^4249 ≤ (6782449331767/50000000000000 : ℝ)^3225 := by
    have hnat : (219534271 : ℕ)^4249*50000000000000^3225 ≤ 6782449331767^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219534271 1000000000 6782449331767 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5225316957/10000000000 : ℝ)^4249 ≤ (42521437585687/100000000000000 : ℝ)^3225 := by
    have hnat : (5225316957 : ℕ)^4249*100000000000000^3225 ≤ 42521437585687^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225316957 10000000000 42521437585687 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535466609/1000000000 : ℝ), (-219534271/1000000000 : ℝ), (5225316957/10000000000 : ℝ)] ![(43913663730349/100000000000000 : ℝ), (6782449331767/50000000000000 : ℝ), (42521437585687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535466609/1000000000 : ℝ)|^4249 ≤ (43913663730349/100000000000000 : ℝ)^3225
        have hw : |(535466609/1000000000 : ℝ)|=(535466609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219534271/1000000000 : ℝ)|^4249 ≤ (6782449331767/50000000000000 : ℝ)^3225
        have hw : |(-219534271/1000000000 : ℝ)|=(219534271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5225316957/10000000000 : ℝ)|^4249 ≤ (42521437585687/100000000000000 : ℝ)^3225
        have hw : |(5225316957/10000000000 : ℝ)|=(5225316957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535466613/1000000000 : ℝ)*x 0 + (261265837/500000000 : ℝ)*x 1 + (-2195342943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535466613/1000000000 : ℝ)^4249 ≤ (10978416040637/25000000000000 : ℝ)^3225 := by
    have hnat : (535466613 : ℕ)^4249*25000000000000^3225 ≤ 10978416040637^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535466613 1000000000 10978416040637 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261265837/500000000 : ℝ)^4249 ≤ (42521435259139/100000000000000 : ℝ)^3225 := by
    have hnat : (261265837 : ℕ)^4249*100000000000000^3225 ≤ 42521435259139^3225*500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261265837 500000000 42521435259139 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195342943/10000000000 : ℝ)^4249 ≤ (6782450280179/50000000000000 : ℝ)^3225 := by
    have hnat : (2195342943 : ℕ)^4249*50000000000000^3225 ≤ 6782450280179^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195342943 10000000000 6782450280179 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535466613/1000000000 : ℝ), (261265837/500000000 : ℝ), (-2195342943/10000000000 : ℝ)] ![(10978416040637/25000000000000 : ℝ), (42521435259139/100000000000000 : ℝ), (6782450280179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535466613/1000000000 : ℝ)|^4249 ≤ (10978416040637/25000000000000 : ℝ)^3225
        have hw : |(535466613/1000000000 : ℝ)|=(535466613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261265837/500000000 : ℝ)|^4249 ≤ (42521435259139/100000000000000 : ℝ)^3225
        have hw : |(261265837/500000000 : ℝ)|=(261265837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195342943/10000000000 : ℝ)|^4249 ≤ (6782450280179/50000000000000 : ℝ)^3225
        have hw : |(-2195342943/10000000000 : ℝ)|=(2195342943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867845859/2000000000 : ℝ)*x 0 + (4129573609/10000000000 : ℝ)*x 1 + (1139762291/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867845859/2000000000 : ℝ)^4249 ≤ (16643860908753/50000000000000 : ℝ)^3225 := by
    have hnat : (867845859 : ℕ)^4249*50000000000000^3225 ≤ 16643860908753^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867845859 2000000000 16643860908753 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129573609/10000000000 : ℝ)^4249 ≤ (31185138183601/100000000000000 : ℝ)^3225 := by
    have hnat : (4129573609 : ℕ)^4249*100000000000000^3225 ≤ 31185138183601^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129573609 10000000000 31185138183601 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139762291/2500000000 : ℝ)^4249 ≤ (35527139977503/100000000000000 : ℝ)^3225 := by
    have hnat : (1139762291 : ℕ)^4249*100000000000000^3225 ≤ 35527139977503^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139762291 2500000000 35527139977503 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867845859/2000000000 : ℝ), (4129573609/10000000000 : ℝ), (1139762291/2500000000 : ℝ)] ![(16643860908753/50000000000000 : ℝ), (31185138183601/100000000000000 : ℝ), (35527139977503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867845859/2000000000 : ℝ)|^4249 ≤ (16643860908753/50000000000000 : ℝ)^3225
        have hw : |(867845859/2000000000 : ℝ)|=(867845859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129573609/10000000000 : ℝ)|^4249 ≤ (31185138183601/100000000000000 : ℝ)^3225
        have hw : |(4129573609/10000000000 : ℝ)|=(4129573609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139762291/2500000000 : ℝ)|^4249 ≤ (35527139977503/100000000000000 : ℝ)^3225
        have hw : |(1139762291/2500000000 : ℝ)|=(1139762291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2088286773/10000000000 : ℝ)*x 0 + (5226219713/10000000000 : ℝ)*x 1 + (5433614481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088286773/10000000000 : ℝ)^4249 ≤ (12700193095299/100000000000000 : ℝ)^3225 := by
    have hnat : (2088286773 : ℕ)^4249*100000000000000^3225 ≤ 12700193095299^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088286773 10000000000 12700193095299 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226219713/10000000000 : ℝ)^4249 ≤ (10632779169361/25000000000000 : ℝ)^3225 := by
    have hnat : (5226219713 : ℕ)^4249*25000000000000^3225 ≤ 10632779169361^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226219713 10000000000 10632779169361 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433614481/10000000000 : ℝ)^4249 ≤ (44768690221047/100000000000000 : ℝ)^3225 := by
    have hnat : (5433614481 : ℕ)^4249*100000000000000^3225 ≤ 44768690221047^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433614481 10000000000 44768690221047 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2088286773/10000000000 : ℝ), (5226219713/10000000000 : ℝ), (5433614481/10000000000 : ℝ)] ![(12700193095299/100000000000000 : ℝ), (10632779169361/25000000000000 : ℝ), (44768690221047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2088286773/10000000000 : ℝ)|^4249 ≤ (12700193095299/100000000000000 : ℝ)^3225
        have hw : |(-2088286773/10000000000 : ℝ)|=(2088286773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226219713/10000000000 : ℝ)|^4249 ≤ (10632779169361/25000000000000 : ℝ)^3225
        have hw : |(5226219713/10000000000 : ℝ)|=(5226219713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433614481/10000000000 : ℝ)|^4249 ≤ (44768690221047/100000000000000 : ℝ)^3225
        have hw : |(5433614481/10000000000 : ℝ)|=(5433614481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650560003/5000000000 : ℝ)*x 0 + (-1987045053/10000000000 : ℝ)*x 1 + (5433614429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650560003/5000000000 : ℝ)^4249 ≤ (43336019549863/100000000000000 : ℝ)^3225 := by
    have hnat : (2650560003 : ℕ)^4249*100000000000000^3225 ≤ 43336019549863^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650560003 5000000000 43336019549863 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987045053/10000000000 : ℝ)^4249 ≤ (11895290778223/100000000000000 : ℝ)^3225 := by
    have hnat : (1987045053 : ℕ)^4249*100000000000000^3225 ≤ 11895290778223^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987045053 10000000000 11895290778223 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433614429/10000000000 : ℝ)^4249 ≤ (4476868965657/10000000000000 : ℝ)^3225 := by
    have hnat : (5433614429 : ℕ)^4249*10000000000000^3225 ≤ 4476868965657^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433614429 10000000000 4476868965657 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650560003/5000000000 : ℝ), (-1987045053/10000000000 : ℝ), (5433614429/10000000000 : ℝ)] ![(43336019549863/100000000000000 : ℝ), (11895290778223/100000000000000 : ℝ), (4476868965657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650560003/5000000000 : ℝ)|^4249 ≤ (43336019549863/100000000000000 : ℝ)^3225
        have hw : |(2650560003/5000000000 : ℝ)|=(2650560003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987045053/10000000000 : ℝ)|^4249 ≤ (11895290778223/100000000000000 : ℝ)^3225
        have hw : |(-1987045053/10000000000 : ℝ)|=(1987045053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433614429/10000000000 : ℝ)|^4249 ≤ (4476868965657/10000000000000 : ℝ)^3225
        have hw : |(5433614429/10000000000 : ℝ)|=(5433614429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301120031/10000000000 : ℝ)*x 0 + (2716807191/5000000000 : ℝ)*x 1 + (-397409017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301120031/10000000000 : ℝ)^4249 ≤ (43336019819127/100000000000000 : ℝ)^3225 := by
    have hnat : (5301120031 : ℕ)^4249*100000000000000^3225 ≤ 43336019819127^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301120031 10000000000 43336019819127 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716807191/5000000000 : ℝ)^4249 ≤ (4476868914637/10000000000000 : ℝ)^3225 := by
    have hnat : (2716807191 : ℕ)^4249*10000000000000^3225 ≤ 4476868914637^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716807191 5000000000 4476868914637 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397409017/2000000000 : ℝ)^4249 ≤ (5947645515307/50000000000000 : ℝ)^3225 := by
    have hnat : (397409017 : ℕ)^4249*50000000000000^3225 ≤ 5947645515307^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397409017 2000000000 5947645515307 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301120031/10000000000 : ℝ), (2716807191/5000000000 : ℝ), (-397409017/2000000000 : ℝ)] ![(43336019819127/100000000000000 : ℝ), (4476868914637/10000000000000 : ℝ), (5947645515307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301120031/10000000000 : ℝ)|^4249 ≤ (43336019819127/100000000000000 : ℝ)^3225
        have hw : |(5301120031/10000000000 : ℝ)|=(5301120031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716807191/5000000000 : ℝ)|^4249 ≤ (4476868914637/10000000000000 : ℝ)^3225
        have hw : |(2716807191/5000000000 : ℝ)|=(2716807191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-397409017/2000000000 : ℝ)|^4249 ≤ (5947645515307/50000000000000 : ℝ)^3225
        have hw : |(-397409017/2000000000 : ℝ)|=(397409017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s3_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (867855169/2000000000 : ℝ)*x 0 + (2278597789/5000000000 : ℝ)*x 1 + (2065719403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867855169/2000000000 : ℝ)^4249 ≤ (6657638461179/20000000000000 : ℝ)^3225 := by
    have hnat : (867855169 : ℕ)^4249*20000000000000^3225 ≤ 6657638461179^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867855169 2000000000 6657638461179 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278597789/5000000000 : ℝ)^4249 ≤ (8877027615971/25000000000000 : ℝ)^3225 := by
    have hnat : (2278597789 : ℕ)^4249*25000000000000^3225 ≤ 8877027615971^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278597789 5000000000 8877027615971 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065719403/5000000000 : ℝ)^4249 ≤ (31203697215529/100000000000000 : ℝ)^3225 := by
    have hnat : (2065719403 : ℕ)^4249*100000000000000^3225 ≤ 31203697215529^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065719403 5000000000 31203697215529 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867855169/2000000000 : ℝ), (2278597789/5000000000 : ℝ), (2065719403/5000000000 : ℝ)] ![(6657638461179/20000000000000 : ℝ), (8877027615971/25000000000000 : ℝ), (31203697215529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867855169/2000000000 : ℝ)|^4249 ≤ (6657638461179/20000000000000 : ℝ)^3225
        have hw : |(867855169/2000000000 : ℝ)|=(867855169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2278597789/5000000000 : ℝ)|^4249 ≤ (8877027615971/25000000000000 : ℝ)^3225
        have hw : |(2278597789/5000000000 : ℝ)|=(2278597789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2065719403/5000000000 : ℝ)|^4249 ≤ (31203697215529/100000000000000 : ℝ)^3225
        have hw : |(2065719403/5000000000 : ℝ)|=(2065719403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2129/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1507/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16331/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9483/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16331/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9483/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16331/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9483/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9483/100000 : ℝ) ^ (531/128 : ℝ) ≤ (570063699752861/10000000000000000000 : ℝ) := by
    have hpowers : (9483/100000 : ℝ)^531 ≤ (570063699752861/10000000000000000000 : ℝ)^128 := by
      have hnat : (9483 : ℕ)^531*10000000000000000000^128 ≤ 570063699752861^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9483 100000 570063699752861 10000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9483/100000 : ℝ)) (X := (570063699752861/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (16331/100000 : ℝ) ^ (531/128 : ℝ) ≤ (54354148877339569/100000000000000000000 : ℝ) := by
    have hpowers : (16331/100000 : ℝ)^531 ≤ (54354148877339569/100000000000000000000 : ℝ)^128 := by
      have hnat : (16331 : ℕ)^531*100000000000000000000^128 ≤ 54354148877339569^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16331 100000 54354148877339569 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16331/100000 : ℝ)) (X := (54354148877339569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000570063699752861/5000000000000000000 : ℝ) ≤ (10000274821080349/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (5000570063699752861/5000000000000000000 : ℝ)^128 ≤ (10000274821080349/10000000000000000 : ℝ)^531 := by
      have hnat : (5000570063699752861 : ℕ)^128*10000000000000000^531 ≤ 10000274821080349^531*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000570063699752861 5000000000000000000 10000274821080349 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000274821080349/10000000000000000 : ℝ)) (X := (5000570063699752861/5000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060054785874868179/100000000000000000000 : ℝ) ≤ (2500361829632939/2500000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (100060054785874868179/100000000000000000000 : ℝ)^128 ≤ (2500361829632939/2500000000000000 : ℝ)^531 := by
      have hnat : (100060054785874868179 : ℕ)^128*2500000000000000^531 ≤ 2500361829632939^531*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060054785874868179 100000000000000000000 2500361829632939 2500000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500361829632939/2500000000000000 : ℝ)) (X := (100060054785874868179/100000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50054354148877339569/50000000000000000000 : ℝ) ≤ (10002619815983163/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50054354148877339569/50000000000000000000 : ℝ)^128 ≤ (10002619815983163/10000000000000000 : ℝ)^531 := by
      have hnat : (50054354148877339569 : ℕ)^128*10000000000000000^531 ≤ 10002619815983163^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50054354148877339569 50000000000000000000 10002619815983163 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002619815983163/10000000000000000 : ℝ)) (X := (50054354148877339569/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(570063699752861/10000000000000000000 : ℝ) ≤ ((6845964438809484479/6848000000000000000 : ℝ)+2*(1172497451407/684800000000000 : ℝ)*(9483/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (6845964438809484479/6848000000000000000 : ℝ)+2*(1172497451407/684800000000000 : ℝ)*(9483/100000 : ℝ)=(10000274821080349/10000000000000000 : ℝ) by norm_num, show 1+2*(570063699752861/10000000000000000000 : ℝ)=(5000570063699752861/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54354148877339569/100000000000000000000 : ℝ)+(570063699752861/10000000000000000000 : ℝ) ≤ ((6845964438809484479/6848000000000000000 : ℝ)+(1172497451407/684800000000000 : ℝ)*((16331/100000 : ℝ)+(9483/100000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (6845964438809484479/6848000000000000000 : ℝ)+(1172497451407/684800000000000 : ℝ)*((16331/100000 : ℝ)+(9483/100000 : ℝ))=(2500361829632939/2500000000000000 : ℝ) by norm_num, show 1+(54354148877339569/100000000000000000000 : ℝ)+(570063699752861/10000000000000000000 : ℝ)=(100060054785874868179/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54354148877339569/100000000000000000000 : ℝ) ≤ ((6845964438809484479/6848000000000000000 : ℝ)+2*(1172497451407/684800000000000 : ℝ)*(16331/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (6845964438809484479/6848000000000000000 : ℝ)+2*(1172497451407/684800000000000 : ℝ)*(16331/100000 : ℝ)=(10002619815983163/10000000000000000 : ℝ) by norm_num, show 1+2*(54354148877339569/100000000000000000000 : ℝ)=(50054354148877339569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6845964438809484479/6848000000000000000 : ℝ)*(X 1 0+X 2 0)+(1172497451407/684800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (9483/100000 : ℝ)) (hi := (16331/100000 : ℝ)) (c := (6845964438809484479/6848000000000000000 : ℝ)) (alpha := (1172497451407/684800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6845964438809484479/6848000000000000000 : ℝ)*(X 0 1+X 2 1)+(1172497451407/684800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (9483/100000 : ℝ)) (hi := (16331/100000 : ℝ)) (c := (6845964438809484479/6848000000000000000 : ℝ)) (alpha := (1172497451407/684800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6845964438809484479/6848000000000000000 : ℝ)*(X 0 2+X 1 2)+(1172497451407/684800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (9483/100000 : ℝ)) (hi := (16331/100000 : ℝ)) (c := (6845964438809484479/6848000000000000000 : ℝ)) (alpha := (1172497451407/684800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104413199/500000000 : ℝ)*X 0 0+(169828843/312500000 : ℝ)*X 0 1+(2612658453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535466609/1000000000 : ℝ)*X 1 0+(-219534271/1000000000 : ℝ)*X 1 1+(5225316957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535466613/1000000000 : ℝ)*X 2 0+(261265837/500000000 : ℝ)*X 2 1+(-2195342943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867845859/2000000000 : ℝ)*X 0 0+(4129573609/10000000000 : ℝ)*X 0 1+(1139762291/2500000000 : ℝ)*X 0 2+(867845859/2000000000 : ℝ)*X 1 0+(4129573609/10000000000 : ℝ)*X 1 1+(1139762291/2500000000 : ℝ)*X 1 2+(867845859/2000000000 : ℝ)*X 2 0+(4129573609/10000000000 : ℝ)*X 2 1+(1139762291/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2088286773/10000000000 : ℝ)*X 0 0+(5226219713/10000000000 : ℝ)*X 0 1+(5433614481/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650560003/5000000000 : ℝ)*X 1 0+(-1987045053/10000000000 : ℝ)*X 1 1+(5433614429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301120031/10000000000 : ℝ)*X 2 0+(2716807191/5000000000 : ℝ)*X 2 1+(-397409017/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867855169/2000000000 : ℝ)*X 0 0+(2278597789/5000000000 : ℝ)*X 0 1+(2065719403/5000000000 : ℝ)*X 0 2+(867855169/2000000000 : ℝ)*X 1 0+(2278597789/5000000000 : ℝ)*X 1 1+(2065719403/5000000000 : ℝ)*X 1 2+(867855169/2000000000 : ℝ)*X 2 0+(2278597789/5000000000 : ℝ)*X 2 1+(2065719403/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2907683883793744043798673/1369600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (346361749/100000000000000 : ℝ)*(base19) + (239888521/50000000000000 : ℝ)*(base23) + (130613059/100000000000000 : ℝ)*(upper3) + (54633959/100000000000000 : ℝ)*(lower4) + (14216828833257/400000000000 : ℝ)*(major0) + (14216828833257/400000000000 : ℝ)*(major1) + (14216828833257/400000000000 : ℝ)*(major2) + (191199344221057/4000000000000 : ℝ)*(sp0) + (4779986098450267/100000000000000 : ℝ)*(sp1) + (1194996383199101/25000000000000 : ℝ)*(sp2) + (2328423878281373/100000000000000 : ℝ)*(sp3) + (2839285591/100000000000000 : ℝ)*(sp4) + (432238571/100000000000000 : ℝ)*(sp6) + (4022767867/100000000000000 : ℝ)*(sp7) + (58210697526231/2500000000000 : ℝ)*(f.failure) + (298749152800751/6250000000000 : ℝ)*(f.sum) + (2633514373807/3424000000000000000000000000 : ℝ)*base65 + (34512806968440903/2739200000000000000000000000000 : ℝ)*base67 + (17243575820844103/2739200000000000000000000000000 : ℝ)*base69 + (30649803015852103/2739200000000000000000000000000 : ℝ)*base71 + (7753290071663/3424000000000000000000000000 : ℝ)*base73 + (58217095892882503/2739200000000000000000000000000 : ℝ)*base75 + (32492829385464903/2739200000000000000000000000000 : ℝ)*base77 + (32006343373100103/2739200000000000000000000000000 : ℝ)*base79 + (4733511233967/3424000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1647453/125000000000000000000 : ℝ)*base90 + (1647453/125000000000000000000 : ℝ)*base92 + (1647453/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87322695847966200319311/17120000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1389473371/100000000000000 : ℝ)*(base19) + (721417563/50000000000000 : ℝ)*(base23) + (26000707/20000000000000 : ℝ)*(upper3) + (1188421/6250000000000 : ℝ)*(lower4) + (149979907/100000000000000 : ℝ)*(upper5) + (1792620372637771/50000000000000 : ℝ)*(major0) + (1792620372637771/50000000000000 : ℝ)*(major1) + (1792620372637771/50000000000000 : ℝ)*(major2) + (1150783581/5000000000000 : ℝ)*(sp1) + (22496237449/100000000000000 : ℝ)*(sp2) + (2410861383256461/50000000000000 : ℝ)*(sp4) + (1205424590341983/25000000000000 : ℝ)*(sp5) + (4821698827440347/100000000000000 : ℝ)*(sp6) + (234875855401733/10000000000000 : ℝ)*(sp7) + (234875855401733/10000000000000 : ℝ)*(f.failure) + (2410861383256461/50000000000000 : ℝ)*(f.sum) + (91098243731483/17120000000000000000000000000 : ℝ)*base66 + (1023734264509226309/342400000000000000000000000000000 : ℝ)*base67 + (814893090262826309/342400000000000000000000000000000 : ℝ)*base69 + (4178454776809173691/342400000000000000000000000000000 : ℝ)*base72 + (34514226508517/17120000000000000000000000000 : ℝ)*base73 + (2393370149423573691/342400000000000000000000000000000 : ℝ)*base76 + (1609009758073173691/342400000000000000000000000000000 : ℝ)*base78 + (2477141653962026309/342400000000000000000000000000000 : ℝ)*base79 + (32424201961563/17120000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5890121/500000000000000000000 : ℝ)*base89 + (5890121/500000000000000000000 : ℝ)*base91 + (5890121/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1289_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1507/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1289_s4_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-261277071/1250000000 : ℝ)*x 0 + (1354790009/2500000000 : ℝ)*x 1 + (5239400049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261277071/1250000000 : ℝ)^4249 ≤ (6357829085903/50000000000000 : ℝ)^3225 := by
    have hnat : (261277071 : ℕ)^4249*50000000000000^3225 ≤ 6357829085903^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261277071 1250000000 6357829085903 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354790009/2500000000 : ℝ)^4249 ≤ (44611848920771/100000000000000 : ℝ)^3225 := by
    have hnat : (1354790009 : ℕ)^4249*100000000000000^3225 ≤ 44611848920771^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354790009 2500000000 44611848920771 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239400049/10000000000 : ℝ)^4249 ≤ (42672492897751/100000000000000 : ℝ)^3225 := by
    have hnat : (5239400049 : ℕ)^4249*100000000000000^3225 ≤ 42672492897751^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239400049 10000000000 42672492897751 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261277071/1250000000 : ℝ), (1354790009/2500000000 : ℝ), (5239400049/10000000000 : ℝ)] ![(6357829085903/50000000000000 : ℝ), (44611848920771/100000000000000 : ℝ), (42672492897751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261277071/1250000000 : ℝ)|^4249 ≤ (6357829085903/50000000000000 : ℝ)^3225
        have hw : |(-261277071/1250000000 : ℝ)|=(261277071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354790009/2500000000 : ℝ)|^4249 ≤ (44611848920771/100000000000000 : ℝ)^3225
        have hw : |(1354790009/2500000000 : ℝ)|=(1354790009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239400049/10000000000 : ℝ)|^4249 ≤ (42672492897751/100000000000000 : ℝ)^3225
        have hw : |(5239400049/10000000000 : ℝ)|=(5239400049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668848143/1250000000 : ℝ)*x 0 + (-2181924937/10000000000 : ℝ)*x 1 + (2619700013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668848143/1250000000 : ℝ)^4249 ≤ (21935867490591/50000000000000 : ℝ)^3225 := by
    have hnat : (668848143 : ℕ)^4249*50000000000000^3225 ≤ 21935867490591^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668848143 1250000000 21935867490591 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181924937/10000000000 : ℝ)^4249 ≤ (13455772351323/100000000000000 : ℝ)^3225 := by
    have hnat : (2181924937 : ℕ)^4249*100000000000000^3225 ≤ 13455772351323^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181924937 10000000000 13455772351323 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619700013/5000000000 : ℝ)^4249 ≤ (10668123162737/25000000000000 : ℝ)^3225 := by
    have hnat : (2619700013 : ℕ)^4249*25000000000000^3225 ≤ 10668123162737^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619700013 5000000000 10668123162737 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668848143/1250000000 : ℝ), (-2181924937/10000000000 : ℝ), (2619700013/5000000000 : ℝ)] ![(21935867490591/50000000000000 : ℝ), (13455772351323/100000000000000 : ℝ), (10668123162737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668848143/1250000000 : ℝ)|^4249 ≤ (21935867490591/50000000000000 : ℝ)^3225
        have hw : |(668848143/1250000000 : ℝ)|=(668848143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2181924937/10000000000 : ℝ)|^4249 ≤ (13455772351323/100000000000000 : ℝ)^3225
        have hw : |(-2181924937/10000000000 : ℝ)|=(2181924937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619700013/5000000000 : ℝ)|^4249 ≤ (10668123162737/25000000000000 : ℝ)^3225
        have hw : |(2619700013/5000000000 : ℝ)|=(2619700013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350785143/10000000000 : ℝ)*x 0 + (2619700013/5000000000 : ℝ)*x 1 + (-2181924939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350785143/10000000000 : ℝ)^4249 ≤ (2193586748519/5000000000000 : ℝ)^3225 := by
    have hnat : (5350785143 : ℕ)^4249*5000000000000^3225 ≤ 2193586748519^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350785143 10000000000 2193586748519 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619700013/5000000000 : ℝ)^4249 ≤ (10668123162737/25000000000000 : ℝ)^3225 := by
    have hnat : (2619700013 : ℕ)^4249*25000000000000^3225 ≤ 10668123162737^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619700013 5000000000 10668123162737 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181924939/10000000000 : ℝ)^4249 ≤ (13455772367573/100000000000000 : ℝ)^3225 := by
    have hnat : (2181924939 : ℕ)^4249*100000000000000^3225 ≤ 13455772367573^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181924939 10000000000 13455772367573 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350785143/10000000000 : ℝ), (2619700013/5000000000 : ℝ), (-2181924939/10000000000 : ℝ)] ![(2193586748519/5000000000000 : ℝ), (10668123162737/25000000000000 : ℝ), (13455772367573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350785143/10000000000 : ℝ)|^4249 ≤ (2193586748519/5000000000000 : ℝ)^3225
        have hw : |(5350785143/10000000000 : ℝ)|=(5350785143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619700013/5000000000 : ℝ)|^4249 ≤ (10668123162737/25000000000000 : ℝ)^3225
        have hw : |(2619700013/5000000000 : ℝ)|=(2619700013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181924939/10000000000 : ℝ)|^4249 ≤ (13455772367573/100000000000000 : ℝ)^3225
        have hw : |(-2181924939/10000000000 : ℝ)|=(2181924939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173616371/400000000 : ℝ)*x 0 + (2079824847/5000000000 : ℝ)*x 1 + (1132168941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173616371/400000000 : ℝ)^4249 ≤ (1664982428051/5000000000000 : ℝ)^3225 := by
    have hnat : (173616371 : ℕ)^4249*5000000000000^3225 ≤ 1664982428051^3225*400000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173616371 400000000 1664982428051 5000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079824847/5000000000 : ℝ)^4249 ≤ (31484724391911/100000000000000 : ℝ)^3225 := by
    have hnat : (2079824847 : ℕ)^4249*100000000000000^3225 ≤ 31484724391911^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079824847 5000000000 31484724391911 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132168941/2500000000 : ℝ)^4249 ≤ (3521562703057/10000000000000 : ℝ)^3225 := by
    have hnat : (1132168941 : ℕ)^4249*10000000000000^3225 ≤ 3521562703057^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132168941 2500000000 3521562703057 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173616371/400000000 : ℝ), (2079824847/5000000000 : ℝ), (1132168941/2500000000 : ℝ)] ![(1664982428051/5000000000000 : ℝ), (31484724391911/100000000000000 : ℝ), (3521562703057/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173616371/400000000 : ℝ)|^4249 ≤ (1664982428051/5000000000000 : ℝ)^3225
        have hw : |(173616371/400000000 : ℝ)|=(173616371/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079824847/5000000000 : ℝ)|^4249 ≤ (31484724391911/100000000000000 : ℝ)^3225
        have hw : |(2079824847/5000000000 : ℝ)|=(2079824847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132168941/2500000000 : ℝ)|^4249 ≤ (3521562703057/10000000000000 : ℝ)^3225
        have hw : |(1132168941/2500000000 : ℝ)|=(1132168941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-418046191/2000000000 : ℝ)*x 0 + (2620033697/5000000000 : ℝ)*x 1 + (5418489141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (418046191/2000000000 : ℝ)^4249 ≤ (6357886742007/50000000000000 : ℝ)^3225 := by
    have hnat : (418046191 : ℕ)^4249*50000000000000^3225 ≤ 6357886742007^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418046191 2000000000 6357886742007 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620033697/5000000000 : ℝ)^4249 ≤ (266747837787/625000000000 : ℝ)^3225 := by
    have hnat : (2620033697 : ℕ)^4249*625000000000^3225 ≤ 266747837787^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620033697 5000000000 266747837787 625000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418489141/10000000000 : ℝ)^4249 ≤ (44604572441821/100000000000000 : ℝ)^3225 := by
    have hnat : (5418489141 : ℕ)^4249*100000000000000^3225 ≤ 44604572441821^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418489141 10000000000 44604572441821 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-418046191/2000000000 : ℝ), (2620033697/5000000000 : ℝ), (5418489141/10000000000 : ℝ)] ![(6357886742007/50000000000000 : ℝ), (266747837787/625000000000 : ℝ), (44604572441821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-418046191/2000000000 : ℝ)|^4249 ≤ (6357886742007/50000000000000 : ℝ)^3225
        have hw : |(-418046191/2000000000 : ℝ)|=(418046191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620033697/5000000000 : ℝ)|^4249 ≤ (266747837787/625000000000 : ℝ)^3225
        have hw : |(2620033697/5000000000 : ℝ)|=(2620033697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418489141/10000000000 : ℝ)|^4249 ≤ (44604572441821/100000000000000 : ℝ)^3225
        have hw : |(5418489141/10000000000 : ℝ)|=(5418489141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652389621/5000000000 : ℝ)*x 0 + (-10014179/50000000 : ℝ)*x 1 + (5418489031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652389621/5000000000 : ℝ)^4249 ≤ (43375435899179/100000000000000 : ℝ)^3225 := by
    have hnat : (2652389621 : ℕ)^4249*100000000000000^3225 ≤ 43375435899179^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652389621 5000000000 43375435899179 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10014179/50000000 : ℝ)^4249 ≤ (480799713527/4000000000000 : ℝ)^3225 := by
    have hnat : (10014179 : ℕ)^4249*4000000000000^3225 ≤ 480799713527^3225*50000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10014179 50000000 480799713527 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5418489031/10000000000 : ℝ)^4249 ≤ (5575571406099/12500000000000 : ℝ)^3225 := by
    have hnat : (5418489031 : ℕ)^4249*12500000000000^3225 ≤ 5575571406099^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418489031 10000000000 5575571406099 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652389621/5000000000 : ℝ), (-10014179/50000000 : ℝ), (5418489031/10000000000 : ℝ)] ![(43375435899179/100000000000000 : ℝ), (480799713527/4000000000000 : ℝ), (5575571406099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652389621/5000000000 : ℝ)|^4249 ≤ (43375435899179/100000000000000 : ℝ)^3225
        have hw : |(2652389621/5000000000 : ℝ)|=(2652389621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10014179/50000000 : ℝ)|^4249 ≤ (480799713527/4000000000000 : ℝ)^3225
        have hw : |(-10014179/50000000 : ℝ)|=(10014179/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5418489031/10000000000 : ℝ)|^4249 ≤ (5575571406099/12500000000000 : ℝ)^3225
        have hw : |(5418489031/10000000000 : ℝ)|=(5418489031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304779231/10000000000 : ℝ)*x 0 + (2709244557/5000000000 : ℝ)*x 1 + (-1001417851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304779231/10000000000 : ℝ)^4249 ≤ (43375435780677/100000000000000 : ℝ)^3225 := by
    have hnat : (5304779231 : ℕ)^4249*100000000000000^3225 ≤ 43375435780677^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304779231 10000000000 43375435780677 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709244557/5000000000 : ℝ)^4249 ≤ (22302286074493/50000000000000 : ℝ)^3225 := by
    have hnat : (2709244557 : ℕ)^4249*50000000000000^3225 ≤ 22302286074493^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709244557 5000000000 22302286074493 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1001417851/5000000000 : ℝ)^4249 ≤ (12019992063281/100000000000000 : ℝ)^3225 := by
    have hnat : (1001417851 : ℕ)^4249*100000000000000^3225 ≤ 12019992063281^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001417851 5000000000 12019992063281 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304779231/10000000000 : ℝ), (2709244557/5000000000 : ℝ), (-1001417851/5000000000 : ℝ)] ![(43375435780677/100000000000000 : ℝ), (22302286074493/50000000000000 : ℝ), (12019992063281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304779231/10000000000 : ℝ)|^4249 ≤ (43375435780677/100000000000000 : ℝ)^3225
        have hw : |(5304779231/10000000000 : ℝ)|=(5304779231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709244557/5000000000 : ℝ)|^4249 ≤ (22302286074493/50000000000000 : ℝ)^3225
        have hw : |(2709244557/5000000000 : ℝ)|=(2709244557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1001417851/5000000000 : ℝ)|^4249 ≤ (12019992063281/100000000000000 : ℝ)^3225
        have hw : |(-1001417851/5000000000 : ℝ)|=(1001417851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s4_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108510967/250000000 : ℝ)*x 0 + (452730597/1000000000 : ℝ)*x 1 + (832205403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108510967/250000000 : ℝ)^4249 ≤ (3329994578759/10000000000000 : ℝ)^3225 := by
    have hnat : (108510967 : ℕ)^4249*10000000000000^3225 ≤ 3329994578759^3225*250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108510967 250000000 3329994578759 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452730597/1000000000 : ℝ)^4249 ≤ (8800398466547/25000000000000 : ℝ)^3225 := by
    have hnat : (452730597 : ℕ)^4249*25000000000000^3225 ≤ 8800398466547^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452730597 1000000000 8800398466547 25000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832205403/2000000000 : ℝ)^4249 ≤ (31498460324377/100000000000000 : ℝ)^3225 := by
    have hnat : (832205403 : ℕ)^4249*100000000000000^3225 ≤ 31498460324377^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832205403 2000000000 31498460324377 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108510967/250000000 : ℝ), (452730597/1000000000 : ℝ), (832205403/2000000000 : ℝ)] ![(3329994578759/10000000000000 : ℝ), (8800398466547/25000000000000 : ℝ), (31498460324377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108510967/250000000 : ℝ)|^4249 ≤ (3329994578759/10000000000000 : ℝ)^3225
        have hw : |(108510967/250000000 : ℝ)|=(108510967/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452730597/1000000000 : ℝ)|^4249 ≤ (8800398466547/25000000000000 : ℝ)^3225
        have hw : |(452730597/1000000000 : ℝ)|=(452730597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832205403/2000000000 : ℝ)|^4249 ≤ (31498460324377/100000000000000 : ℝ)^3225
        have hw : |(832205403/2000000000 : ℝ)|=(832205403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1507/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2189/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1507/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2129/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1507/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2129/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1507/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2129/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1507/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2129/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1507/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2129/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1507/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2129/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2129/20000 : ℝ) ^ (531/128 : ℝ) ≤ (4604098456018599/50000000000000000000 : ℝ) := by
    have hpowers : (2129/20000 : ℝ)^531 ≤ (4604098456018599/50000000000000000000 : ℝ)^128 := by
      have hnat : (2129 : ℕ)^531*50000000000000000000^128 ≤ 4604098456018599^128*20000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2129 20000 4604098456018599 50000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2129/20000 : ℝ)) (X := (4604098456018599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (1507/10000 : ℝ) ^ (531/128 : ℝ) ≤ (38945223017933771/100000000000000000000 : ℝ) := by
    have hpowers : (1507/10000 : ℝ)^531 ≤ (38945223017933771/100000000000000000000 : ℝ)^128 := by
      have hnat : (1507 : ℕ)^531*100000000000000000000^128 ≤ 38945223017933771^128*10000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1507 10000 38945223017933771 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1507/10000 : ℝ)) (X := (38945223017933771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004604098456018599/25000000000000000000 : ℝ) ≤ (10000443904649159/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (25004604098456018599/25000000000000000000 : ℝ)^128 ≤ (10000443904649159/10000000000000000 : ℝ)^531 := by
      have hnat : (25004604098456018599 : ℕ)^128*10000000000000000^531 ≤ 10000443904649159^531*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004604098456018599 25000000000000000000 10000443904649159 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000443904649159/10000000000000000 : ℝ)) (X := (25004604098456018599/25000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048153419929970969/100000000000000000000 : ℝ) ≤ (2500290137090069/2500000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (100048153419929970969/100000000000000000000 : ℝ)^128 ≤ (2500290137090069/2500000000000000 : ℝ)^531 := by
      have hnat : (100048153419929970969 : ℕ)^128*2500000000000000^531 ≤ 2500290137090069^531*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048153419929970969 100000000000000000000 2500290137090069 2500000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290137090069/2500000000000000 : ℝ)) (X := (100048153419929970969/100000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038945223017933771/50000000000000000000 : ℝ) ≤ (10001877192071393/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50038945223017933771/50000000000000000000 : ℝ)^128 ≤ (10001877192071393/10000000000000000 : ℝ)^531 := by
      have hnat : (50038945223017933771 : ℕ)^128*10000000000000000^531 ≤ 10001877192071393^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038945223017933771 50000000000000000000 10001877192071393 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001877192071393/10000000000000000 : ℝ)) (X := (50038945223017933771/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4604098456018599/50000000000000000000 : ℝ) ≤ ((2949113795564189843/2950000000000000000 : ℝ)+2*(238881237039/147500000000000 : ℝ)*(2129/20000 : ℝ))^(531/128 : ℝ) := by
    rw [show (2949113795564189843/2950000000000000000 : ℝ)+2*(238881237039/147500000000000 : ℝ)*(2129/20000 : ℝ)=(10000443904649159/10000000000000000 : ℝ) by norm_num, show 1+2*(4604098456018599/50000000000000000000 : ℝ)=(25004604098456018599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38945223017933771/100000000000000000000 : ℝ)+(4604098456018599/50000000000000000000 : ℝ) ≤ ((2949113795564189843/2950000000000000000 : ℝ)+(238881237039/147500000000000 : ℝ)*((1507/10000 : ℝ)+(2129/20000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (2949113795564189843/2950000000000000000 : ℝ)+(238881237039/147500000000000 : ℝ)*((1507/10000 : ℝ)+(2129/20000 : ℝ))=(2500290137090069/2500000000000000 : ℝ) by norm_num, show 1+(38945223017933771/100000000000000000000 : ℝ)+(4604098456018599/50000000000000000000 : ℝ)=(100048153419929970969/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38945223017933771/100000000000000000000 : ℝ) ≤ ((2949113795564189843/2950000000000000000 : ℝ)+2*(238881237039/147500000000000 : ℝ)*(1507/10000 : ℝ))^(531/128 : ℝ) := by
    rw [show (2949113795564189843/2950000000000000000 : ℝ)+2*(238881237039/147500000000000 : ℝ)*(1507/10000 : ℝ)=(10001877192071393/10000000000000000 : ℝ) by norm_num, show 1+2*(38945223017933771/100000000000000000000 : ℝ)=(50038945223017933771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2949113795564189843/2950000000000000000 : ℝ)*(X 1 0+X 2 0)+(238881237039/147500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (2129/20000 : ℝ)) (hi := (1507/10000 : ℝ)) (c := (2949113795564189843/2950000000000000000 : ℝ)) (alpha := (238881237039/147500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2949113795564189843/2950000000000000000 : ℝ)*(X 0 1+X 2 1)+(238881237039/147500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (2129/20000 : ℝ)) (hi := (1507/10000 : ℝ)) (c := (2949113795564189843/2950000000000000000 : ℝ)) (alpha := (238881237039/147500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2949113795564189843/2950000000000000000 : ℝ)*(X 0 2+X 1 2)+(238881237039/147500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (2129/20000 : ℝ)) (hi := (1507/10000 : ℝ)) (c := (2949113795564189843/2950000000000000000 : ℝ)) (alpha := (238881237039/147500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261277071/1250000000 : ℝ)*X 0 0+(1354790009/2500000000 : ℝ)*X 0 1+(5239400049/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668848143/1250000000 : ℝ)*X 1 0+(-2181924937/10000000000 : ℝ)*X 1 1+(2619700013/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350785143/10000000000 : ℝ)*X 2 0+(2619700013/5000000000 : ℝ)*X 2 1+(-2181924939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173616371/400000000 : ℝ)*X 0 0+(2079824847/5000000000 : ℝ)*X 0 1+(1132168941/2500000000 : ℝ)*X 0 2+(173616371/400000000 : ℝ)*X 1 0+(2079824847/5000000000 : ℝ)*X 1 1+(1132168941/2500000000 : ℝ)*X 1 2+(173616371/400000000 : ℝ)*X 2 0+(2079824847/5000000000 : ℝ)*X 2 1+(1132168941/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-418046191/2000000000 : ℝ)*X 0 0+(2620033697/5000000000 : ℝ)*X 0 1+(5418489141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652389621/5000000000 : ℝ)*X 1 0+(-10014179/50000000 : ℝ)*X 1 1+(5418489031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304779231/10000000000 : ℝ)*X 2 0+(2709244557/5000000000 : ℝ)*X 2 1+(-1001417851/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108510967/250000000 : ℝ)*X 0 0+(452730597/1000000000 : ℝ)*X 0 1+(832205403/2000000000 : ℝ)*X 0 2+(108510967/250000000 : ℝ)*X 1 0+(452730597/1000000000 : ℝ)*X 1 1+(832205403/2000000000 : ℝ)*X 1 2+(108510967/250000000 : ℝ)*X 2 0+(452730597/1000000000 : ℝ)*X 2 1+(832205403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3652831854987838244787/368750000000000000000000000 : ℝ) := by norm_num
    linear_combination (2004333837/100000000000000 : ℝ)*(base19) + (950923211/50000000000000 : ℝ)*(base23) + (5428251/10000000000000 : ℝ)*(lower2) + (63882939/25000000000000 : ℝ)*(upper3) + (88624007/50000000000000 : ℝ)*(upper5) + (827292621030431/20000000000000 : ℝ)*(major0) + (827292621030431/20000000000000 : ℝ)*(major1) + (827292621030431/20000000000000 : ℝ)*(major2) + (222520516302091/4000000000000 : ℝ)*(sp0) + (5563049200156539/100000000000000 : ℝ)*(sp1) + (1112609860528791/20000000000000 : ℝ)*(sp2) + (67746358603817/2500000000000 : ℝ)*(sp3) + (19148469051/50000000000000 : ℝ)*(sp4) + (20331461753/100000000000000 : ℝ)*(sp7) + (1354937337807217/50000000000000 : ℝ)*(f.failure) + (5563051204490377/100000000000000 : ℝ)*(f.sum) + (2667579975441/1475000000000000000000000000 : ℝ)*base66 + (630532502621707667/59000000000000000000000000000000 : ℝ)*base68 + (223672845392292333/59000000000000000000000000000000 : ℝ)*base69 + (328475880663707667/59000000000000000000000000000000 : ℝ)*base72 + (1328905802621/368750000000000000000000000 : ℝ)*base73 + (324004814129292333/59000000000000000000000000000000 : ℝ)*base75 + (44574986345292333/59000000000000000000000000000000 : ℝ)*base77 + (1226928972399707667/59000000000000000000000000000000 : ℝ)*base80 + (6547722005559/1475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (39741029/2500000000000000000000 : ℝ)*base89 + (39741029/2500000000000000000000 : ℝ)*base91 + (39741029/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60491607893946805387796511/29500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599753769/100000000000000 : ℝ)*(base19) + (44016893/6250000000000 : ℝ)*(base23) + (562563/1562500000000 : ℝ)*(upper2) + (40633113/100000000000000 : ℝ)*(upper3) + (833485659212253/20000000000000 : ℝ)*(major0) + (833485659212253/20000000000000 : ℝ)*(major1) + (833485659212253/20000000000000 : ℝ)*(major2) + (15410713/160000000000 : ℝ)*(sp1) + (3799311861/25000000000000 : ℝ)*(sp2) + (253552989/100000000000000 : ℝ)*(sp3) + (5604695969970433/100000000000000 : ℝ)*(sp4) + (5604685738521039/100000000000000 : ℝ)*(sp5) + (5604680068452701/100000000000000 : ℝ)*(sp6) + (2730160300247/100000000000 : ℝ)*(sp7) + (273016055379999/10000000000000 : ℝ)*(f.failure) + (5604695969970433/100000000000000 : ℝ)*(f.sum) + (7449808464633/1475000000000000000000000000 : ℝ)*base66 + (389939658810913721/59000000000000000000000000000000 : ℝ)*base68 + (235049594989913721/59000000000000000000000000000000 : ℝ)*base70 + (772685252065913721/59000000000000000000000000000000 : ℝ)*base72 + (12512910223/368750000000000000000000000 : ℝ)*base73 + (160222337943913721/59000000000000000000000000000000 : ℝ)*base76 + (487910541180913721/59000000000000000000000000000000 : ℝ)*base78 + (349056721314913721/59000000000000000000000000000000 : ℝ)*base80 + (8402432963683/1475000000000000000000000000 : ℝ)*base82 + (7737963/500000000000000000000 : ℝ)*base89 + (7737963/500000000000000000000 : ℝ)*base91 + (7737963/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1289_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1507/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2129/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2189/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1289_s5_0 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-261323233/1250000000 : ℝ)*x 0 + (2708028979/5000000000 : ℝ)*x 1 + (327641197/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261323233/1250000000 : ℝ)^4249 ≤ (12718618169383/100000000000000 : ℝ)^3225 := by
    have hnat : (261323233 : ℕ)^4249*100000000000000^3225 ≤ 12718618169383^3225*1250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261323233 1250000000 12718618169383 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708028979/5000000000 : ℝ)^4249 ≤ (4457820640249/10000000000000 : ℝ)^3225 := by
    have hnat : (2708028979 : ℕ)^4249*10000000000000^3225 ≤ 4457820640249^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708028979 5000000000 4457820640249 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327641197/625000000 : ℝ)^4249 ≤ (4270317540791/10000000000000 : ℝ)^3225 := by
    have hnat : (327641197 : ℕ)^4249*10000000000000^3225 ≤ 4270317540791^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327641197 625000000 4270317540791 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261323233/1250000000 : ℝ), (2708028979/5000000000 : ℝ), (327641197/625000000 : ℝ)] ![(12718618169383/100000000000000 : ℝ), (4457820640249/10000000000000 : ℝ), (4270317540791/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261323233/1250000000 : ℝ)|^4249 ≤ (12718618169383/100000000000000 : ℝ)^3225
        have hw : |(-261323233/1250000000 : ℝ)|=(261323233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708028979/5000000000 : ℝ)|^4249 ≤ (4457820640249/10000000000000 : ℝ)^3225
        have hw : |(2708028979/5000000000 : ℝ)|=(2708028979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327641197/625000000 : ℝ)|^4249 ≤ (4270317540791/10000000000000 : ℝ)^3225
        have hw : |(327641197/625000000 : ℝ)|=(327641197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_1 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167187439/312500000 : ℝ)*x 0 + (-68099829/312500000 : ℝ)*x 1 + (5242259147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167187439/312500000 : ℝ)^4249 ≤ (8772646514909/20000000000000 : ℝ)^3225 := by
    have hnat : (167187439 : ℕ)^4249*20000000000000^3225 ≤ 8772646514909^3225*312500000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167187439 312500000 8772646514909 20000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68099829/312500000 : ℝ)^4249 ≤ (13433592060793/100000000000000 : ℝ)^3225 := by
    have hnat : (68099829 : ℕ)^4249*100000000000000^3225 ≤ 13433592060793^3225*312500000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68099829 312500000 13433592060793 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242259147/10000000000 : ℝ)^4249 ≤ (5337896919281/12500000000000 : ℝ)^3225 := by
    have hnat : (5242259147 : ℕ)^4249*12500000000000^3225 ≤ 5337896919281^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242259147 10000000000 5337896919281 12500000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167187439/312500000 : ℝ), (-68099829/312500000 : ℝ), (5242259147/10000000000 : ℝ)] ![(8772646514909/20000000000000 : ℝ), (13433592060793/100000000000000 : ℝ), (5337896919281/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167187439/312500000 : ℝ)|^4249 ≤ (8772646514909/20000000000000 : ℝ)^3225
        have hw : |(167187439/312500000 : ℝ)|=(167187439/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68099829/312500000 : ℝ)|^4249 ≤ (13433592060793/100000000000000 : ℝ)^3225
        have hw : |(-68099829/312500000 : ℝ)|=(68099829/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242259147/10000000000 : ℝ)|^4249 ≤ (5337896919281/12500000000000 : ℝ)^3225
        have hw : |(5242259147/10000000000 : ℝ)|=(5242259147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_2 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334374877/625000000 : ℝ)*x 0 + (5242259169/10000000000 : ℝ)*x 1 + (-54479863/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334374877/625000000 : ℝ)^4249 ≤ (43863232401713/100000000000000 : ℝ)^3225 := by
    have hnat : (334374877 : ℕ)^4249*100000000000000^3225 ≤ 43863232401713^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334374877 625000000 43863232401713 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242259169/10000000000 : ℝ)^4249 ≤ (21351587795181/50000000000000 : ℝ)^3225 := by
    have hnat : (5242259169 : ℕ)^4249*50000000000000^3225 ≤ 21351587795181^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242259169 10000000000 21351587795181 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54479863/250000000 : ℝ)^4249 ≤ (13433591995819/100000000000000 : ℝ)^3225 := by
    have hnat : (54479863 : ℕ)^4249*100000000000000^3225 ≤ 13433591995819^3225*250000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54479863 250000000 13433591995819 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334374877/625000000 : ℝ), (5242259169/10000000000 : ℝ), (-54479863/250000000 : ℝ)] ![(43863232401713/100000000000000 : ℝ), (21351587795181/50000000000000 : ℝ), (13433591995819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334374877/625000000 : ℝ)|^4249 ≤ (43863232401713/100000000000000 : ℝ)^3225
        have hw : |(334374877/625000000 : ℝ)|=(334374877/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242259169/10000000000 : ℝ)|^4249 ≤ (21351587795181/50000000000000 : ℝ)^3225
        have hw : |(5242259169/10000000000 : ℝ)|=(5242259169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54479863/250000000 : ℝ)|^4249 ≤ (13433591995819/100000000000000 : ℝ)^3225
        have hw : |(-54479863/250000000 : ℝ)|=(54479863/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_3 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170313191/5000000000 : ℝ)*x 0 + (166629649/400000000 : ℝ)*x 1 + (1130632383/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170313191/5000000000 : ℝ)^4249 ≤ (33301843099773/100000000000000 : ℝ)^3225 := by
    have hnat : (2170313191 : ℕ)^4249*100000000000000^3225 ≤ 33301843099773^3225*5000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170313191 5000000000 33301843099773 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166629649/400000000 : ℝ)^4249 ≤ (31545485758623/100000000000000 : ℝ)^3225 := by
    have hnat : (166629649 : ℕ)^4249*100000000000000^3225 ≤ 31545485758623^3225*400000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166629649 400000000 31545485758623 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130632383/2500000000 : ℝ)^4249 ≤ (549260486171/1562500000000 : ℝ)^3225 := by
    have hnat : (1130632383 : ℕ)^4249*1562500000000^3225 ≤ 549260486171^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130632383 2500000000 549260486171 1562500000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170313191/5000000000 : ℝ), (166629649/400000000 : ℝ), (1130632383/2500000000 : ℝ)] ![(33301843099773/100000000000000 : ℝ), (31545485758623/100000000000000 : ℝ), (549260486171/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170313191/5000000000 : ℝ)|^4249 ≤ (33301843099773/100000000000000 : ℝ)^3225
        have hw : |(2170313191/5000000000 : ℝ)|=(2170313191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166629649/400000000 : ℝ)|^4249 ≤ (31545485758623/100000000000000 : ℝ)^3225
        have hw : |(166629649/400000000 : ℝ)|=(166629649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130632383/2500000000 : ℝ)|^4249 ≤ (549260486171/1562500000000 : ℝ)^3225
        have hw : |(1130632383/2500000000 : ℝ)|=(1130632383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_4 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-209059891/1000000000 : ℝ)*x 0 + (327680193/625000000 : ℝ)*x 1 + (1083086157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209059891/1000000000 : ℝ)^4249 ≤ (12718722739293/100000000000000 : ℝ)^3225 := by
    have hnat : (209059891 : ℕ)^4249*100000000000000^3225 ≤ 12718722739293^3225*1000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209059891 1000000000 12718722739293 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327680193/625000000 : ℝ)^4249 ≤ (21354935946809/50000000000000 : ℝ)^3225 := by
    have hnat : (327680193 : ℕ)^4249*50000000000000^3225 ≤ 21354935946809^3225*625000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327680193 625000000 21354935946809 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083086157/2000000000 : ℝ)^4249 ≤ (4457140535717/10000000000000 : ℝ)^3225 := by
    have hnat : (1083086157 : ℕ)^4249*10000000000000^3225 ≤ 4457140535717^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083086157 2000000000 4457140535717 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209059891/1000000000 : ℝ), (327680193/625000000 : ℝ), (1083086157/2000000000 : ℝ)] ![(12718722739293/100000000000000 : ℝ), (21354935946809/50000000000000 : ℝ), (4457140535717/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209059891/1000000000 : ℝ)|^4249 ≤ (12718722739293/100000000000000 : ℝ)^3225
        have hw : |(-209059891/1000000000 : ℝ)|=(209059891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327680193/625000000 : ℝ)|^4249 ≤ (21354935946809/50000000000000 : ℝ)^3225
        have hw : |(327680193/625000000 : ℝ)|=(327680193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083086157/2000000000 : ℝ)|^4249 ≤ (4457140535717/10000000000000 : ℝ)^3225
        have hw : |(1083086157/2000000000 : ℝ)|=(1083086157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_5 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305518009/10000000000 : ℝ)*x 0 + (-401204581/2000000000 : ℝ)*x 1 + (42308053/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305518009/10000000000 : ℝ)^4249 ≤ (43383394755017/100000000000000 : ℝ)^3225 := by
    have hnat : (5305518009 : ℕ)^4249*100000000000000^3225 ≤ 43383394755017^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305518009 10000000000 43383394755017 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401204581/2000000000 : ℝ)^4249 ≤ (12045199881677/100000000000000 : ℝ)^3225 := by
    have hnat : (401204581 : ℕ)^4249*100000000000000^3225 ≤ 12045199881677^3225*2000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401204581 2000000000 12045199881677 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42308053/78125000 : ℝ)^4249 ≤ (44571405346327/100000000000000 : ℝ)^3225 := by
    have hnat : (42308053 : ℕ)^4249*100000000000000^3225 ≤ 44571405346327^3225*78125000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42308053 78125000 44571405346327 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305518009/10000000000 : ℝ), (-401204581/2000000000 : ℝ), (42308053/78125000 : ℝ)] ![(43383394755017/100000000000000 : ℝ), (12045199881677/100000000000000 : ℝ), (44571405346327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305518009/10000000000 : ℝ)|^4249 ≤ (43383394755017/100000000000000 : ℝ)^3225
        have hw : |(5305518009/10000000000 : ℝ)|=(5305518009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-401204581/2000000000 : ℝ)|^4249 ≤ (12045199881677/100000000000000 : ℝ)^3225
        have hw : |(-401204581/2000000000 : ℝ)|=(401204581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42308053/78125000 : ℝ)|^4249 ≤ (44571405346327/100000000000000 : ℝ)^3225
        have hw : |(42308053/78125000 : ℝ)|=(42308053/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_6 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326379501/2500000000 : ℝ)*x 0 + (5415430787/10000000000 : ℝ)*x 1 + (-501505727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326379501/2500000000 : ℝ)^4249 ≤ (867667894023/2000000000000 : ℝ)^3225 := by
    have hnat : (1326379501 : ℕ)^4249*2000000000000^3225 ≤ 867667894023^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326379501 2500000000 867667894023 2000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415430787/10000000000 : ℝ)^4249 ≤ (22285702689429/50000000000000 : ℝ)^3225 := by
    have hnat : (5415430787 : ℕ)^4249*50000000000000^3225 ≤ 22285702689429^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415430787 10000000000 22285702689429 50000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501505727/2500000000 : ℝ)^4249 ≤ (1204519990541/10000000000000 : ℝ)^3225 := by
    have hnat : (501505727 : ℕ)^4249*10000000000000^3225 ≤ 1204519990541^3225*2500000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501505727 2500000000 1204519990541 10000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326379501/2500000000 : ℝ), (5415430787/10000000000 : ℝ), (-501505727/2500000000 : ℝ)] ![(867667894023/2000000000000 : ℝ), (22285702689429/50000000000000 : ℝ), (1204519990541/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326379501/2500000000 : ℝ)|^4249 ≤ (867667894023/2000000000000 : ℝ)^3225
        have hw : |(1326379501/2500000000 : ℝ)|=(1326379501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415430787/10000000000 : ℝ)|^4249 ≤ (22285702689429/50000000000000 : ℝ)^3225
        have hw : |(5415430787/10000000000 : ℝ)|=(5415430787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-501505727/2500000000 : ℝ)|^4249 ≤ (1204519990541/10000000000000 : ℝ)^3225
        have hw : |(-501505727/2500000000 : ℝ)|=(501505727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1289_s5_7 (p : ℝ) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340653209/10000000000 : ℝ)*x 0 + (4521248641/10000000000 : ℝ)*x 1 + (4167028677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340653209/10000000000 : ℝ)^4249 ≤ (260172767751/781250000000 : ℝ)^3225 := by
    have hnat : (4340653209 : ℕ)^4249*781250000000^3225 ≤ 260172767751^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340653209 10000000000 260172767751 781250000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521248641/10000000000 : ℝ)^4249 ≤ (1405582174193/4000000000000 : ℝ)^3225 := by
    have hnat : (4521248641 : ℕ)^4249*4000000000000^3225 ≤ 1405582174193^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521248641 10000000000 1405582174193 4000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4167028677/10000000000 : ℝ)^4249 ≤ (31558331355729/100000000000000 : ℝ)^3225 := by
    have hnat : (4167028677 : ℕ)^4249*100000000000000^3225 ≤ 31558331355729^3225*10000000000^4249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167028677 10000000000 31558331355729 100000000000000 4249 3225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4249/1024 : ℝ)) 4249 3225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340653209/10000000000 : ℝ), (4521248641/10000000000 : ℝ), (4167028677/10000000000 : ℝ)] ![(260172767751/781250000000 : ℝ), (1405582174193/4000000000000 : ℝ), (31558331355729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340653209/10000000000 : ℝ)|^4249 ≤ (260172767751/781250000000 : ℝ)^3225
        have hw : |(4340653209/10000000000 : ℝ)|=(4340653209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521248641/10000000000 : ℝ)|^4249 ≤ (1405582174193/4000000000000 : ℝ)^3225
        have hw : |(4521248641/10000000000 : ℝ)|=(4521248641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4167028677/10000000000 : ℝ)|^4249 ≤ (31558331355729/100000000000000 : ℝ)^3225
        have hw : |(4167028677/10000000000 : ℝ)|=(4167028677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1289_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2189/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5503/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2937/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2189/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2189/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2189/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2189/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2189/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2189/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2189/20000 : ℝ) ^ (531/128 : ℝ) ≤ (5166740602178107/50000000000000000000 : ℝ) := by
    have hpowers : (2189/20000 : ℝ)^531 ≤ (5166740602178107/50000000000000000000 : ℝ)^128 := by
      have hnat : (2189 : ℕ)^531*50000000000000000000^128 ≤ 5166740602178107^128*20000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2189 20000 5166740602178107 50000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2189/20000 : ℝ)) (X := (5166740602178107/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (531/128 : ℝ) ≤ (35617505276234857/100000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^531 ≤ (35617505276234857/100000000000000000000 : ℝ)^128 := by
      have hnat : (14749 : ℕ)^531*100000000000000000000^128 ≤ 35617505276234857^128*100000^531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 35617505276234857 100000000000000000000 531 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (35617505276234857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005166740602178107/25000000000000000000 : ℝ) ≤ (10000498147598673/10000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (25005166740602178107/25000000000000000000 : ℝ)^128 ≤ (10000498147598673/10000000000000000 : ℝ)^531 := by
      have hnat : (25005166740602178107 : ℕ)^128*10000000000000000^531 ≤ 10000498147598673^531*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005166740602178107 25000000000000000000 10000498147598673 10000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000498147598673/10000000000000000 : ℝ)) (X := (25005166740602178107/25000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045950986480591071/100000000000000000000 : ℝ) ≤ (5000553738318327/5000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (100045950986480591071/100000000000000000000 : ℝ)^128 ≤ (5000553738318327/5000000000000000 : ℝ)^531 := by
      have hnat : (100045950986480591071 : ℕ)^128*5000000000000000^531 ≤ 5000553738318327^531*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045950986480591071 100000000000000000000 5000553738318327 5000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000553738318327/5000000000000000 : ℝ)) (X := (100045950986480591071/100000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035617505276234857/50000000000000000000 : ℝ) ≤ (2000343361134927/2000000000000000 : ℝ) ^ (531/128 : ℝ) := by
    have hpowers : (50035617505276234857/50000000000000000000 : ℝ)^128 ≤ (2000343361134927/2000000000000000 : ℝ)^531 := by
      have hnat : (50035617505276234857 : ℕ)^128*2000000000000000^531 ≤ 2000343361134927^531*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035617505276234857 50000000000000000000 2000343361134927 2000000000000000 128 531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000343361134927/2000000000000000 : ℝ)) (X := (50035617505276234857/50000000000000000000 : ℝ)) (by norm_num) 531 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5166740602178107/50000000000000000000 : ℝ) ≤ ((6338092790137324667/6340000000000000000 : ℝ)+2*(203109679327/126800000000000 : ℝ)*(2189/20000 : ℝ))^(531/128 : ℝ) := by
    rw [show (6338092790137324667/6340000000000000000 : ℝ)+2*(203109679327/126800000000000 : ℝ)*(2189/20000 : ℝ)=(10000498147598673/10000000000000000 : ℝ) by norm_num, show 1+2*(5166740602178107/50000000000000000000 : ℝ)=(25005166740602178107/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35617505276234857/100000000000000000000 : ℝ)+(5166740602178107/50000000000000000000 : ℝ) ≤ ((6338092790137324667/6340000000000000000 : ℝ)+(203109679327/126800000000000 : ℝ)*((14749/100000 : ℝ)+(2189/20000 : ℝ)))^(531/128 : ℝ) := by
    rw [show (6338092790137324667/6340000000000000000 : ℝ)+(203109679327/126800000000000 : ℝ)*((14749/100000 : ℝ)+(2189/20000 : ℝ))=(5000553738318327/5000000000000000 : ℝ) by norm_num, show 1+(35617505276234857/100000000000000000000 : ℝ)+(5166740602178107/50000000000000000000 : ℝ)=(100045950986480591071/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35617505276234857/100000000000000000000 : ℝ) ≤ ((6338092790137324667/6340000000000000000 : ℝ)+2*(203109679327/126800000000000 : ℝ)*(14749/100000 : ℝ))^(531/128 : ℝ) := by
    rw [show (6338092790137324667/6340000000000000000 : ℝ)+2*(203109679327/126800000000000 : ℝ)*(14749/100000 : ℝ)=(2000343361134927/2000000000000000 : ℝ) by norm_num, show 1+2*(35617505276234857/100000000000000000000 : ℝ)=(50035617505276234857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6338092790137324667/6340000000000000000 : ℝ)*(X 1 0+X 2 0)+(203109679327/126800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (2189/20000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (6338092790137324667/6340000000000000000 : ℝ)) (alpha := (203109679327/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6338092790137324667/6340000000000000000 : ℝ)*(X 0 1+X 2 1)+(203109679327/126800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (2189/20000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (6338092790137324667/6340000000000000000 : ℝ)) (alpha := (203109679327/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6338092790137324667/6340000000000000000 : ℝ)*(X 0 2+X 1 2)+(203109679327/126800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (531/128 : ℝ)) (lo := (2189/20000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (6338092790137324667/6340000000000000000 : ℝ)) (alpha := (203109679327/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261323233/1250000000 : ℝ)*X 0 0+(2708028979/5000000000 : ℝ)*X 0 1+(327641197/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167187439/312500000 : ℝ)*X 1 0+(-68099829/312500000 : ℝ)*X 1 1+(5242259147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334374877/625000000 : ℝ)*X 2 0+(5242259169/10000000000 : ℝ)*X 2 1+(-54479863/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170313191/5000000000 : ℝ)*X 0 0+(166629649/400000000 : ℝ)*X 0 1+(1130632383/2500000000 : ℝ)*X 0 2+(2170313191/5000000000 : ℝ)*X 1 0+(166629649/400000000 : ℝ)*X 1 1+(1130632383/2500000000 : ℝ)*X 1 2+(2170313191/5000000000 : ℝ)*X 2 0+(166629649/400000000 : ℝ)*X 2 1+(1130632383/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-209059891/1000000000 : ℝ)*X 0 0+(327680193/625000000 : ℝ)*X 0 1+(1083086157/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305518009/10000000000 : ℝ)*X 1 0+(-401204581/2000000000 : ℝ)*X 1 1+(42308053/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326379501/2500000000 : ℝ)*X 2 0+(5415430787/10000000000 : ℝ)*X 2 1+(-501505727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4340653209/10000000000 : ℝ)*X 0 0+(4521248641/10000000000 : ℝ)*X 0 1+(4167028677/10000000000 : ℝ)*X 0 2+(4340653209/10000000000 : ℝ)*X 1 0+(4521248641/10000000000 : ℝ)*X 1 1+(4167028677/10000000000 : ℝ)*X 1 2+(4340653209/10000000000 : ℝ)*X 2 0+(4521248641/10000000000 : ℝ)*X 2 1+(4167028677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1289_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1690294492469258856722692881/158500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (500263521/25000000000000 : ℝ)*(base19) + (1856792861/100000000000000 : ℝ)*(base23) + (67973549/100000000000000 : ℝ)*(lower2) + (3865149/1562500000000 : ℝ)*(upper3) + (158957913/100000000000000 : ℝ)*(upper5) + (2139171240401119/50000000000000 : ℝ)*(major0) + (2139171240401119/50000000000000 : ℝ)*(major1) + (2139171240401119/50000000000000 : ℝ)*(major2) + (2876910780071219/50000000000000 : ℝ)*(sp0) + (287693004277083/5000000000000 : ℝ)*(sp1) + (5753860229802883/100000000000000 : ℝ)*(sp2) + (350350192373671/12500000000000 : ℝ)*(sp3) + (20263226653/50000000000000 : ℝ)*(sp4) + (20980542073/100000000000000 : ℝ)*(sp7) + (1401411259765721/50000000000000 : ℝ)*(f.failure) + (179808190206117/3125000000000 : ℝ)*(f.sum) + (5979186766057/3170000000000000000000000000 : ℝ)*base66 + (2613376286333752373/317000000000000000000000000000000 : ℝ)*base67 + (333893762652247627/317000000000000000000000000000000 : ℝ)*base70 + (2717203490337752373/317000000000000000000000000000000 : ℝ)*base71 + (2918095831297/3170000000000000000000000000 : ℝ)*base74 + (1131265581169752373/317000000000000000000000000000000 : ℝ)*base75 + (252450325745752373/317000000000000000000000000000000 : ℝ)*base77 + (200592674981247627/317000000000000000000000000000000 : ℝ)*base80 + (5401854709623/3170000000000000000000000000 : ℝ)*base81 + (19493677/2500000000000000000000 : ℝ)*base89 + (19493677/2500000000000000000000 : ℝ)*base91 + (19493677/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104458648041613080611938269/9906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (463791621/25000000000000 : ℝ)*(base19) + (1012069489/50000000000000 : ℝ)*(base23) + (105822461/50000000000000 : ℝ)*(upper3) + (79825769/100000000000000 : ℝ)*(lower4) + (215840337/100000000000000 : ℝ)*(upper5) + (269331306461481/6250000000000 : ℝ)*(major0) + (269331306461481/6250000000000 : ℝ)*(major1) + (269331306461481/6250000000000 : ℝ)*(major2) + (46073469/125000000000 : ℝ)*(sp1) + (317749107/800000000000 : ℝ)*(sp2) + (2897748745809123/50000000000000 : ℝ)*(sp4) + (5795458777676563/100000000000000 : ℝ)*(sp5) + (5795455748840893/100000000000000 : ℝ)*(sp6) + (2823103963658423/100000000000000 : ℝ)*(sp7) + (2823103963658423/100000000000000 : ℝ)*(f.failure) + (2897748745809123/50000000000000 : ℝ)*(f.sum) + (4486571298847/1585000000000000000000000000 : ℝ)*base66 + (7987082647626827/39625000000000000000000000000000 : ℝ)*base67 + (93809971056376827/39625000000000000000000000000000 : ℝ)*base69 + (403898359191248173/39625000000000000000000000000000 : ℝ)*base72 + (268721948399/49531250000000000000000000 : ℝ)*base73 + (21448116282126827/39625000000000000000000000000000 : ℝ)*base75 + (148153855698126827/39625000000000000000000000000000 : ℝ)*base77 + (33737011746876827/39625000000000000000000000000000 : ℝ)*base79 + (1765307487853/1585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15567651/5000000000000000000000 : ℝ)*base89 + (15567651/5000000000000000000000 : ℝ)*base91 + (15567651/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1289_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2189/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1289_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1289_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1289_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1289_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1289_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (531/128 : ℝ) ≤ p) (hpb : p ≤ (4249/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76322037/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16331/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9483/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5503/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2937/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1289_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

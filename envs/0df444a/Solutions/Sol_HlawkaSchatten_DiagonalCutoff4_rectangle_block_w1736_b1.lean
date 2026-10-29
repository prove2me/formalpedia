-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1736_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:03.498197+00:00
-- url     : https://prove2.me/submissions/a2df4524-0127-41af-8dba-0519b11358fb

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
theorem support_rectangle_w1736_s3_0 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-652476037/5000000000 : ℝ)*x 0 + (689583359/1250000000 : ℝ)*x 1 + (63453671/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652476037/5000000000 : ℝ)^5551 ≤ (329308915651/4000000000000 : ℝ)^4527 := by
    have hnat : (652476037 : ℕ)^5551*4000000000000^4527 ≤ 329308915651^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652476037 5000000000 329308915651 4000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689583359/1250000000 : ℝ)^5551 ≤ (48221916292991/100000000000000 : ℝ)^4527 := by
    have hnat : (689583359 : ℕ)^5551*100000000000000^4527 ≤ 48221916292991^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689583359 1250000000 48221916292991 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63453671/125000000 : ℝ)^5551 ≤ (21772680399379/50000000000000 : ℝ)^4527 := by
    have hnat : (63453671 : ℕ)^5551*50000000000000^4527 ≤ 21772680399379^4527*125000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63453671 125000000 21772680399379 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-652476037/5000000000 : ℝ), (689583359/1250000000 : ℝ), (63453671/125000000 : ℝ)] ![(329308915651/4000000000000 : ℝ), (48221916292991/100000000000000 : ℝ), (21772680399379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-652476037/5000000000 : ℝ)|^5551 ≤ (329308915651/4000000000000 : ℝ)^4527
        have hw : |(-652476037/5000000000 : ℝ)|=(652476037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689583359/1250000000 : ℝ)|^5551 ≤ (48221916292991/100000000000000 : ℝ)^4527
        have hw : |(689583359/1250000000 : ℝ)|=(689583359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63453671/125000000 : ℝ)|^5551 ≤ (21772680399379/50000000000000 : ℝ)^4527
        have hw : |(63453671/125000000 : ℝ)|=(63453671/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_1 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346171727/10000000000 : ℝ)*x 0 + (-767959933/5000000000 : ℝ)*x 1 + (507629369/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346171727/10000000000 : ℝ)^5551 ≤ (23200463364091/50000000000000 : ℝ)^4527 := by
    have hnat : (5346171727 : ℕ)^5551*50000000000000^4527 ≤ 23200463364091^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346171727 10000000000 23200463364091 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (767959933/5000000000 : ℝ)^5551 ≤ (10053712352969/100000000000000 : ℝ)^4527 := by
    have hnat : (767959933 : ℕ)^5551*100000000000000^4527 ≤ 10053712352969^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767959933 5000000000 10053712352969 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507629369/1000000000 : ℝ)^5551 ≤ (5443170112993/12500000000000 : ℝ)^4527 := by
    have hnat : (507629369 : ℕ)^5551*12500000000000^4527 ≤ 5443170112993^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507629369 1000000000 5443170112993 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346171727/10000000000 : ℝ), (-767959933/5000000000 : ℝ), (507629369/1000000000 : ℝ)] ![(23200463364091/50000000000000 : ℝ), (10053712352969/100000000000000 : ℝ), (5443170112993/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346171727/10000000000 : ℝ)|^5551 ≤ (23200463364091/50000000000000 : ℝ)^4527
        have hw : |(5346171727/10000000000 : ℝ)|=(5346171727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-767959933/5000000000 : ℝ)|^5551 ≤ (10053712352969/100000000000000 : ℝ)^4527
        have hw : |(-767959933/5000000000 : ℝ)|=(767959933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507629369/1000000000 : ℝ)|^5551 ≤ (5443170112993/12500000000000 : ℝ)^4527
        have hw : |(507629369/1000000000 : ℝ)|=(507629369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_2 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13365429/25000000 : ℝ)*x 0 + (2538146897/5000000000 : ℝ)*x 1 + (-767959949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13365429/25000000 : ℝ)^5551 ≤ (23200462688291/50000000000000 : ℝ)^4527 := by
    have hnat : (13365429 : ℕ)^5551*50000000000000^4527 ≤ 23200462688291^4527*25000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13365429 25000000 23200462688291 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538146897/5000000000 : ℝ)^5551 ≤ (43545361997873/100000000000000 : ℝ)^4527 := by
    have hnat : (2538146897 : ℕ)^5551*100000000000000^4527 ≤ 43545361997873^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538146897 5000000000 43545361997873 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767959949/5000000000 : ℝ)^5551 ≤ (10053712609813/100000000000000 : ℝ)^4527 := by
    have hnat : (767959949 : ℕ)^5551*100000000000000^4527 ≤ 10053712609813^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767959949 5000000000 10053712609813 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13365429/25000000 : ℝ), (2538146897/5000000000 : ℝ), (-767959949/5000000000 : ℝ)] ![(23200462688291/50000000000000 : ℝ), (43545361997873/100000000000000 : ℝ), (10053712609813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13365429/25000000 : ℝ)|^5551 ≤ (23200462688291/50000000000000 : ℝ)^4527
        have hw : |(13365429/25000000 : ℝ)|=(13365429/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538146897/5000000000 : ℝ)|^5551 ≤ (43545361997873/100000000000000 : ℝ)^4527
        have hw : |(2538146897/5000000000 : ℝ)|=(2538146897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-767959949/5000000000 : ℝ)|^5551 ≤ (10053712609813/100000000000000 : ℝ)^4527
        have hw : |(-767959949/5000000000 : ℝ)|=(767959949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_3 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2025648851/5000000000 : ℝ)*x 0 + (680494849/2000000000 : ℝ)*x 1 + (2383464871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2025648851/5000000000 : ℝ)^5551 ≤ (206401388679/625000000000 : ℝ)^4527 := by
    have hnat : (2025648851 : ℕ)^5551*625000000000^4527 ≤ 206401388679^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025648851 5000000000 206401388679 625000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680494849/2000000000 : ℝ)^5551 ≤ (26661685802233/100000000000000 : ℝ)^4527 := by
    have hnat : (680494849 : ℕ)^5551*100000000000000^4527 ≤ 26661685802233^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680494849 2000000000 26661685802233 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383464871/5000000000 : ℝ)^5551 ≤ (40314091995827/100000000000000 : ℝ)^4527 := by
    have hnat : (2383464871 : ℕ)^5551*100000000000000^4527 ≤ 40314091995827^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383464871 5000000000 40314091995827 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2025648851/5000000000 : ℝ), (680494849/2000000000 : ℝ), (2383464871/5000000000 : ℝ)] ![(206401388679/625000000000 : ℝ), (26661685802233/100000000000000 : ℝ), (40314091995827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2025648851/5000000000 : ℝ)|^5551 ≤ (206401388679/625000000000 : ℝ)^4527
        have hw : |(2025648851/5000000000 : ℝ)|=(2025648851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680494849/2000000000 : ℝ)|^5551 ≤ (26661685802233/100000000000000 : ℝ)^4527
        have hw : |(680494849/2000000000 : ℝ)|=(680494849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2383464871/5000000000 : ℝ)|^5551 ≤ (40314091995827/100000000000000 : ℝ)^4527
        have hw : |(2383464871/5000000000 : ℝ)|=(2383464871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_4 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-261066913/2000000000 : ℝ)*x 0 + (2541646113/5000000000 : ℝ)*x 1 + (5509520607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261066913/2000000000 : ℝ)^5551 ≤ (2058920473363/25000000000000 : ℝ)^4527 := by
    have hnat : (261066913 : ℕ)^5551*25000000000000^4527 ≤ 2058920473363^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261066913 2000000000 2058920473363 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541646113/5000000000 : ℝ)^5551 ≤ (8723797366207/20000000000000 : ℝ)^4527 := by
    have hnat : (2541646113 : ℕ)^5551*20000000000000^4527 ≤ 8723797366207^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541646113 5000000000 8723797366207 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5509520607/10000000000 : ℝ)^5551 ≤ (48145331260437/100000000000000 : ℝ)^4527 := by
    have hnat : (5509520607 : ℕ)^5551*100000000000000^4527 ≤ 48145331260437^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509520607 10000000000 48145331260437 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261066913/2000000000 : ℝ), (2541646113/5000000000 : ℝ), (5509520607/10000000000 : ℝ)] ![(2058920473363/25000000000000 : ℝ), (8723797366207/20000000000000 : ℝ), (48145331260437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261066913/2000000000 : ℝ)|^5551 ≤ (2058920473363/25000000000000 : ℝ)^4527
        have hw : |(-261066913/2000000000 : ℝ)|=(261066913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2541646113/5000000000 : ℝ)|^5551 ≤ (8723797366207/20000000000000 : ℝ)^4527
        have hw : |(2541646113/5000000000 : ℝ)|=(2541646113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5509520607/10000000000 : ℝ)|^5551 ≤ (48145331260437/100000000000000 : ℝ)^4527
        have hw : |(5509520607/10000000000 : ℝ)|=(5509520607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_5 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2614545243/5000000000 : ℝ)*x 0 + (-110269293/1000000000 : ℝ)*x 1 + (688690077/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2614545243/5000000000 : ℝ)^5551 ≤ (45157991145373/100000000000000 : ℝ)^4527 := by
    have hnat : (2614545243 : ℕ)^5551*100000000000000^4527 ≤ 45157991145373^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614545243 5000000000 45157991145373 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110269293/1000000000 : ℝ)^5551 ≤ (6696677484409/100000000000000 : ℝ)^4527 := by
    have hnat : (110269293 : ℕ)^5551*100000000000000^4527 ≤ 6696677484409^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110269293 1000000000 6696677484409 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (688690077/1250000000 : ℝ)^5551 ≤ (24072665678437/50000000000000 : ℝ)^4527 := by
    have hnat : (688690077 : ℕ)^5551*50000000000000^4527 ≤ 24072665678437^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688690077 1250000000 24072665678437 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2614545243/5000000000 : ℝ), (-110269293/1000000000 : ℝ), (688690077/1250000000 : ℝ)] ![(45157991145373/100000000000000 : ℝ), (6696677484409/100000000000000 : ℝ), (24072665678437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2614545243/5000000000 : ℝ)|^5551 ≤ (45157991145373/100000000000000 : ℝ)^4527
        have hw : |(2614545243/5000000000 : ℝ)|=(2614545243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110269293/1000000000 : ℝ)|^5551 ≤ (6696677484409/100000000000000 : ℝ)^4527
        have hw : |(-110269293/1000000000 : ℝ)|=(110269293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(688690077/1250000000 : ℝ)|^5551 ≤ (24072665678437/50000000000000 : ℝ)^4527
        have hw : |(688690077/1250000000 : ℝ)|=(688690077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_6 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5229090483/10000000000 : ℝ)*x 0 + (2754760309/5000000000 : ℝ)*x 1 + (-1102692931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5229090483/10000000000 : ℝ)^5551 ≤ (9031598222721/20000000000000 : ℝ)^4527 := by
    have hnat : (5229090483 : ℕ)^5551*20000000000000^4527 ≤ 9031598222721^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229090483 10000000000 9031598222721 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754760309/5000000000 : ℝ)^5551 ≤ (9629066275661/20000000000000 : ℝ)^4527 := by
    have hnat : (2754760309 : ℕ)^5551*20000000000000^4527 ≤ 9629066275661^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754760309 5000000000 9629066275661 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102692931/10000000000 : ℝ)^5551 ≤ (1339335498371/20000000000000 : ℝ)^4527 := by
    have hnat : (1102692931 : ℕ)^5551*20000000000000^4527 ≤ 1339335498371^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102692931 10000000000 1339335498371 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5229090483/10000000000 : ℝ), (2754760309/5000000000 : ℝ), (-1102692931/10000000000 : ℝ)] ![(9031598222721/20000000000000 : ℝ), (9629066275661/20000000000000 : ℝ), (1339335498371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5229090483/10000000000 : ℝ)|^5551 ≤ (9031598222721/20000000000000 : ℝ)^4527
        have hw : |(5229090483/10000000000 : ℝ)|=(5229090483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754760309/5000000000 : ℝ)|^5551 ≤ (9629066275661/20000000000000 : ℝ)^4527
        have hw : |(2754760309/5000000000 : ℝ)|=(2754760309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102692931/10000000000 : ℝ)|^5551 ≤ (1339335498371/20000000000000 : ℝ)^4527
        have hw : |(-1102692931/10000000000 : ℝ)|=(1102692931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_s3_7 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4052482583/10000000000 : ℝ)*x 0 + (949049089/2000000000 : ℝ)*x 1 + (1712308121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4052482583/10000000000 : ℝ)^5551 ≤ (33036065912483/100000000000000 : ℝ)^4527 := by
    have hnat : (4052482583 : ℕ)^5551*100000000000000^4527 ≤ 33036065912483^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052482583 10000000000 33036065912483 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949049089/2000000000 : ℝ)^5551 ≤ (10022335401151/25000000000000 : ℝ)^4527 := by
    have hnat : (949049089 : ℕ)^5551*25000000000000^4527 ≤ 10022335401151^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949049089 2000000000 10022335401151 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1712308121/5000000000 : ℝ)^5551 ≤ (26874592474151/100000000000000 : ℝ)^4527 := by
    have hnat : (1712308121 : ℕ)^5551*100000000000000^4527 ≤ 26874592474151^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712308121 5000000000 26874592474151 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4052482583/10000000000 : ℝ), (949049089/2000000000 : ℝ), (1712308121/5000000000 : ℝ)] ![(33036065912483/100000000000000 : ℝ), (10022335401151/25000000000000 : ℝ), (26874592474151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4052482583/10000000000 : ℝ)|^5551 ≤ (33036065912483/100000000000000 : ℝ)^4527
        have hw : |(4052482583/10000000000 : ℝ)|=(4052482583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(949049089/2000000000 : ℝ)|^5551 ≤ (10022335401151/25000000000000 : ℝ)^4527
        have hw : |(949049089/2000000000 : ℝ)|=(949049089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1712308121/5000000000 : ℝ)|^5551 ≤ (26874592474151/100000000000000 : ℝ)^4527
        have hw : |(1712308121/5000000000 : ℝ)|=(1712308121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1736_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1767/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18251/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (276/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9127/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (276/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (276/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9127/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (276/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (276/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9127/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (276/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (276/3125 : ℝ) ^ (5535/1024 : ℝ) ≤ (25122973914481/12500000000000000000 : ℝ) := by
    have hpowers : (276/3125 : ℝ)^5535 ≤ (25122973914481/12500000000000000000 : ℝ)^1024 := by
      have hnat : (276 : ℕ)^5535*12500000000000000000^1024 ≤ 25122973914481^1024*3125^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        276 3125 25122973914481 12500000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (276/3125 : ℝ)) (X := (25122973914481/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9127/50000 : ℝ) ^ (5535/1024 : ℝ) ≤ (10172747555213937/100000000000000000000 : ℝ) := by
    have hpowers : (9127/50000 : ℝ)^5535 ≤ (10172747555213937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9127 : ℕ)^5535*100000000000000000000^1024 ≤ 10172747555213937^1024*50000^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9127 50000 10172747555213937 100000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9127/50000 : ℝ)) (X := (10172747555213937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250025122973914481/6250000000000000000 : ℝ) ≤ (2000001487313931/2000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (6250025122973914481/6250000000000000000 : ℝ)^1024 ≤ (2000001487313931/2000000000000000 : ℝ)^5535 := by
      have hnat : (6250025122973914481 : ℕ)^1024*2000000000000000^5535 ≤ 2000001487313931^5535*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250025122973914481 6250000000000000000 2000001487313931 2000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000001487313931/2000000000000000 : ℝ)) (X := (6250025122973914481/6250000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002074746269305957/20000000000000000000 : ℝ) ≤ (1000019191060301/1000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (20002074746269305957/20000000000000000000 : ℝ)^1024 ≤ (1000019191060301/1000000000000000 : ℝ)^5535 := by
      have hnat : (20002074746269305957 : ℕ)^1024*1000000000000000^5535 ≤ 1000019191060301^5535*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002074746269305957 20000000000000000000 1000019191060301 1000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000019191060301/1000000000000000 : ℝ)) (X := (20002074746269305957/20000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010172747555213937/50000000000000000000 : ℝ) ≤ (2000075276927273/2000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (50010172747555213937/50000000000000000000 : ℝ)^1024 ≤ (2000075276927273/2000000000000000 : ℝ)^5535 := by
      have hnat : (50010172747555213937 : ℕ)^1024*2000000000000000^5535 ≤ 2000075276927273^5535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010172747555213937 50000000000000000000 2000075276927273 2000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000075276927273/2000000000000000 : ℝ)) (X := (50010172747555213937/50000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25122973914481/12500000000000000000 : ℝ) ≤ ((9421681151803410669/9422000000000000000 : ℝ)+2*(36894806671/188440000000000 : ℝ)*(276/3125 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (9421681151803410669/9422000000000000000 : ℝ)+2*(36894806671/188440000000000 : ℝ)*(276/3125 : ℝ)=(2000001487313931/2000000000000000 : ℝ) by norm_num, show 1+2*(25122973914481/12500000000000000000 : ℝ)=(6250025122973914481/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10172747555213937/100000000000000000000 : ℝ)+(25122973914481/12500000000000000000 : ℝ) ≤ ((9421681151803410669/9422000000000000000 : ℝ)+(36894806671/188440000000000 : ℝ)*((9127/50000 : ℝ)+(276/3125 : ℝ)))^(5535/1024 : ℝ) := by
    rw [show (9421681151803410669/9422000000000000000 : ℝ)+(36894806671/188440000000000 : ℝ)*((9127/50000 : ℝ)+(276/3125 : ℝ))=(1000019191060301/1000000000000000 : ℝ) by norm_num, show 1+(10172747555213937/100000000000000000000 : ℝ)+(25122973914481/12500000000000000000 : ℝ)=(20002074746269305957/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10172747555213937/100000000000000000000 : ℝ) ≤ ((9421681151803410669/9422000000000000000 : ℝ)+2*(36894806671/188440000000000 : ℝ)*(9127/50000 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (9421681151803410669/9422000000000000000 : ℝ)+2*(36894806671/188440000000000 : ℝ)*(9127/50000 : ℝ)=(2000075276927273/2000000000000000 : ℝ) by norm_num, show 1+2*(10172747555213937/100000000000000000000 : ℝ)=(50010172747555213937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9421681151803410669/9422000000000000000 : ℝ)*(X 1 0+X 2 0)+(36894806671/188440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (276/3125 : ℝ)) (hi := (9127/50000 : ℝ)) (c := (9421681151803410669/9422000000000000000 : ℝ)) (alpha := (36894806671/188440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9421681151803410669/9422000000000000000 : ℝ)*(X 0 1+X 2 1)+(36894806671/188440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (276/3125 : ℝ)) (hi := (9127/50000 : ℝ)) (c := (9421681151803410669/9422000000000000000 : ℝ)) (alpha := (36894806671/188440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9421681151803410669/9422000000000000000 : ℝ)*(X 0 2+X 1 2)+(36894806671/188440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (276/3125 : ℝ)) (hi := (9127/50000 : ℝ)) (c := (9421681151803410669/9422000000000000000 : ℝ)) (alpha := (36894806671/188440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-652476037/5000000000 : ℝ)*X 0 0+(689583359/1250000000 : ℝ)*X 0 1+(63453671/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346171727/10000000000 : ℝ)*X 1 0+(-767959933/5000000000 : ℝ)*X 1 1+(507629369/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((13365429/25000000 : ℝ)*X 2 0+(2538146897/5000000000 : ℝ)*X 2 1+(-767959949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2025648851/5000000000 : ℝ)*X 0 0+(680494849/2000000000 : ℝ)*X 0 1+(2383464871/5000000000 : ℝ)*X 0 2+(2025648851/5000000000 : ℝ)*X 1 0+(680494849/2000000000 : ℝ)*X 1 1+(2383464871/5000000000 : ℝ)*X 1 2+(2025648851/5000000000 : ℝ)*X 2 0+(680494849/2000000000 : ℝ)*X 2 1+(2383464871/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-261066913/2000000000 : ℝ)*X 0 0+(2541646113/5000000000 : ℝ)*X 0 1+(5509520607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2614545243/5000000000 : ℝ)*X 1 0+(-110269293/1000000000 : ℝ)*X 1 1+(688690077/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5229090483/10000000000 : ℝ)*X 2 0+(2754760309/5000000000 : ℝ)*X 2 1+(-1102692931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4052482583/10000000000 : ℝ)*X 0 0+(949049089/2000000000 : ℝ)*X 0 1+(1712308121/5000000000 : ℝ)*X 0 2+(4052482583/10000000000 : ℝ)*X 1 0+(949049089/2000000000 : ℝ)*X 1 1+(1712308121/5000000000 : ℝ)*X 1 2+(4052482583/10000000000 : ℝ)*X 2 0+(949049089/2000000000 : ℝ)*X 2 1+(1712308121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84182499718368082155147/9422000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316779291/25000000000000 : ℝ)*(base19) + (553931327/50000000000000 : ℝ)*(base23) + (56300799/100000000000000 : ℝ)*(lower2) + (120304311/50000000000000 : ℝ)*(upper3) + (35212073/25000000000000 : ℝ)*(upper5) + (300371922577809/20000000000000 : ℝ)*(major0) + (300371922577809/20000000000000 : ℝ)*(major1) + (300371922577809/20000000000000 : ℝ)*(major2) + (14192568102793/625000000000 : ℝ)*(sp0) + (1135409264451467/50000000000000 : ℝ)*(sp1) + (454163737631489/20000000000000 : ℝ)*(sp2) + (183223951571477/25000000000000 : ℝ)*(sp3) + (8899573219/100000000000000 : ℝ)*(sp4) + (3325649607/100000000000000 : ℝ)*(sp7) + (146579826387103/20000000000000 : ℝ)*(f.failure) + (1135409898010049/50000000000000 : ℝ)*(f.sum) + (16289887293329/9422000000000000000000000000 : ℝ)*base66 + (1275032024875565779/188440000000000000000000000000000 : ℝ)*base68 + (483781987502525779/188440000000000000000000000000000 : ℝ)*base70 + (206042138566594221/188440000000000000000000000000000 : ℝ)*base71 + (62223157592287/9422000000000000000000000000 : ℝ)*base74 + (1117742413205594221/188440000000000000000000000000000 : ℝ)*base75 + (72359979358514221/188440000000000000000000000000000 : ℝ)*base77 + (348687644613005779/188440000000000000000000000000000 : ℝ)*base80 + (10858926422649/1884400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (998811/200000000000000000000 : ℝ)*base89 + (998811/200000000000000000000 : ℝ)*base91 + (998811/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (475002271202173367748497079/67300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (947674551/100000000000000 : ℝ)*(base19) + (203385077/20000000000000 : ℝ)*(base23) + (27221971/10000000000000 : ℝ)*(lower1) + (155443133/100000000000000 : ℝ)*(upper3) + (622127/2000000000000 : ℝ)*(lower4) + (147159417/100000000000000 : ℝ)*(upper5) + (1551683090102307/100000000000000 : ℝ)*(major0) + (1551683090102307/100000000000000 : ℝ)*(major1) + (1551683090102307/100000000000000 : ℝ)*(major2) + (248092237/50000000000000 : ℝ)*(sp2) + (2346153233433873/100000000000000 : ℝ)*(sp4) + (1173076142879661/50000000000000 : ℝ)*(sp5) + (1173075860162007/50000000000000 : ℝ)*(sp6) + (757212711504623/100000000000000 : ℝ)*(sp7) + (757212711504623/100000000000000 : ℝ)*(f.failure) + (2346153233433873/100000000000000 : ℝ)*(f.sum) + (1392442287189/9422000000000000000000000000 : ℝ)*base65 + (5677570602452563383/942200000000000000000000000000000 : ℝ)*base67 + (6560935729975763383/942200000000000000000000000000000 : ℝ)*base69 + (1961036162562963383/942200000000000000000000000000000 : ℝ)*base71 + (29908711231947/9422000000000000000000000000 : ℝ)*base73 + (22476708680265563383/942200000000000000000000000000000 : ℝ)*base75 + (3291906222088963383/942200000000000000000000000000000 : ℝ)*base77 + (4817432726890563383/942200000000000000000000000000000 : ℝ)*base79 + (40413494020237/9422000000000000000000000000 : ℝ)*base81 + (9812949/1000000000000000000000 : ℝ)*base90 + (9812949/1000000000000000000000 : ℝ)*base92 + (9812949/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1736_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1767/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18251/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1736_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1736_box_0 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223400303/2500000000 : ℝ)*x 0 + (680130109/1250000000 : ℝ)*x 1 + (5441041941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223400303/2500000000 : ℝ)^5551 ≤ (2587403635543/50000000000000 : ℝ)^4527 := by
    have hnat : (223400303 : ℕ)^5551*50000000000000^4527 ≤ 2587403635543^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223400303 2500000000 2587403635543 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680130109/1250000000 : ℝ)^5551 ≤ (11853147662511/25000000000000 : ℝ)^4527 := by
    have hnat : (680130109 : ℕ)^5551*25000000000000^4527 ≤ 11853147662511^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680130109 1250000000 11853147662511 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441041941/10000000000 : ℝ)^5551 ≤ (23706301036127/50000000000000 : ℝ)^4527 := by
    have hnat : (5441041941 : ℕ)^5551*50000000000000^4527 ≤ 23706301036127^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441041941 10000000000 23706301036127 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223400303/2500000000 : ℝ), (680130109/1250000000 : ℝ), (5441041941/10000000000 : ℝ)] ![(2587403635543/50000000000000 : ℝ), (11853147662511/25000000000000 : ℝ), (23706301036127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223400303/2500000000 : ℝ)|^5551 ≤ (2587403635543/50000000000000 : ℝ)^4527
        have hw : |(-223400303/2500000000 : ℝ)|=(223400303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(680130109/1250000000 : ℝ)|^5551 ≤ (11853147662511/25000000000000 : ℝ)^4527
        have hw : |(680130109/1250000000 : ℝ)|=(680130109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441041941/10000000000 : ℝ)|^5551 ≤ (23706301036127/50000000000000 : ℝ)^4527
        have hw : |(5441041941/10000000000 : ℝ)|=(5441041941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_1 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (103906849/200000000 : ℝ)*x 0 + (-155872177/1250000000 : ℝ)*x 1 + (170032553/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103906849/200000000 : ℝ)^5551 ≤ (8960176552813/20000000000000 : ℝ)^4527 := by
    have hnat : (103906849 : ℕ)^5551*20000000000000^4527 ≤ 8960176552813^4527*200000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103906849 200000000 8960176552813 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (155872177/1250000000 : ℝ)^5551 ≤ (3893258880903/50000000000000 : ℝ)^4527 := by
    have hnat : (155872177 : ℕ)^5551*50000000000000^4527 ≤ 3893258880903^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155872177 1250000000 3893258880903 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170032553/312500000 : ℝ)^5551 ≤ (47412599454441/100000000000000 : ℝ)^4527 := by
    have hnat : (170032553 : ℕ)^5551*100000000000000^4527 ≤ 47412599454441^4527*312500000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170032553 312500000 47412599454441 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103906849/200000000 : ℝ), (-155872177/1250000000 : ℝ), (170032553/312500000 : ℝ)] ![(8960176552813/20000000000000 : ℝ), (3893258880903/50000000000000 : ℝ), (47412599454441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103906849/200000000 : ℝ)|^5551 ≤ (8960176552813/20000000000000 : ℝ)^4527
        have hw : |(103906849/200000000 : ℝ)|=(103906849/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-155872177/1250000000 : ℝ)|^5551 ≤ (3893258880903/50000000000000 : ℝ)^4527
        have hw : |(-155872177/1250000000 : ℝ)|=(155872177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170032553/312500000 : ℝ)|^5551 ≤ (47412599454441/100000000000000 : ℝ)^4527
        have hw : |(170032553/312500000 : ℝ)|=(170032553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_2 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298835527/2500000000 : ℝ)*x 0 + (1088208463/2000000000 : ℝ)*x 1 + (-49879081/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298835527/2500000000 : ℝ)^5551 ≤ (44800879147809/100000000000000 : ℝ)^4527 := by
    have hnat : (1298835527 : ℕ)^5551*100000000000000^4527 ≤ 44800879147809^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298835527 2500000000 44800879147809 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1088208463/2000000000 : ℝ)^5551 ≤ (1896504242737/4000000000000 : ℝ)^4527 := by
    have hnat : (1088208463 : ℕ)^5551*4000000000000^4527 ≤ 1896504242737^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088208463 2000000000 1896504242737 4000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49879081/400000000 : ℝ)^5551 ≤ (778651476801/10000000000000 : ℝ)^4527 := by
    have hnat : (49879081 : ℕ)^5551*10000000000000^4527 ≤ 778651476801^4527*400000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49879081 400000000 778651476801 10000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298835527/2500000000 : ℝ), (1088208463/2000000000 : ℝ), (-49879081/400000000 : ℝ)] ![(44800879147809/100000000000000 : ℝ), (1896504242737/4000000000000 : ℝ), (778651476801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298835527/2500000000 : ℝ)|^5551 ≤ (44800879147809/100000000000000 : ℝ)^4527
        have hw : |(1298835527/2500000000 : ℝ)|=(1298835527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1088208463/2000000000 : ℝ)|^5551 ≤ (1896504242737/4000000000000 : ℝ)^4527
        have hw : |(1088208463/2000000000 : ℝ)|=(1088208463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49879081/400000000 : ℝ)|^5551 ≤ (778651476801/10000000000000 : ℝ)^4527
        have hw : |(-49879081/400000000 : ℝ)|=(49879081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_3 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (458052187/1000000000 : ℝ)*x 0 + (956969001/2500000000 : ℝ)*x 1 + (956968517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458052187/1000000000 : ℝ)^5551 ≤ (599838732709/1562500000000 : ℝ)^4527 := by
    have hnat : (458052187 : ℕ)^5551*1562500000000^4527 ≤ 599838732709^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458052187 1000000000 599838732709 1562500000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956969001/2500000000 : ℝ)^5551 ≤ (7701292524731/25000000000000 : ℝ)^4527 := by
    have hnat : (956969001 : ℕ)^5551*25000000000000^4527 ≤ 7701292524731^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956969001 2500000000 7701292524731 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956968517/2500000000 : ℝ)^5551 ≤ (6161030198919/20000000000000 : ℝ)^4527 := by
    have hnat : (956968517 : ℕ)^5551*20000000000000^4527 ≤ 6161030198919^4527*2500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956968517 2500000000 6161030198919 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(458052187/1000000000 : ℝ), (956969001/2500000000 : ℝ), (956968517/2500000000 : ℝ)] ![(599838732709/1562500000000 : ℝ), (7701292524731/25000000000000 : ℝ), (6161030198919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(458052187/1000000000 : ℝ)|^5551 ≤ (599838732709/1562500000000 : ℝ)^4527
        have hw : |(458052187/1000000000 : ℝ)|=(458052187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(956969001/2500000000 : ℝ)|^5551 ≤ (7701292524731/25000000000000 : ℝ)^4527
        have hw : |(956969001/2500000000 : ℝ)|=(956969001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(956968517/2500000000 : ℝ)|^5551 ≤ (6161030198919/20000000000000 : ℝ)^4527
        have hw : |(956968517/2500000000 : ℝ)|=(956968517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_4 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219629079/1250000000 : ℝ)*x 0 + (205051609/400000000 : ℝ)*x 1 + (5126290031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219629079/1250000000 : ℝ)^5551 ≤ (11856329460147/100000000000000 : ℝ)^4527 := by
    have hnat : (219629079 : ℕ)^5551*100000000000000^4527 ≤ 11856329460147^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219629079 1250000000 11856329460147 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205051609/400000000 : ℝ)^5551 ≤ (22035918143831/50000000000000 : ℝ)^4527 := by
    have hnat : (205051609 : ℕ)^5551*50000000000000^4527 ≤ 22035918143831^4527*400000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205051609 400000000 22035918143831 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5126290031/10000000000 : ℝ)^5551 ≤ (22035917121267/50000000000000 : ℝ)^4527 := by
    have hnat : (5126290031 : ℕ)^5551*50000000000000^4527 ≤ 22035917121267^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5126290031 10000000000 22035917121267 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219629079/1250000000 : ℝ), (205051609/400000000 : ℝ), (5126290031/10000000000 : ℝ)] ![(11856329460147/100000000000000 : ℝ), (22035918143831/50000000000000 : ℝ), (22035917121267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219629079/1250000000 : ℝ)|^5551 ≤ (11856329460147/100000000000000 : ℝ)^4527
        have hw : |(-219629079/1250000000 : ℝ)|=(219629079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205051609/400000000 : ℝ)|^5551 ≤ (22035918143831/50000000000000 : ℝ)^4527
        have hw : |(205051609/400000000 : ℝ)|=(205051609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5126290031/10000000000 : ℝ)|^5551 ≤ (22035917121267/50000000000000 : ℝ)^4527
        have hw : |(5126290031/10000000000 : ℝ)|=(5126290031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_5 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081466147/2000000000 : ℝ)*x 0 + (-1387462911/10000000000 : ℝ)*x 1 + (256314523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081466147/2000000000 : ℝ)^5551 ≤ (11763163092047/25000000000000 : ℝ)^4527 := by
    have hnat : (1081466147 : ℕ)^5551*25000000000000^4527 ≤ 11763163092047^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081466147 2000000000 11763163092047 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387462911/10000000000 : ℝ)^5551 ≤ (8875508852377/100000000000000 : ℝ)^4527 := by
    have hnat : (1387462911 : ℕ)^5551*100000000000000^4527 ≤ 8875508852377^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387462911 10000000000 8875508852377 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256314523/500000000 : ℝ)^5551 ≤ (44071838765007/100000000000000 : ℝ)^4527 := by
    have hnat : (256314523 : ℕ)^5551*100000000000000^4527 ≤ 44071838765007^4527*500000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256314523 500000000 44071838765007 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081466147/2000000000 : ℝ), (-1387462911/10000000000 : ℝ), (256314523/500000000 : ℝ)] ![(11763163092047/25000000000000 : ℝ), (8875508852377/100000000000000 : ℝ), (44071838765007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081466147/2000000000 : ℝ)|^5551 ≤ (11763163092047/25000000000000 : ℝ)^4527
        have hw : |(1081466147/2000000000 : ℝ)|=(1081466147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387462911/10000000000 : ℝ)|^5551 ≤ (8875508852377/100000000000000 : ℝ)^4527
        have hw : |(-1387462911/10000000000 : ℝ)|=(1387462911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256314523/500000000 : ℝ)|^5551 ≤ (44071838765007/100000000000000 : ℝ)^4527
        have hw : |(256314523/500000000 : ℝ)|=(256314523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_6 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540733047/1000000000 : ℝ)*x 0 + (1025258127/2000000000 : ℝ)*x 1 + (-1387463037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540733047/1000000000 : ℝ)^5551 ≤ (23526324770327/50000000000000 : ℝ)^4527 := by
    have hnat : (540733047 : ℕ)^5551*50000000000000^4527 ≤ 23526324770327^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540733047 1000000000 23526324770327 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025258127/2000000000 : ℝ)^5551 ≤ (44071840609839/100000000000000 : ℝ)^4527 := by
    have hnat : (1025258127 : ℕ)^5551*100000000000000^4527 ≤ 44071840609839^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025258127 2000000000 44071840609839 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1387463037/10000000000 : ℝ)^5551 ≤ (8875509840709/100000000000000 : ℝ)^4527 := by
    have hnat : (1387463037 : ℕ)^5551*100000000000000^4527 ≤ 8875509840709^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387463037 10000000000 8875509840709 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540733047/1000000000 : ℝ), (1025258127/2000000000 : ℝ), (-1387463037/10000000000 : ℝ)] ![(23526324770327/50000000000000 : ℝ), (44071840609839/100000000000000 : ℝ), (8875509840709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540733047/1000000000 : ℝ)|^5551 ≤ (23526324770327/50000000000000 : ℝ)^4527
        have hw : |(540733047/1000000000 : ℝ)|=(540733047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025258127/2000000000 : ℝ)|^5551 ≤ (44071840609839/100000000000000 : ℝ)^4527
        have hw : |(1025258127/2000000000 : ℝ)|=(1025258127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1387463037/10000000000 : ℝ)|^5551 ≤ (8875509840709/100000000000000 : ℝ)^4527
        have hw : |(-1387463037/10000000000 : ℝ)|=(1387463037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_7 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1743993409/5000000000 : ℝ)*x 0 + (4371929817/10000000000 : ℝ)*x 1 + (874385703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1743993409/5000000000 : ℝ)^5551 ≤ (6871412474977/25000000000000 : ℝ)^4527 := by
    have hnat : (1743993409 : ℕ)^5551*25000000000000^4527 ≤ 6871412474977^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1743993409 5000000000 6871412474977 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4371929817/10000000000 : ℝ)^5551 ≤ (9064295416467/25000000000000 : ℝ)^4527 := by
    have hnat : (4371929817 : ℕ)^5551*25000000000000^4527 ≤ 9064295416467^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371929817 10000000000 9064295416467 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874385703/2000000000 : ℝ)^5551 ≤ (141629564163/390625000000 : ℝ)^4527 := by
    have hnat : (874385703 : ℕ)^5551*390625000000^4527 ≤ 141629564163^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874385703 2000000000 141629564163 390625000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1743993409/5000000000 : ℝ), (4371929817/10000000000 : ℝ), (874385703/2000000000 : ℝ)] ![(6871412474977/25000000000000 : ℝ), (9064295416467/25000000000000 : ℝ), (141629564163/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1743993409/5000000000 : ℝ)|^5551 ≤ (6871412474977/25000000000000 : ℝ)^4527
        have hw : |(1743993409/5000000000 : ℝ)|=(1743993409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4371929817/10000000000 : ℝ)|^5551 ≤ (9064295416467/25000000000000 : ℝ)^4527
        have hw : |(4371929817/10000000000 : ℝ)|=(4371929817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874385703/2000000000 : ℝ)|^5551 ≤ (141629564163/390625000000 : ℝ)^4527
        have hw : |(874385703/2000000000 : ℝ)|=(874385703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_8 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1569761121/10000000000 : ℝ)*x 0 + (4888209103/10000000000 : ℝ)*x 1 + (2752581271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1569761121/10000000000 : ℝ)^5551 ≤ (2581501875451/25000000000000 : ℝ)^4527 := by
    have hnat : (1569761121 : ℕ)^5551*25000000000000^4527 ≤ 2581501875451^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569761121 10000000000 2581501875451 25000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4888209103/10000000000 : ℝ)^5551 ≤ (20787677335617/50000000000000 : ℝ)^4527 := by
    have hnat : (4888209103 : ℕ)^5551*50000000000000^4527 ≤ 20787677335617^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888209103 10000000000 20787677335617 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752581271/5000000000 : ℝ)^5551 ≤ (24049318906423/50000000000000 : ℝ)^4527 := by
    have hnat : (2752581271 : ℕ)^5551*50000000000000^4527 ≤ 24049318906423^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752581271 5000000000 24049318906423 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1569761121/10000000000 : ℝ), (4888209103/10000000000 : ℝ), (2752581271/5000000000 : ℝ)] ![(2581501875451/25000000000000 : ℝ), (20787677335617/50000000000000 : ℝ), (24049318906423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1569761121/10000000000 : ℝ)|^5551 ≤ (2581501875451/25000000000000 : ℝ)^4527
        have hw : |(-1569761121/10000000000 : ℝ)|=(1569761121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4888209103/10000000000 : ℝ)|^5551 ≤ (20787677335617/50000000000000 : ℝ)^4527
        have hw : |(4888209103/10000000000 : ℝ)|=(4888209103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752581271/5000000000 : ℝ)|^5551 ≤ (24049318906423/50000000000000 : ℝ)^4527
        have hw : |(2752581271/5000000000 : ℝ)|=(2752581271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_9 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152208351/10000000000 : ℝ)*x 0 + (-1216806009/10000000000 : ℝ)*x 1 + (2752581513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152208351/10000000000 : ℝ)^5551 ≤ (44345218485269/100000000000000 : ℝ)^4527 := by
    have hnat : (5152208351 : ℕ)^5551*100000000000000^4527 ≤ 44345218485269^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152208351 10000000000 44345218485269 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216806009/10000000000 : ℝ)^5551 ≤ (7556138496027/100000000000000 : ℝ)^4527 := by
    have hnat : (1216806009 : ℕ)^5551*100000000000000^4527 ≤ 7556138496027^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216806009 10000000000 7556138496027 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752581513/5000000000 : ℝ)^5551 ≤ (9619728599617/20000000000000 : ℝ)^4527 := by
    have hnat : (2752581513 : ℕ)^5551*20000000000000^4527 ≤ 9619728599617^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752581513 5000000000 9619728599617 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152208351/10000000000 : ℝ), (-1216806009/10000000000 : ℝ), (2752581513/5000000000 : ℝ)] ![(44345218485269/100000000000000 : ℝ), (7556138496027/100000000000000 : ℝ), (9619728599617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152208351/10000000000 : ℝ)|^5551 ≤ (44345218485269/100000000000000 : ℝ)^4527
        have hw : |(5152208351/10000000000 : ℝ)|=(5152208351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1216806009/10000000000 : ℝ)|^5551 ≤ (7556138496027/100000000000000 : ℝ)^4527
        have hw : |(-1216806009/10000000000 : ℝ)|=(1216806009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752581513/5000000000 : ℝ)|^5551 ≤ (9619728599617/20000000000000 : ℝ)^4527
        have hw : |(2752581513/5000000000 : ℝ)|=(2752581513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_10 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1030441629/2000000000 : ℝ)*x 0 + (688145377/1250000000 : ℝ)*x 1 + (-121680631/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030441629/2000000000 : ℝ)^5551 ≤ (1108630407779/2500000000000 : ℝ)^4527 := by
    have hnat : (1030441629 : ℕ)^5551*2500000000000^4527 ≤ 1108630407779^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030441629 2000000000 1108630407779 2500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688145377/1250000000 : ℝ)^5551 ≤ (6012330361369/12500000000000 : ℝ)^4527 := by
    have hnat : (688145377 : ℕ)^5551*12500000000000^4527 ≤ 6012330361369^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688145377 1250000000 6012330361369 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (121680631/1000000000 : ℝ)^5551 ≤ (7556140787981/100000000000000 : ℝ)^4527 := by
    have hnat : (121680631 : ℕ)^5551*100000000000000^4527 ≤ 7556140787981^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121680631 1000000000 7556140787981 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030441629/2000000000 : ℝ), (688145377/1250000000 : ℝ), (-121680631/1000000000 : ℝ)] ![(1108630407779/2500000000000 : ℝ), (6012330361369/12500000000000 : ℝ), (7556140787981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030441629/2000000000 : ℝ)|^5551 ≤ (1108630407779/2500000000000 : ℝ)^4527
        have hw : |(1030441629/2000000000 : ℝ)|=(1030441629/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688145377/1250000000 : ℝ)|^5551 ≤ (6012330361369/12500000000000 : ℝ)^4527
        have hw : |(688145377/1250000000 : ℝ)|=(688145377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-121680631/1000000000 : ℝ)|^5551 ≤ (7556140787981/100000000000000 : ℝ)^4527
        have hw : |(-121680631/1000000000 : ℝ)|=(121680631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_11 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4792365721/10000000000 : ℝ)*x 0 + (1858312423/5000000000 : ℝ)*x 1 + (743325073/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4792365721/10000000000 : ℝ)^5551 ≤ (20289011063977/50000000000000 : ℝ)^4527 := by
    have hnat : (4792365721 : ℕ)^5551*50000000000000^4527 ≤ 20289011063977^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792365721 10000000000 20289011063977 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1858312423/5000000000 : ℝ)^5551 ≤ (5942197276741/20000000000000 : ℝ)^4527 := by
    have hnat : (1858312423 : ℕ)^5551*20000000000000^4527 ≤ 5942197276741^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858312423 5000000000 5942197276741 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (743325073/2000000000 : ℝ)^5551 ≤ (3713873933889/12500000000000 : ℝ)^4527 := by
    have hnat : (743325073 : ℕ)^5551*12500000000000^4527 ≤ 3713873933889^4527*2000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743325073 2000000000 3713873933889 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4792365721/10000000000 : ℝ), (1858312423/5000000000 : ℝ), (743325073/2000000000 : ℝ)] ![(20289011063977/50000000000000 : ℝ), (5942197276741/20000000000000 : ℝ), (3713873933889/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4792365721/10000000000 : ℝ)|^5551 ≤ (20289011063977/50000000000000 : ℝ)^4527
        have hw : |(4792365721/10000000000 : ℝ)|=(4792365721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1858312423/5000000000 : ℝ)|^5551 ≤ (5942197276741/20000000000000 : ℝ)^4527
        have hw : |(1858312423/5000000000 : ℝ)|=(1858312423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(743325073/2000000000 : ℝ)|^5551 ≤ (3713873933889/12500000000000 : ℝ)^4527
        have hw : |(743325073/2000000000 : ℝ)|=(743325073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_12 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106813117/1000000000 : ℝ)*x 0 + (5664381399/10000000000 : ℝ)*x 1 + (2547862507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106813117/1000000000 : ℝ)^5551 ≤ (3220112634531/50000000000000 : ℝ)^4527 := by
    have hnat : (106813117 : ℕ)^5551*50000000000000^4527 ≤ 3220112634531^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106813117 1000000000 3220112634531 50000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5664381399/10000000000 : ℝ)^5551 ≤ (49809936059959/100000000000000 : ℝ)^4527 := by
    have hnat : (5664381399 : ℕ)^5551*100000000000000^4527 ≤ 49809936059959^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664381399 10000000000 49809936059959 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547862507/5000000000 : ℝ)^5551 ≤ (43749838660781/100000000000000 : ℝ)^4527 := by
    have hnat : (2547862507 : ℕ)^5551*100000000000000^4527 ≤ 43749838660781^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547862507 5000000000 43749838660781 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106813117/1000000000 : ℝ), (5664381399/10000000000 : ℝ), (2547862507/5000000000 : ℝ)] ![(3220112634531/50000000000000 : ℝ), (49809936059959/100000000000000 : ℝ), (43749838660781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106813117/1000000000 : ℝ)|^5551 ≤ (3220112634531/50000000000000 : ℝ)^4527
        have hw : |(-106813117/1000000000 : ℝ)|=(106813117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5664381399/10000000000 : ℝ)|^5551 ≤ (49809936059959/100000000000000 : ℝ)^4527
        have hw : |(5664381399/10000000000 : ℝ)|=(5664381399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547862507/5000000000 : ℝ)|^5551 ≤ (43749838660781/100000000000000 : ℝ)^4527
        have hw : |(2547862507/5000000000 : ℝ)|=(2547862507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_13 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2713992943/5000000000 : ℝ)*x 0 + (-175048841/1250000000 : ℝ)*x 1 + (5095725447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2713992943/5000000000 : ℝ)^5551 ≤ (4727313667447/10000000000000 : ℝ)^4527 := by
    have hnat : (2713992943 : ℕ)^5551*10000000000000^4527 ≤ 4727313667447^4527*5000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713992943 5000000000 4727313667447 10000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175048841/1250000000 : ℝ)^5551 ≤ (8977020093387/100000000000000 : ℝ)^4527 := by
    have hnat : (175048841 : ℕ)^5551*100000000000000^4527 ≤ 8977020093387^4527*1250000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175048841 1250000000 8977020093387 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5095725447/10000000000 : ℝ)^5551 ≤ (43749843219251/100000000000000 : ℝ)^4527 := by
    have hnat : (5095725447 : ℕ)^5551*100000000000000^4527 ≤ 43749843219251^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095725447 10000000000 43749843219251 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2713992943/5000000000 : ℝ), (-175048841/1250000000 : ℝ), (5095725447/10000000000 : ℝ)] ![(4727313667447/10000000000000 : ℝ), (8977020093387/100000000000000 : ℝ), (43749843219251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2713992943/5000000000 : ℝ)|^5551 ≤ (4727313667447/10000000000000 : ℝ)^4527
        have hw : |(2713992943/5000000000 : ℝ)|=(2713992943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-175048841/1250000000 : ℝ)|^5551 ≤ (8977020093387/100000000000000 : ℝ)^4527
        have hw : |(-175048841/1250000000 : ℝ)|=(175048841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5095725447/10000000000 : ℝ)|^5551 ≤ (43749843219251/100000000000000 : ℝ)^4527
        have hw : |(5095725447/10000000000 : ℝ)|=(5095725447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_14 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5427985689/10000000000 : ℝ)*x 0 + (5095725271/10000000000 : ℝ)*x 1 + (-21881113/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5427985689/10000000000 : ℝ)^5551 ≤ (47273134570679/100000000000000 : ℝ)^4527 := by
    have hnat : (5427985689 : ℕ)^5551*100000000000000^4527 ≤ 47273134570679^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427985689 10000000000 47273134570679 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5095725271/10000000000 : ℝ)^5551 ≤ (8749968273277/20000000000000 : ℝ)^4527 := by
    have hnat : (5095725271 : ℕ)^5551*20000000000000^4527 ≤ 8749968273277^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5095725271 10000000000 8749968273277 20000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21881113/156250000 : ℝ)^5551 ≤ (448851202751/5000000000000 : ℝ)^4527 := by
    have hnat : (21881113 : ℕ)^5551*5000000000000^4527 ≤ 448851202751^4527*156250000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21881113 156250000 448851202751 5000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5427985689/10000000000 : ℝ), (5095725271/10000000000 : ℝ), (-21881113/156250000 : ℝ)] ![(47273134570679/100000000000000 : ℝ), (8749968273277/20000000000000 : ℝ), (448851202751/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5427985689/10000000000 : ℝ)|^5551 ≤ (47273134570679/100000000000000 : ℝ)^4527
        have hw : |(5427985689/10000000000 : ℝ)|=(5427985689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5095725271/10000000000 : ℝ)|^5551 ≤ (8749968273277/20000000000000 : ℝ)^4527
        have hw : |(5095725271/10000000000 : ℝ)|=(5095725271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21881113/156250000 : ℝ)|^5551 ≤ (448851202751/5000000000000 : ℝ)^4527
        have hw : |(-21881113/156250000 : ℝ)|=(21881113/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1736_box_15 (p : ℝ) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337667377/1000000000 : ℝ)*x 0 + (4424549661/10000000000 : ℝ)*x 1 + (4424549423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337667377/1000000000 : ℝ)^5551 ≤ (26413996160319/100000000000000 : ℝ)^4527 := by
    have hnat : (337667377 : ℕ)^5551*100000000000000^4527 ≤ 26413996160319^4527*1000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337667377 1000000000 26413996160319 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4424549661/10000000000 : ℝ)^5551 ≤ (36793003128551/100000000000000 : ℝ)^4527 := by
    have hnat : (4424549661 : ℕ)^5551*100000000000000^4527 ≤ 36793003128551^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424549661 10000000000 36793003128551 100000000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4424549423/10000000000 : ℝ)^5551 ≤ (4599125087719/12500000000000 : ℝ)^4527 := by
    have hnat : (4424549423 : ℕ)^5551*12500000000000^4527 ≤ 4599125087719^4527*10000000000^5551 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424549423 10000000000 4599125087719 12500000000000 5551 4527 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5551/1024 : ℝ)) 5551 4527 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337667377/1000000000 : ℝ), (4424549661/10000000000 : ℝ), (4424549423/10000000000 : ℝ)] ![(26413996160319/100000000000000 : ℝ), (36793003128551/100000000000000 : ℝ), (4599125087719/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337667377/1000000000 : ℝ)|^5551 ≤ (26413996160319/100000000000000 : ℝ)^4527
        have hw : |(337667377/1000000000 : ℝ)|=(337667377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4424549661/10000000000 : ℝ)|^5551 ≤ (36793003128551/100000000000000 : ℝ)^4527
        have hw : |(4424549661/10000000000 : ℝ)|=(4424549661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4424549423/10000000000 : ℝ)|^5551 ≤ (4599125087719/12500000000000 : ℝ)^4527
        have hw : |(4424549423/10000000000 : ℝ)|=(4424549423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1736_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1767/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13733/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1794/3125 : ℝ) ∧ (80711/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11579/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18251/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1767/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18251/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1767/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18251/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1767/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18251/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1767/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18251/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1767/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18251/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1767/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1767/20000 : ℝ) ^ (5535/1024 : ℝ) ≤ (201353079855983/100000000000000000000 : ℝ) := by
    have hpowers : (1767/20000 : ℝ)^5535 ≤ (201353079855983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1767 : ℕ)^5535*100000000000000000000^1024 ≤ 201353079855983^1024*20000^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1767 20000 201353079855983 100000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1767/20000 : ℝ)) (X := (201353079855983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18251/100000 : ℝ) ^ (5535/1024 : ℝ) ≤ (10163713932851669/100000000000000000000 : ℝ) := by
    have hpowers : (18251/100000 : ℝ)^5535 ≤ (10163713932851669/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18251 : ℕ)^5535*100000000000000000000^1024 ≤ 10163713932851669^1024*100000^5535 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18251 100000 10163713932851669 100000000000000000000 5535 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18251/100000 : ℝ)) (X := (10163713932851669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000201353079855983/50000000000000000000 : ℝ) ≤ (500000372511681/500000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (50000201353079855983/50000000000000000000 : ℝ)^1024 ≤ (500000372511681/500000000000000 : ℝ)^5535 := by
      have hnat : (50000201353079855983 : ℕ)^1024*500000000000000^5535 ≤ 500000372511681^5535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000201353079855983 50000000000000000000 500000372511681 500000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000372511681/500000000000000 : ℝ)) (X := (50000201353079855983/50000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25002591266753176913/25000000000000000000 : ℝ) ≤ (5000095875161233/5000000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (25002591266753176913/25000000000000000000 : ℝ)^1024 ≤ (5000095875161233/5000000000000000 : ℝ)^5535 := by
      have hnat : (25002591266753176913 : ℕ)^1024*5000000000000000^5535 ≤ 5000095875161233^5535*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002591266753176913 25000000000000000000 5000095875161233 5000000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000095875161233/5000000000000000 : ℝ)) (X := (25002591266753176913/25000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50010163713932851669/50000000000000000000 : ℝ) ≤ (625023503150707/625000000000000 : ℝ) ^ (5535/1024 : ℝ) := by
    have hpowers : (50010163713932851669/50000000000000000000 : ℝ)^1024 ≤ (625023503150707/625000000000000 : ℝ)^5535 := by
      have hnat : (50010163713932851669 : ℕ)^1024*625000000000000^5535 ≤ 625023503150707^5535*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010163713932851669 50000000000000000000 625023503150707 625000000000000 1024 5535 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625023503150707/625000000000000 : ℝ)) (X := (50010163713932851669/50000000000000000000 : ℝ)) (by norm_num) 5535 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(201353079855983/100000000000000000000 : ℝ) ≤ ((941568135688298571/941600000000000000 : ℝ)+2*(92150044423/470800000000000 : ℝ)*(1767/20000 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (941568135688298571/941600000000000000 : ℝ)+2*(92150044423/470800000000000 : ℝ)*(1767/20000 : ℝ)=(500000372511681/500000000000000 : ℝ) by norm_num, show 1+2*(201353079855983/100000000000000000000 : ℝ)=(50000201353079855983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10163713932851669/100000000000000000000 : ℝ)+(201353079855983/100000000000000000000 : ℝ) ≤ ((941568135688298571/941600000000000000 : ℝ)+(92150044423/470800000000000 : ℝ)*((18251/100000 : ℝ)+(1767/20000 : ℝ)))^(5535/1024 : ℝ) := by
    rw [show (941568135688298571/941600000000000000 : ℝ)+(92150044423/470800000000000 : ℝ)*((18251/100000 : ℝ)+(1767/20000 : ℝ))=(5000095875161233/5000000000000000 : ℝ) by norm_num, show 1+(10163713932851669/100000000000000000000 : ℝ)+(201353079855983/100000000000000000000 : ℝ)=(25002591266753176913/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10163713932851669/100000000000000000000 : ℝ) ≤ ((941568135688298571/941600000000000000 : ℝ)+2*(92150044423/470800000000000 : ℝ)*(18251/100000 : ℝ))^(5535/1024 : ℝ) := by
    rw [show (941568135688298571/941600000000000000 : ℝ)+2*(92150044423/470800000000000 : ℝ)*(18251/100000 : ℝ)=(625023503150707/625000000000000 : ℝ) by norm_num, show 1+2*(10163713932851669/100000000000000000000 : ℝ)=(50010163713932851669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (941568135688298571/941600000000000000 : ℝ)*(X 1 0+X 2 0)+(92150044423/470800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (1767/20000 : ℝ)) (hi := (18251/100000 : ℝ)) (c := (941568135688298571/941600000000000000 : ℝ)) (alpha := (92150044423/470800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (941568135688298571/941600000000000000 : ℝ)*(X 0 1+X 2 1)+(92150044423/470800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (1767/20000 : ℝ)) (hi := (18251/100000 : ℝ)) (c := (941568135688298571/941600000000000000 : ℝ)) (alpha := (92150044423/470800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (941568135688298571/941600000000000000 : ℝ)*(X 0 2+X 1 2)+(92150044423/470800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5535/1024 : ℝ)) (lo := (1767/20000 : ℝ)) (hi := (18251/100000 : ℝ)) (c := (941568135688298571/941600000000000000 : ℝ)) (alpha := (92150044423/470800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-223400303/2500000000 : ℝ)*X 0 0+(680130109/1250000000 : ℝ)*X 0 1+(5441041941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((103906849/200000000 : ℝ)*X 1 0+(-155872177/1250000000 : ℝ)*X 1 1+(170032553/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1298835527/2500000000 : ℝ)*X 2 0+(1088208463/2000000000 : ℝ)*X 2 1+(-49879081/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((458052187/1000000000 : ℝ)*X 0 0+(956969001/2500000000 : ℝ)*X 0 1+(956968517/2500000000 : ℝ)*X 0 2+(458052187/1000000000 : ℝ)*X 1 0+(956969001/2500000000 : ℝ)*X 1 1+(956968517/2500000000 : ℝ)*X 1 2+(458052187/1000000000 : ℝ)*X 2 0+(956969001/2500000000 : ℝ)*X 2 1+(956968517/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219629079/1250000000 : ℝ)*X 0 0+(205051609/400000000 : ℝ)*X 0 1+(5126290031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1081466147/2000000000 : ℝ)*X 1 0+(-1387462911/10000000000 : ℝ)*X 1 1+(256314523/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((540733047/1000000000 : ℝ)*X 2 0+(1025258127/2000000000 : ℝ)*X 2 1+(-1387463037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1743993409/5000000000 : ℝ)*X 0 0+(4371929817/10000000000 : ℝ)*X 0 1+(874385703/2000000000 : ℝ)*X 0 2+(1743993409/5000000000 : ℝ)*X 1 0+(4371929817/10000000000 : ℝ)*X 1 1+(874385703/2000000000 : ℝ)*X 1 2+(1743993409/5000000000 : ℝ)*X 2 0+(4371929817/10000000000 : ℝ)*X 2 1+(874385703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1569761121/10000000000 : ℝ)*X 0 0+(4888209103/10000000000 : ℝ)*X 0 1+(2752581271/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152208351/10000000000 : ℝ)*X 1 0+(-1216806009/10000000000 : ℝ)*X 1 1+(2752581513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1030441629/2000000000 : ℝ)*X 2 0+(688145377/1250000000 : ℝ)*X 2 1+(-121680631/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4792365721/10000000000 : ℝ)*X 0 0+(1858312423/5000000000 : ℝ)*X 0 1+(743325073/2000000000 : ℝ)*X 0 2+(4792365721/10000000000 : ℝ)*X 1 0+(1858312423/5000000000 : ℝ)*X 1 1+(743325073/2000000000 : ℝ)*X 1 2+(4792365721/10000000000 : ℝ)*X 2 0+(1858312423/5000000000 : ℝ)*X 2 1+(743325073/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-106813117/1000000000 : ℝ)*X 0 0+(5664381399/10000000000 : ℝ)*X 0 1+(2547862507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2713992943/5000000000 : ℝ)*X 1 0+(-175048841/1250000000 : ℝ)*X 1 1+(5095725447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5427985689/10000000000 : ℝ)*X 2 0+(5095725271/10000000000 : ℝ)*X 2 1+(-21881113/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((337667377/1000000000 : ℝ)*X 0 0+(4424549661/10000000000 : ℝ)*X 0 1+(4424549423/10000000000 : ℝ)*X 0 2+(337667377/1000000000 : ℝ)*X 1 0+(4424549661/10000000000 : ℝ)*X 1 1+(4424549423/10000000000 : ℝ)*X 1 2+(337667377/1000000000 : ℝ)*X 2 0+(4424549661/10000000000 : ℝ)*X 2 1+(4424549423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1736_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13733/20000 : ℝ) ≤ (-1469369266265736224570557293/2140000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5124471/20000000000000 : ℝ)*(upper1) + (42548853/50000000000000 : ℝ)*(upper3) + (3485199/50000000000000 : ℝ)*(lower4) + (6596419/100000000000000 : ℝ)*(upper5) + (1001405702401313/100000000000000 : ℝ)*(major0) + (1001405702401313/100000000000000 : ℝ)*(major1) + (1001405702401313/100000000000000 : ℝ)*(major2) + (180852619/25000000000000 : ℝ)*(sp3) + (768509183736371/50000000000000 : ℝ)*(sp4) + (192127031631193/12500000000000 : ℝ)*(sp5) + (768499954117161/50000000000000 : ℝ)*(sp6) + (488679685668091/100000000000000 : ℝ)*(sp7) + (2114423199/100000000000000 : ℝ)*(sp13) + (18459238421/100000000000000 : ℝ)*(sp14) + (488680409078567/100000000000000 : ℝ)*(f.failure) + (768509183736371/50000000000000 : ℝ)*(f.sum) + (12088533009651/2140000000000000000000000000 : ℝ)*base66 + (35573848426823793/8560000000000000000000000000000 : ℝ)*base67 + (27146939015783793/8560000000000000000000000000000 : ℝ)*base69 + (52583918187336207/8560000000000000000000000000000 : ℝ)*base72 + (673790516991/2140000000000000000000000000 : ℝ)*base74 + (8253647780823793/8560000000000000000000000000000 : ℝ)*base75 + (4009721010136207/8560000000000000000000000000000 : ℝ)*base78 + (1143968643336207/8560000000000000000000000000000 : ℝ)*base80 + (6270627499729/2140000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (870979/1000000000000000000000 : ℝ)*base89 + (870979/1000000000000000000000 : ℝ)*base91 + (870979/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1794/3125 : ℝ) ≤ (844654301986965162847019589/1471250000000000000000000000 : ℝ) := by norm_num
    linear_combination (7794053/5000000000000 : ℝ)*(lower0) + (27389147/100000000000000 : ℝ)*(lower1) + (125647/250000000000 : ℝ)*(lower3) + (279161596545341/25000000000000 : ℝ)*(major0) + (279161596545341/25000000000000 : ℝ)*(major1) + (279161596545341/25000000000000 : ℝ)*(major2) + (834619172115719/50000000000000 : ℝ)*(sp0) + (1669237581760547/100000000000000 : ℝ)*(sp1) + (16692361925563/1000000000000 : ℝ)*(sp2) + (272458492401787/50000000000000 : ℝ)*(sp3) + (77267023/3125000000000 : ℝ)*(sp6) + (14784067/6250000000000 : ℝ)*(sp7) + (135417561/12500000000000 : ℝ)*(sp9) + (320869597/100000000000000 : ℝ)*(sp12) + (272458610674323/50000000000000 : ℝ)*(f.failure) + (333847733020207/20000000000000 : ℝ)*(f.sum) + (5819840359807/5885000000000000000000000000 : ℝ)*base66 + (52339157616633711/23540000000000000000000000000000 : ℝ)*base67 + (54428333649626289/23540000000000000000000000000000 : ℝ)*base70 + (28496681445933711/23540000000000000000000000000000 : ℝ)*base71 + (2446417512483/5885000000000000000000000000 : ℝ)*base73 + (105939708121013711/23540000000000000000000000000000 : ℝ)*base75 + (116209604316346289/23540000000000000000000000000000 : ℝ)*base78 + (59674089695706289/23540000000000000000000000000000 : ℝ)*base80 + (2382475786943/5885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1865951/500000000000000000000 : ℝ)*base89 + (1865951/500000000000000000000 : ℝ)*base91 + (1865951/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80711/100000 : ℝ) ≤ (593749636621878946114212220599/735625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26083373/100000000000000 : ℝ)*(lower1) + (10801637/25000000000000 : ℝ)*(upper2) + (40403983/100000000000000 : ℝ)*(lower5) + (17028003472391/1562500000000 : ℝ)*(major0) + (17028003472391/1562500000000 : ℝ)*(major1) + (17028003472391/1562500000000 : ℝ)*(major2) + (31643333/4000000000000 : ℝ)*(sp0) + (8957874297/100000000000000 : ℝ)*(sp1) + (6682043817/100000000000000 : ℝ)*(sp2) + (545999229/25000000000000 : ℝ)*(sp3) + (1620866571424989/100000000000000 : ℝ)*(sp8) + (1620858404634017/100000000000000 : ℝ)*(sp9) + (1620860680464497/100000000000000 : ℝ)*(sp10) + (531810354811707/100000000000000 : ℝ)*(sp11) + (531812538808623/100000000000000 : ℝ)*(f.failure) + (810433681254157/50000000000000 : ℝ)*(f.sum) + (8842057759779/2942500000000000000000000000 : ℝ)*base65 + (7632100976436989/1471250000000000000000000000000 : ℝ)*base68 + (3846145346538239/1471250000000000000000000000000 : ℝ)*base70 + (4973290683795739/1471250000000000000000000000000 : ℝ)*base72 + (18136171894603/5885000000000000000000000000 : ℝ)*base73 + (605933923421989/1471250000000000000000000000000 : ℝ)*base76 + (1050630227630739/1471250000000000000000000000000 : ℝ)*base78 + (2000781316536989/1471250000000000000000000000000 : ℝ)*base80 + (1190323391351/735625000000000000000000000 : ℝ)*base81 + (1564949/1000000000000000000000 : ℝ)*base90 + (1564949/1000000000000000000000 : ℝ)*base92 + (1564949/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-11579/12500 : ℝ) ≤ (-1982262509155526895998230985901/2140000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64206049/100000000000000 : ℝ)*(lower0) + (88889/25000000000000 : ℝ)*(lower1) + (9543613/10000000000000 : ℝ)*(lower4) + (1142626744920153/100000000000000 : ℝ)*(major0) + (1142626744920153/100000000000000 : ℝ)*(major1) + (1142626744920153/100000000000000 : ℝ)*(major2) + (161879359/5000000000000 : ℝ)*(sp0) + (5890785041/50000000000000 : ℝ)*(sp5) + (41213803817/100000000000000 : ℝ)*(sp6) + (5629165417/100000000000000 : ℝ)*(sp7) + (879265561757093/50000000000000 : ℝ)*(sp12) + (439630644882821/25000000000000 : ℝ)*(sp13) + (1758493147297549/100000000000000 : ℝ)*(sp14) + (139397465661119/25000000000000 : ℝ)*(sp15) + (557595491809893/100000000000000 : ℝ)*(f.failure) + (879267180550683/50000000000000 : ℝ)*(f.sum) + (76746201538121/23540000000000000000000000000 : ℝ)*base66 + (120786122533400637/94160000000000000000000000000000 : ℝ)*base68 + (106281677339480637/94160000000000000000000000000000 : ℝ)*base70 + (385468660430760637/94160000000000000000000000000000 : ℝ)*base72 + (72486334073379/23540000000000000000000000000 : ℝ)*base73 + (594165755504920637/94160000000000000000000000000000 : ℝ)*base76 + (33371686365880637/94160000000000000000000000000000 : ℝ)*base78 + (267551619082599363/94160000000000000000000000000000 : ℝ)*base79 + (67983969954521/23540000000000000000000000000 : ℝ)*base82 + (5677959/1000000000000000000000 : ℝ)*base90 + (5677959/1000000000000000000000 : ℝ)*base92 + (5677959/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1736_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18251/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1767/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13733/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(1794/3125 : ℝ) else (80711/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11579/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1736_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1736_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13733/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(1794/3125 : ℝ) else (80711/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11579/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1736_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1736_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5535/1024 : ℝ) ≤ p) (hpb : p ≤ (5551/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20492037/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9127/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (276/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13733/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(1794/3125 : ℝ) else (80711/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11579/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1736_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1414_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:31.508975+00:00
-- url     : https://prove2.me/submissions/295fbb0e-37af-4166-b415-600bb4794514

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
theorem support_rectangle_w1414_s6_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-396673087/2000000000 : ℝ)*x 0 + (338062131/625000000 : ℝ)*x 1 + (5246560117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396673087/2000000000 : ℝ)^2187 ≤ (12095913778003/100000000000000 : ℝ)^1675 := by
    have hnat : (396673087 : ℕ)^2187*100000000000000^1675 ≤ 12095913778003^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396673087 2000000000 12095913778003 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338062131/625000000 : ℝ)^2187 ≤ (8965361126521/20000000000000 : ℝ)^1675 := by
    have hnat : (338062131 : ℕ)^2187*20000000000000^1675 ≤ 8965361126521^1675*625000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338062131 625000000 8965361126521 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246560117/10000000000 : ℝ)^2187 ≤ (43077280579759/100000000000000 : ℝ)^1675 := by
    have hnat : (5246560117 : ℕ)^2187*100000000000000^1675 ≤ 43077280579759^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246560117 10000000000 43077280579759 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396673087/2000000000 : ℝ), (338062131/625000000 : ℝ), (5246560117/10000000000 : ℝ)] ![(12095913778003/100000000000000 : ℝ), (8965361126521/20000000000000 : ℝ), (43077280579759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396673087/2000000000 : ℝ)|^2187 ≤ (12095913778003/100000000000000 : ℝ)^1675
        have hw : |(-396673087/2000000000 : ℝ)|=(396673087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338062131/625000000 : ℝ)|^2187 ≤ (8965361126521/20000000000000 : ℝ)^1675
        have hw : |(338062131/625000000 : ℝ)|=(338062131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246560117/10000000000 : ℝ)|^2187 ≤ (43077280579759/100000000000000 : ℝ)^1675
        have hw : |(5246560117/10000000000 : ℝ)|=(5246560117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668454823/1250000000 : ℝ)*x 0 + (-413214767/2000000000 : ℝ)*x 1 + (5246560213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668454823/1250000000 : ℝ)^2187 ≤ (1766562008887/4000000000000 : ℝ)^1675 := by
    have hnat : (668454823 : ℕ)^2187*4000000000000^1675 ≤ 1766562008887^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668454823 1250000000 1766562008887 4000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413214767/2000000000 : ℝ)^2187 ≤ (12758668148531/100000000000000 : ℝ)^1675 := by
    have hnat : (413214767 : ℕ)^2187*100000000000000^1675 ≤ 12758668148531^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413214767 2000000000 12758668148531 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246560213/10000000000 : ℝ)^2187 ≤ (4307728160891/10000000000000 : ℝ)^1675 := by
    have hnat : (5246560213 : ℕ)^2187*10000000000000^1675 ≤ 4307728160891^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246560213 10000000000 4307728160891 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668454823/1250000000 : ℝ), (-413214767/2000000000 : ℝ), (5246560213/10000000000 : ℝ)] ![(1766562008887/4000000000000 : ℝ), (12758668148531/100000000000000 : ℝ), (4307728160891/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668454823/1250000000 : ℝ)|^2187 ≤ (1766562008887/4000000000000 : ℝ)^1675
        have hw : |(668454823/1250000000 : ℝ)|=(668454823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413214767/2000000000 : ℝ)|^2187 ≤ (12758668148531/100000000000000 : ℝ)^1675
        have hw : |(-413214767/2000000000 : ℝ)|=(413214767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246560213/10000000000 : ℝ)|^2187 ≤ (4307728160891/10000000000000 : ℝ)^1675
        have hw : |(5246560213/10000000000 : ℝ)|=(5246560213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347638571/10000000000 : ℝ)*x 0 + (2623280053/5000000000 : ℝ)*x 1 + (-413214799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347638571/10000000000 : ℝ)^2187 ≤ (8832810016399/20000000000000 : ℝ)^1675 := by
    have hnat : (5347638571 : ℕ)^2187*20000000000000^1675 ≤ 8832810016399^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347638571 10000000000 8832810016399 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623280053/5000000000 : ℝ)^2187 ≤ (10769320115459/25000000000000 : ℝ)^1675 := by
    have hnat : (2623280053 : ℕ)^2187*25000000000000^1675 ≤ 10769320115459^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623280053 5000000000 10769320115459 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413214799/2000000000 : ℝ)^2187 ≤ (6379334719301/50000000000000 : ℝ)^1675 := by
    have hnat : (413214799 : ℕ)^2187*50000000000000^1675 ≤ 6379334719301^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413214799 2000000000 6379334719301 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347638571/10000000000 : ℝ), (2623280053/5000000000 : ℝ), (-413214799/2000000000 : ℝ)] ![(8832810016399/20000000000000 : ℝ), (10769320115459/25000000000000 : ℝ), (6379334719301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347638571/10000000000 : ℝ)|^2187 ≤ (8832810016399/20000000000000 : ℝ)^1675
        have hw : |(5347638571/10000000000 : ℝ)|=(5347638571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623280053/5000000000 : ℝ)|^2187 ≤ (10769320115459/25000000000000 : ℝ)^1675
        have hw : |(2623280053/5000000000 : ℝ)|=(2623280053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413214799/2000000000 : ℝ)|^2187 ≤ (6379334719301/50000000000000 : ℝ)^1675
        have hw : |(-413214799/2000000000 : ℝ)|=(413214799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4308137961/10000000000 : ℝ)*x 0 + (2068306307/5000000000 : ℝ)*x 1 + (4486080789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308137961/10000000000 : ℝ)^2187 ≤ (16652226487043/50000000000000 : ℝ)^1675 := by
    have hnat : (4308137961 : ℕ)^2187*50000000000000^1675 ≤ 16652226487043^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308137961 10000000000 16652226487043 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068306307/5000000000 : ℝ)^2187 ≤ (31583776259203/100000000000000 : ℝ)^1675 := by
    have hnat : (2068306307 : ℕ)^2187*100000000000000^1675 ≤ 31583776259203^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068306307 5000000000 31583776259203 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486080789/10000000000 : ℝ)^2187 ≤ (35111770762059/100000000000000 : ℝ)^1675 := by
    have hnat : (4486080789 : ℕ)^2187*100000000000000^1675 ≤ 35111770762059^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486080789 10000000000 35111770762059 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308137961/10000000000 : ℝ), (2068306307/5000000000 : ℝ), (4486080789/10000000000 : ℝ)] ![(16652226487043/50000000000000 : ℝ), (31583776259203/100000000000000 : ℝ), (35111770762059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308137961/10000000000 : ℝ)|^2187 ≤ (16652226487043/50000000000000 : ℝ)^1675
        have hw : |(4308137961/10000000000 : ℝ)|=(4308137961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2068306307/5000000000 : ℝ)|^2187 ≤ (31583776259203/100000000000000 : ℝ)^1675
        have hw : |(2068306307/5000000000 : ℝ)|=(2068306307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486080789/10000000000 : ℝ)|^2187 ≤ (35111770762059/100000000000000 : ℝ)^1675
        have hw : |(4486080789/10000000000 : ℝ)|=(4486080789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-396675433/2000000000 : ℝ)*x 0 + (1311786299/2500000000 : ℝ)*x 1 + (169012681/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396675433/2000000000 : ℝ)^2187 ≤ (6048003591307/50000000000000 : ℝ)^1675 := by
    have hnat : (396675433 : ℕ)^2187*50000000000000^1675 ≤ 6048003591307^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396675433 2000000000 6048003591307 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311786299/2500000000 : ℝ)^2187 ≤ (5385444114821/12500000000000 : ℝ)^1675 := by
    have hnat : (1311786299 : ℕ)^2187*12500000000000^1675 ≤ 5385444114821^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311786299 2500000000 5385444114821 12500000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169012681/312500000 : ℝ)^2187 ≤ (11205109969701/25000000000000 : ℝ)^1675 := by
    have hnat : (169012681 : ℕ)^2187*25000000000000^1675 ≤ 11205109969701^1675*312500000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169012681 312500000 11205109969701 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396675433/2000000000 : ℝ), (1311786299/2500000000 : ℝ), (169012681/312500000 : ℝ)] ![(6048003591307/50000000000000 : ℝ), (5385444114821/12500000000000 : ℝ), (11205109969701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396675433/2000000000 : ℝ)|^2187 ≤ (6048003591307/50000000000000 : ℝ)^1675
        have hw : |(-396675433/2000000000 : ℝ)|=(396675433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311786299/2500000000 : ℝ)|^2187 ≤ (5385444114821/12500000000000 : ℝ)^1675
        have hw : |(1311786299/2500000000 : ℝ)|=(1311786299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169012681/312500000 : ℝ)|^2187 ≤ (11205109969701/25000000000000 : ℝ)^1675
        have hw : |(169012681/312500000 : ℝ)|=(169012681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331592071/625000000 : ℝ)*x 0 + (-1904228097/10000000000 : ℝ)*x 1 + (5408405817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331592071/625000000 : ℝ)^2187 ≤ (43709927849571/100000000000000 : ℝ)^1675 := by
    have hnat : (331592071 : ℕ)^2187*100000000000000^1675 ≤ 43709927849571^1675*625000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331592071 625000000 43709927849571 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904228097/10000000000 : ℝ)^2187 ≤ (11469631991539/100000000000000 : ℝ)^1675 := by
    have hnat : (1904228097 : ℕ)^2187*100000000000000^1675 ≤ 11469631991539^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904228097 10000000000 11469631991539 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408405817/10000000000 : ℝ)^2187 ≤ (44820440149313/100000000000000 : ℝ)^1675 := by
    have hnat : (5408405817 : ℕ)^2187*100000000000000^1675 ≤ 44820440149313^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408405817 10000000000 44820440149313 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331592071/625000000 : ℝ), (-1904228097/10000000000 : ℝ), (5408405817/10000000000 : ℝ)] ![(43709927849571/100000000000000 : ℝ), (11469631991539/100000000000000 : ℝ), (44820440149313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331592071/625000000 : ℝ)|^2187 ≤ (43709927849571/100000000000000 : ℝ)^1675
        have hw : |(331592071/625000000 : ℝ)|=(331592071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904228097/10000000000 : ℝ)|^2187 ≤ (11469631991539/100000000000000 : ℝ)^1675
        have hw : |(-1904228097/10000000000 : ℝ)|=(1904228097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408405817/10000000000 : ℝ)|^2187 ≤ (44820440149313/100000000000000 : ℝ)^1675
        have hw : |(5408405817/10000000000 : ℝ)|=(5408405817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652736573/5000000000 : ℝ)*x 0 + (1081681167/2000000000 : ℝ)*x 1 + (-952114029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652736573/5000000000 : ℝ)^2187 ≤ (43709927957141/100000000000000 : ℝ)^1675 := by
    have hnat : (2652736573 : ℕ)^2187*100000000000000^1675 ≤ 43709927957141^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652736573 5000000000 43709927957141 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081681167/2000000000 : ℝ)^2187 ≤ (44820440344079/100000000000000 : ℝ)^1675 := by
    have hnat : (1081681167 : ℕ)^2187*100000000000000^1675 ≤ 44820440344079^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081681167 2000000000 44820440344079 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (952114029/5000000000 : ℝ)^2187 ≤ (2867407921207/25000000000000 : ℝ)^1675 := by
    have hnat : (952114029 : ℕ)^2187*25000000000000^1675 ≤ 2867407921207^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952114029 5000000000 2867407921207 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652736573/5000000000 : ℝ), (1081681167/2000000000 : ℝ), (-952114029/5000000000 : ℝ)] ![(43709927957141/100000000000000 : ℝ), (44820440344079/100000000000000 : ℝ), (2867407921207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652736573/5000000000 : ℝ)|^2187 ≤ (43709927957141/100000000000000 : ℝ)^1675
        have hw : |(2652736573/5000000000 : ℝ)|=(2652736573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081681167/2000000000 : ℝ)|^2187 ≤ (44820440344079/100000000000000 : ℝ)^1675
        have hw : |(1081681167/2000000000 : ℝ)|=(1081681167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-952114029/5000000000 : ℝ)|^2187 ≤ (2867407921207/25000000000000 : ℝ)^1675
        have hw : |(-952114029/5000000000 : ℝ)|=(952114029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_s6_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4308162919/10000000000 : ℝ)*x 0 + (4484822031/10000000000 : ℝ)*x 1 + (2068938791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308162919/10000000000 : ℝ)^2187 ≤ (33304704890717/100000000000000 : ℝ)^1675 := by
    have hnat : (4308162919 : ℕ)^2187*100000000000000^1675 ≤ 33304704890717^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308162919 10000000000 33304704890717 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484822031/10000000000 : ℝ)^2187 ≤ (35098907733577/100000000000000 : ℝ)^1675 := by
    have hnat : (4484822031 : ℕ)^2187*100000000000000^1675 ≤ 35098907733577^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484822031 10000000000 35098907733577 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068938791/5000000000 : ℝ)^2187 ≤ (6319277472071/20000000000000 : ℝ)^1675 := by
    have hnat : (2068938791 : ℕ)^2187*20000000000000^1675 ≤ 6319277472071^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068938791 5000000000 6319277472071 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308162919/10000000000 : ℝ), (4484822031/10000000000 : ℝ), (2068938791/5000000000 : ℝ)] ![(33304704890717/100000000000000 : ℝ), (35098907733577/100000000000000 : ℝ), (6319277472071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308162919/10000000000 : ℝ)|^2187 ≤ (33304704890717/100000000000000 : ℝ)^1675
        have hw : |(4308162919/10000000000 : ℝ)|=(4308162919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484822031/10000000000 : ℝ)|^2187 ≤ (35098907733577/100000000000000 : ℝ)^1675
        have hw : |(4484822031/10000000000 : ℝ)|=(4484822031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2068938791/5000000000 : ℝ)|^2187 ≤ (6319277472071/20000000000000 : ℝ)^1675
        have hw : |(2068938791/5000000000 : ℝ)|=(2068938791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2261/20000 : ℝ) ^ (4373/1024 : ℝ) ≤ (9057003982094447/100000000000000000000 : ℝ) := by
    have hpowers : (2261/20000 : ℝ)^4373 ≤ (9057003982094447/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2261 : ℕ)^4373*100000000000000000000^1024 ≤ 9057003982094447^1024*20000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 20000 9057003982094447 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/20000 : ℝ)) (X := (9057003982094447/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (28229098502507253/100000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^4373 ≤ (28229098502507253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14753 : ℕ)^4373*100000000000000000000^1024 ≤ 28229098502507253^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 28229098502507253 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (28229098502507253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009057003982094447/50000000000000000000 : ℝ) ≤ (5000212067890677/5000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50009057003982094447/50000000000000000000 : ℝ)^1024 ≤ (5000212067890677/5000000000000000 : ℝ)^4373 := by
      have hnat : (50009057003982094447 : ℕ)^1024*5000000000000000^4373 ≤ 5000212067890677^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009057003982094447 50000000000000000000 5000212067890677 5000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000212067890677/5000000000000000 : ℝ)) (X := (50009057003982094447/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1000372861024846017/1000000000000000000 : ℝ) ≤ (78131820174731/78125000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (1000372861024846017/1000000000000000000 : ℝ)^1024 ≤ (78131820174731/78125000000000 : ℝ)^4373 := by
      have hnat : (1000372861024846017 : ℕ)^1024*78125000000000^4373 ≤ 78131820174731^4373*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000372861024846017 1000000000000000000 78131820174731 78125000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78131820174731/78125000000000 : ℝ)) (X := (1000372861024846017/1000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028229098502507253/50000000000000000000 : ℝ) ≤ (5000660914474891/5000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50028229098502507253/50000000000000000000 : ℝ)^1024 ≤ (5000660914474891/5000000000000000 : ℝ)^4373 := by
      have hnat : (50028229098502507253 : ℕ)^1024*5000000000000000^4373 ≤ 5000660914474891^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028229098502507253 50000000000000000000 5000660914474891 5000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000660914474891/5000000000000000 : ℝ)) (X := (50028229098502507253/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9057003982094447/100000000000000000000 : ℝ) ≤ ((8617828499726257513/8620000000000000000 : ℝ)+2*(224423292107/172400000000000 : ℝ)*(2261/20000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (8617828499726257513/8620000000000000000 : ℝ)+2*(224423292107/172400000000000 : ℝ)*(2261/20000 : ℝ)=(5000212067890677/5000000000000000 : ℝ) by norm_num, show 1+2*(9057003982094447/100000000000000000000 : ℝ)=(50009057003982094447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28229098502507253/100000000000000000000 : ℝ)+(9057003982094447/100000000000000000000 : ℝ) ≤ ((8617828499726257513/8620000000000000000 : ℝ)+(224423292107/172400000000000 : ℝ)*((14753/100000 : ℝ)+(2261/20000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (8617828499726257513/8620000000000000000 : ℝ)+(224423292107/172400000000000 : ℝ)*((14753/100000 : ℝ)+(2261/20000 : ℝ))=(78131820174731/78125000000000 : ℝ) by norm_num, show 1+(28229098502507253/100000000000000000000 : ℝ)+(9057003982094447/100000000000000000000 : ℝ)=(1000372861024846017/1000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28229098502507253/100000000000000000000 : ℝ) ≤ ((8617828499726257513/8620000000000000000 : ℝ)+2*(224423292107/172400000000000 : ℝ)*(14753/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (8617828499726257513/8620000000000000000 : ℝ)+2*(224423292107/172400000000000 : ℝ)*(14753/100000 : ℝ)=(5000660914474891/5000000000000000 : ℝ) by norm_num, show 1+2*(28229098502507253/100000000000000000000 : ℝ)=(50028229098502507253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8617828499726257513/8620000000000000000 : ℝ)*(X 1 0+X 2 0)+(224423292107/172400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (8617828499726257513/8620000000000000000 : ℝ)) (alpha := (224423292107/172400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8617828499726257513/8620000000000000000 : ℝ)*(X 0 1+X 2 1)+(224423292107/172400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (8617828499726257513/8620000000000000000 : ℝ)) (alpha := (224423292107/172400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8617828499726257513/8620000000000000000 : ℝ)*(X 0 2+X 1 2)+(224423292107/172400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (8617828499726257513/8620000000000000000 : ℝ)) (alpha := (224423292107/172400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-396673087/2000000000 : ℝ)*X 0 0+(338062131/625000000 : ℝ)*X 0 1+(5246560117/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668454823/1250000000 : ℝ)*X 1 0+(-413214767/2000000000 : ℝ)*X 1 1+(5246560213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347638571/10000000000 : ℝ)*X 2 0+(2623280053/5000000000 : ℝ)*X 2 1+(-413214799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308137961/10000000000 : ℝ)*X 0 0+(2068306307/5000000000 : ℝ)*X 0 1+(4486080789/10000000000 : ℝ)*X 0 2+(4308137961/10000000000 : ℝ)*X 1 0+(2068306307/5000000000 : ℝ)*X 1 1+(4486080789/10000000000 : ℝ)*X 1 2+(4308137961/10000000000 : ℝ)*X 2 0+(2068306307/5000000000 : ℝ)*X 2 1+(4486080789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-396675433/2000000000 : ℝ)*X 0 0+(1311786299/2500000000 : ℝ)*X 0 1+(169012681/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331592071/625000000 : ℝ)*X 1 0+(-1904228097/10000000000 : ℝ)*X 1 1+(5408405817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652736573/5000000000 : ℝ)*X 2 0+(1081681167/2000000000 : ℝ)*X 2 1+(-952114029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308162919/10000000000 : ℝ)*X 0 0+(4484822031/10000000000 : ℝ)*X 0 1+(2068938791/5000000000 : ℝ)*X 0 2+(4308162919/10000000000 : ℝ)*X 1 0+(4484822031/10000000000 : ℝ)*X 1 1+(2068938791/5000000000 : ℝ)*X 1 2+(4308162919/10000000000 : ℝ)*X 2 0+(4484822031/10000000000 : ℝ)*X 2 1+(2068938791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66183521832651235417257/8620000000000000000000000000 : ℝ) := by norm_num
    linear_combination (257419219/100000000000000 : ℝ)*(base19) + (458373979/100000000000000 : ℝ)*(base23) + (8602299/20000000000000 : ℝ)*(upper3) + (579793/500000000000 : ℝ)*(lower4) + (4508932867341617/100000000000000 : ℝ)*(major0) + (4508932867341617/100000000000000 : ℝ)*(major1) + (4508932867341617/100000000000000 : ℝ)*(major2) + (3078180227955463/50000000000000 : ℝ)*(sp0) + (6156368753080717/100000000000000 : ℝ)*(sp1) + (6156368435447651/100000000000000 : ℝ)*(sp2) + (1430746921904081/50000000000000 : ℝ)*(sp3) + (855458901/10000000000000 : ℝ)*(sp4) + (58339153/50000000000000 : ℝ)*(sp6) + (32805563/1250000000000 : ℝ)*(sp7) + (1430748234126601/50000000000000 : ℝ)*(f.failure) + (192386531578123/3125000000000 : ℝ)*(f.sum) + (28307479327821/8620000000000000000000000000 : ℝ)*base66 + (2158834525633231479/862000000000000000000000000000000 : ℝ)*base68 + (20252516214768521/862000000000000000000000000000000 : ℝ)*base69 + (5250460974005231479/862000000000000000000000000000000 : ℝ)*base72 + (1543948435041/8620000000000000000000000000 : ℝ)*base74 + (132287984556768521/862000000000000000000000000000000 : ℝ)*base75 + (3156510665316768521/862000000000000000000000000000000 : ℝ)*base77 + (9369065988553231479/862000000000000000000000000000000 : ℝ)*base80 + (14253446361919/8620000000000000000000000000 : ℝ)*base81 + (9977253/5000000000000000000000 : ℝ)*base90 + (9977253/5000000000000000000000 : ℝ)*base92 + (9977253/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129101141683526598951069327/26937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (382392029/50000000000000 : ℝ)*(base19) + (838669159/100000000000000 : ℝ)*(base23) + (252602793/100000000000000 : ℝ)*(lower1) + (114057823/100000000000000 : ℝ)*(upper3) + (17083377/100000000000000 : ℝ)*(lower4) + (66237169/100000000000000 : ℝ)*(upper5) + (283857020903893/6250000000000 : ℝ)*(major0) + (283857020903893/6250000000000 : ℝ)*(major1) + (283857020903893/6250000000000 : ℝ)*(major2) + (1887216549/50000000000000 : ℝ)*(sp2) + (1240225052586109/20000000000000 : ℝ)*(sp4) + (6201124498146487/100000000000000 : ℝ)*(sp5) + (6201120649828289/100000000000000 : ℝ)*(sp6) + (115291969849603/4000000000000 : ℝ)*(sp7) + (115291969849603/4000000000000 : ℝ)*(f.failure) + (1240225052586109/20000000000000 : ℝ)*(f.sum) + (902394519949/538750000000000000000000000 : ℝ)*base66 + (3262795057657873109/53875000000000000000000000000000 : ℝ)*base67 + (335807717779001891/53875000000000000000000000000000 : ℝ)*base70 + (9444253733511373109/53875000000000000000000000000000 : ℝ)*base71 + (1756380290063/1077500000000000000000000000 : ℝ)*base74 + (526374272905126891/53875000000000000000000000000000 : ℝ)*base76 + (78323673053626891/53875000000000000000000000000000 : ℝ)*base78 + (973398502663751891/53875000000000000000000000000000 : ℝ)*base80 + (8634744084693/1077500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (351159/400000000000000000000 : ℝ)*base90 + (351159/400000000000000000000 : ℝ)*base92 + (351159/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1414_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1414_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1414_box_0 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-18216091/100000000 : ℝ)*x 0 + (5386900177/10000000000 : ℝ)*x 1 + (2693449891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18216091/100000000 : ℝ)^2187 ≤ (5412118716151/50000000000000 : ℝ)^1675 := by
    have hnat : (18216091 : ℕ)^2187*50000000000000^1675 ≤ 5412118716151^1675*100000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18216091 100000000 5412118716151 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386900177/10000000000 : ℝ)^2187 ≤ (8917576681621/20000000000000 : ℝ)^1675 := by
    have hnat : (5386900177 : ℕ)^2187*20000000000000^1675 ≤ 8917576681621^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386900177 10000000000 8917576681621 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693449891/5000000000 : ℝ)^2187 ≤ (22293939569637/50000000000000 : ℝ)^1675 := by
    have hnat : (2693449891 : ℕ)^2187*50000000000000^1675 ≤ 22293939569637^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693449891 5000000000 22293939569637 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18216091/100000000 : ℝ), (5386900177/10000000000 : ℝ), (2693449891/5000000000 : ℝ)] ![(5412118716151/50000000000000 : ℝ), (8917576681621/20000000000000 : ℝ), (22293939569637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18216091/100000000 : ℝ)|^2187 ≤ (5412118716151/50000000000000 : ℝ)^1675
        have hw : |(-18216091/100000000 : ℝ)|=(18216091/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386900177/10000000000 : ℝ)|^2187 ≤ (8917576681621/20000000000000 : ℝ)^1675
        have hw : |(5386900177/10000000000 : ℝ)|=(5386900177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693449891/5000000000 : ℝ)|^2187 ≤ (22293939569637/50000000000000 : ℝ)^1675
        have hw : |(2693449891/5000000000 : ℝ)|=(2693449891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_1 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (26429743/50000000 : ℝ)*x 0 + (-1960240147/10000000000 : ℝ)*x 1 + (1346724959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26429743/50000000 : ℝ)^2187 ≤ (21750010618971/50000000000000 : ℝ)^1675 := by
    have hnat : (26429743 : ℕ)^2187*50000000000000^1675 ≤ 21750010618971^1675*50000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26429743 50000000 21750010618971 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1960240147/10000000000 : ℝ)^2187 ≤ (5956049514649/50000000000000 : ℝ)^1675 := by
    have hnat : (1960240147 : ℕ)^2187*50000000000000^1675 ≤ 5956049514649^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960240147 10000000000 5956049514649 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346724959/2500000000 : ℝ)^2187 ≤ (44587879722861/100000000000000 : ℝ)^1675 := by
    have hnat : (1346724959 : ℕ)^2187*100000000000000^1675 ≤ 44587879722861^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346724959 2500000000 44587879722861 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26429743/50000000 : ℝ), (-1960240147/10000000000 : ℝ), (1346724959/2500000000 : ℝ)] ![(21750010618971/50000000000000 : ℝ), (5956049514649/50000000000000 : ℝ), (44587879722861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26429743/50000000 : ℝ)|^2187 ≤ (21750010618971/50000000000000 : ℝ)^1675
        have hw : |(26429743/50000000 : ℝ)|=(26429743/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1960240147/10000000000 : ℝ)|^2187 ≤ (5956049514649/50000000000000 : ℝ)^1675
        have hw : |(-1960240147/10000000000 : ℝ)|=(1960240147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346724959/2500000000 : ℝ)|^2187 ≤ (44587879722861/100000000000000 : ℝ)^1675
        have hw : |(1346724959/2500000000 : ℝ)|=(1346724959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_2 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321487003/2500000000 : ℝ)*x 0 + (5386900049/10000000000 : ℝ)*x 1 + (-1960240653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321487003/2500000000 : ℝ)^2187 ≤ (43500014919969/100000000000000 : ℝ)^1675 := by
    have hnat : (1321487003 : ℕ)^2187*100000000000000^1675 ≤ 43500014919969^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321487003 2500000000 43500014919969 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386900049/10000000000 : ℝ)^2187 ≤ (11146970506197/25000000000000 : ℝ)^1675 := by
    have hnat : (5386900049 : ℕ)^2187*25000000000000^1675 ≤ 11146970506197^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386900049 10000000000 11146970506197 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960240653/10000000000 : ℝ)^2187 ≤ (5956051522047/50000000000000 : ℝ)^1675 := by
    have hnat : (1960240653 : ℕ)^2187*50000000000000^1675 ≤ 5956051522047^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960240653 10000000000 5956051522047 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321487003/2500000000 : ℝ), (5386900049/10000000000 : ℝ), (-1960240653/10000000000 : ℝ)] ![(43500014919969/100000000000000 : ℝ), (11146970506197/25000000000000 : ℝ), (5956051522047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321487003/2500000000 : ℝ)|^2187 ≤ (43500014919969/100000000000000 : ℝ)^1675
        have hw : |(1321487003/2500000000 : ℝ)|=(1321487003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386900049/10000000000 : ℝ)|^2187 ≤ (11146970506197/25000000000000 : ℝ)^1675
        have hw : |(5386900049/10000000000 : ℝ)|=(5386900049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1960240653/10000000000 : ℝ)|^2187 ≤ (5956051522047/50000000000000 : ℝ)^1675
        have hw : |(-1960240653/10000000000 : ℝ)|=(1960240653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_3 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4454747341/10000000000 : ℝ)*x 0 + (1059643593/2500000000 : ℝ)*x 1 + (4238574673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4454747341/10000000000 : ℝ)^2187 ≤ (34791908360137/100000000000000 : ℝ)^1675 := by
    have hnat : (4454747341 : ℕ)^2187*100000000000000^1675 ≤ 34791908360137^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454747341 10000000000 34791908360137 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059643593/2500000000 : ℝ)^2187 ≤ (8151011074839/25000000000000 : ℝ)^1675 := by
    have hnat : (1059643593 : ℕ)^2187*25000000000000^1675 ≤ 8151011074839^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059643593 2500000000 8151011074839 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238574673/10000000000 : ℝ)^2187 ≤ (16302023661227/50000000000000 : ℝ)^1675 := by
    have hnat : (4238574673 : ℕ)^2187*50000000000000^1675 ≤ 16302023661227^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238574673 10000000000 16302023661227 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4454747341/10000000000 : ℝ), (1059643593/2500000000 : ℝ), (4238574673/10000000000 : ℝ)] ![(34791908360137/100000000000000 : ℝ), (8151011074839/25000000000000 : ℝ), (16302023661227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4454747341/10000000000 : ℝ)|^2187 ≤ (34791908360137/100000000000000 : ℝ)^1675
        have hw : |(4454747341/10000000000 : ℝ)|=(4454747341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059643593/2500000000 : ℝ)|^2187 ≤ (8151011074839/25000000000000 : ℝ)^1675
        have hw : |(1059643593/2500000000 : ℝ)|=(1059643593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238574673/10000000000 : ℝ)|^2187 ≤ (16302023661227/50000000000000 : ℝ)^1675
        have hw : |(4238574673/10000000000 : ℝ)|=(4238574673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_4 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147864941/10000000000 : ℝ)*x 0 + (2633146793/5000000000 : ℝ)*x 1 + (5266293457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147864941/10000000000 : ℝ)^2187 ≤ (3355524788339/25000000000000 : ℝ)^1675 := by
    have hnat : (2147864941 : ℕ)^2187*25000000000000^1675 ≤ 3355524788339^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147864941 10000000000 3355524788339 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633146793/5000000000 : ℝ)^2187 ≤ (43288951111171/100000000000000 : ℝ)^1675 := by
    have hnat : (2633146793 : ℕ)^2187*100000000000000^1675 ≤ 43288951111171^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633146793 5000000000 43288951111171 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266293457/10000000000 : ℝ)^2187 ≤ (21644474863331/50000000000000 : ℝ)^1675 := by
    have hnat : (5266293457 : ℕ)^2187*50000000000000^1675 ≤ 21644474863331^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266293457 10000000000 21644474863331 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147864941/10000000000 : ℝ), (2633146793/5000000000 : ℝ), (5266293457/10000000000 : ℝ)] ![(3355524788339/25000000000000 : ℝ), (43288951111171/100000000000000 : ℝ), (21644474863331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147864941/10000000000 : ℝ)|^2187 ≤ (3355524788339/25000000000000 : ℝ)^1675
        have hw : |(-2147864941/10000000000 : ℝ)|=(2147864941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633146793/5000000000 : ℝ)|^2187 ≤ (43288951111171/100000000000000 : ℝ)^1675
        have hw : |(2633146793/5000000000 : ℝ)|=(2633146793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266293457/10000000000 : ℝ)|^2187 ≤ (21644474863331/50000000000000 : ℝ)^1675
        have hw : |(5266293457/10000000000 : ℝ)|=(5266293457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_5 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5370406411/10000000000 : ℝ)*x 0 + (-2009111827/10000000000 : ℝ)*x 1 + (210651737/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370406411/10000000000 : ℝ)^2187 ≤ (44409715981807/100000000000000 : ℝ)^1675 := by
    have hnat : (5370406411 : ℕ)^2187*100000000000000^1675 ≤ 44409715981807^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370406411 10000000000 44409715981807 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2009111827/10000000000 : ℝ)^2187 ≤ (1230133461883/10000000000000 : ℝ)^1675 := by
    have hnat : (2009111827 : ℕ)^2187*10000000000000^1675 ≤ 1230133461883^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009111827 10000000000 1230133461883 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210651737/400000000 : ℝ)^2187 ≤ (21644474691609/50000000000000 : ℝ)^1675 := by
    have hnat : (210651737 : ℕ)^2187*50000000000000^1675 ≤ 21644474691609^1675*400000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210651737 400000000 21644474691609 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370406411/10000000000 : ℝ), (-2009111827/10000000000 : ℝ), (210651737/400000000 : ℝ)] ![(44409715981807/100000000000000 : ℝ), (1230133461883/10000000000000 : ℝ), (21644474691609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370406411/10000000000 : ℝ)|^2187 ≤ (44409715981807/100000000000000 : ℝ)^1675
        have hw : |(5370406411/10000000000 : ℝ)|=(5370406411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2009111827/10000000000 : ℝ)|^2187 ≤ (1230133461883/10000000000000 : ℝ)^1675
        have hw : |(-2009111827/10000000000 : ℝ)|=(2009111827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210651737/400000000 : ℝ)|^2187 ≤ (21644474691609/50000000000000 : ℝ)^1675
        have hw : |(210651737/400000000 : ℝ)|=(210651737/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_6 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685203217/5000000000 : ℝ)*x 0 + (1316573419/2500000000 : ℝ)*x 1 + (-100455573/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685203217/5000000000 : ℝ)^2187 ≤ (44409716230139/100000000000000 : ℝ)^1675 := by
    have hnat : (2685203217 : ℕ)^2187*100000000000000^1675 ≤ 44409716230139^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685203217 5000000000 44409716230139 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316573419/2500000000 : ℝ)^2187 ≤ (43288952077107/100000000000000 : ℝ)^1675 := by
    have hnat : (1316573419 : ℕ)^2187*100000000000000^1675 ≤ 43288952077107^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316573419 2500000000 43288952077107 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100455573/500000000 : ℝ)^2187 ≤ (12301331684911/100000000000000 : ℝ)^1675 := by
    have hnat : (100455573 : ℕ)^2187*100000000000000^1675 ≤ 12301331684911^1675*500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100455573 500000000 12301331684911 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685203217/5000000000 : ℝ), (1316573419/2500000000 : ℝ), (-100455573/500000000 : ℝ)] ![(44409716230139/100000000000000 : ℝ), (43288952077107/100000000000000 : ℝ), (12301331684911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685203217/5000000000 : ℝ)|^2187 ≤ (44409716230139/100000000000000 : ℝ)^1675
        have hw : |(2685203217/5000000000 : ℝ)|=(2685203217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316573419/2500000000 : ℝ)|^2187 ≤ (43288952077107/100000000000000 : ℝ)^1675
        have hw : |(1316573419/2500000000 : ℝ)|=(1316573419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100455573/500000000 : ℝ)|^2187 ≤ (12301331684911/100000000000000 : ℝ)^1675
        have hw : |(-100455573/500000000 : ℝ)|=(100455573/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_7 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (520063083/1250000000 : ℝ)*x 0 + (438564437/1000000000 : ℝ)*x 1 + (274102793/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520063083/1250000000 : ℝ)^2187 ≤ (31822166942881/100000000000000 : ℝ)^1675 := by
    have hnat : (520063083 : ℕ)^2187*100000000000000^1675 ≤ 31822166942881^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520063083 1250000000 31822166942881 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438564437/1000000000 : ℝ)^2187 ≤ (34088914911203/100000000000000 : ℝ)^1675 := by
    have hnat : (438564437 : ℕ)^2187*100000000000000^1675 ≤ 34088914911203^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438564437 1000000000 34088914911203 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274102793/625000000 : ℝ)^2187 ≤ (17044459069257/50000000000000 : ℝ)^1675 := by
    have hnat : (274102793 : ℕ)^2187*50000000000000^1675 ≤ 17044459069257^1675*625000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274102793 625000000 17044459069257 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520063083/1250000000 : ℝ), (438564437/1000000000 : ℝ), (274102793/625000000 : ℝ)] ![(31822166942881/100000000000000 : ℝ), (34088914911203/100000000000000 : ℝ), (17044459069257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520063083/1250000000 : ℝ)|^2187 ≤ (31822166942881/100000000000000 : ℝ)^1675
        have hw : |(520063083/1250000000 : ℝ)|=(520063083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438564437/1000000000 : ℝ)|^2187 ≤ (34088914911203/100000000000000 : ℝ)^1675
        have hw : |(438564437/1000000000 : ℝ)|=(438564437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274102793/625000000 : ℝ)|^2187 ≤ (17044459069257/50000000000000 : ℝ)^1675
        have hw : |(274102793/625000000 : ℝ)|=(274102793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_8 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079179421/10000000000 : ℝ)*x 0 + (5182937739/10000000000 : ℝ)*x 1 + (675110441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079179421/10000000000 : ℝ)^2187 ≤ (12864440007473/100000000000000 : ℝ)^1675 := by
    have hnat : (2079179421 : ℕ)^2187*100000000000000^1675 ≤ 12864440007473^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079179421 10000000000 12864440007473 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182937739/10000000000 : ℝ)^2187 ≤ (21198248111547/50000000000000 : ℝ)^1675 := by
    have hnat : (5182937739 : ℕ)^2187*50000000000000^1675 ≤ 21198248111547^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182937739 10000000000 21198248111547 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675110441/1250000000 : ℝ)^2187 ≤ (8947812749841/20000000000000 : ℝ)^1675 := by
    have hnat : (675110441 : ℕ)^2187*20000000000000^1675 ≤ 8947812749841^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675110441 1250000000 8947812749841 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079179421/10000000000 : ℝ), (5182937739/10000000000 : ℝ), (675110441/1250000000 : ℝ)] ![(12864440007473/100000000000000 : ℝ), (21198248111547/50000000000000 : ℝ), (8947812749841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079179421/10000000000 : ℝ)|^2187 ≤ (12864440007473/100000000000000 : ℝ)^1675
        have hw : |(-2079179421/10000000000 : ℝ)|=(2079179421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182937739/10000000000 : ℝ)|^2187 ≤ (21198248111547/50000000000000 : ℝ)^1675
        have hw : |(5182937739/10000000000 : ℝ)|=(5182937739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675110441/1250000000 : ℝ)|^2187 ≤ (8947812749841/20000000000000 : ℝ)^1675
        have hw : |(675110441/1250000000 : ℝ)|=(675110441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_9 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (527615193/1000000000 : ℝ)*x 0 + (-1954446719/10000000000 : ℝ)*x 1 + (1350220799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527615193/1000000000 : ℝ)^2187 ≤ (43394787281969/100000000000000 : ℝ)^1675 := by
    have hnat : (527615193 : ℕ)^2187*100000000000000^1675 ≤ 43394787281969^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527615193 1000000000 43394787281969 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954446719/10000000000 : ℝ)^2187 ≤ (11866152548689/100000000000000 : ℝ)^1675 := by
    have hnat : (1954446719 : ℕ)^2187*100000000000000^1675 ≤ 11866152548689^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954446719 10000000000 11866152548689 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350220799/2500000000 : ℝ)^2187 ≤ (44739060158381/100000000000000 : ℝ)^1675 := by
    have hnat : (1350220799 : ℕ)^2187*100000000000000^1675 ≤ 44739060158381^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350220799 2500000000 44739060158381 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527615193/1000000000 : ℝ), (-1954446719/10000000000 : ℝ), (1350220799/2500000000 : ℝ)] ![(43394787281969/100000000000000 : ℝ), (11866152548689/100000000000000 : ℝ), (44739060158381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527615193/1000000000 : ℝ)|^2187 ≤ (43394787281969/100000000000000 : ℝ)^1675
        have hw : |(527615193/1000000000 : ℝ)|=(527615193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954446719/10000000000 : ℝ)|^2187 ≤ (11866152548689/100000000000000 : ℝ)^1675
        have hw : |(-1954446719/10000000000 : ℝ)|=(1954446719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350220799/2500000000 : ℝ)|^2187 ≤ (44739060158381/100000000000000 : ℝ)^1675
        have hw : |(1350220799/2500000000 : ℝ)|=(1350220799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_10 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (329759493/625000000 : ℝ)*x 0 + (5400883343/10000000000 : ℝ)*x 1 + (-78177863/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329759493/625000000 : ℝ)^2187 ≤ (43394786830941/100000000000000 : ℝ)^1675 := by
    have hnat : (329759493 : ℕ)^2187*100000000000000^1675 ≤ 43394786830941^1675*625000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329759493 625000000 43394786830941 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400883343/10000000000 : ℝ)^2187 ≤ (22369530874147/50000000000000 : ℝ)^1675 := by
    have hnat : (5400883343 : ℕ)^2187*50000000000000^1675 ≤ 22369530874147^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400883343 10000000000 22369530874147 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78177863/400000000 : ℝ)^2187 ≤ (2966537851793/25000000000000 : ℝ)^1675 := by
    have hnat : (78177863 : ℕ)^2187*25000000000000^1675 ≤ 2966537851793^1675*400000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78177863 400000000 2966537851793 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329759493/625000000 : ℝ), (5400883343/10000000000 : ℝ), (-78177863/400000000 : ℝ)] ![(43394786830941/100000000000000 : ℝ), (22369530874147/50000000000000 : ℝ), (2966537851793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329759493/625000000 : ℝ)|^2187 ≤ (43394786830941/100000000000000 : ℝ)^1675
        have hw : |(329759493/625000000 : ℝ)|=(329759493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400883343/10000000000 : ℝ)|^2187 ≤ (22369530874147/50000000000000 : ℝ)^1675
        have hw : |(5400883343/10000000000 : ℝ)|=(5400883343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78177863/400000000 : ℝ)|^2187 ≤ (2966537851793/25000000000000 : ℝ)^1675
        have hw : |(-78177863/400000000 : ℝ)|=(78177863/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_11 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (561038157/1250000000 : ℝ)*x 0 + (527688483/1250000000 : ℝ)*x 1 + (1055377233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (561038157/1250000000 : ℝ)^2187 ≤ (35134504899909/100000000000000 : ℝ)^1675 := by
    have hnat : (561038157 : ℕ)^2187*100000000000000^1675 ≤ 35134504899909^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561038157 1250000000 35134504899909 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527688483/1250000000 : ℝ)^2187 ≤ (32432742188387/100000000000000 : ℝ)^1675 := by
    have hnat : (527688483 : ℕ)^2187*100000000000000^1675 ≤ 32432742188387^1675*1250000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527688483 1250000000 32432742188387 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055377233/2500000000 : ℝ)^2187 ≤ (32432752901639/100000000000000 : ℝ)^1675 := by
    have hnat : (1055377233 : ℕ)^2187*100000000000000^1675 ≤ 32432752901639^1675*2500000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055377233 2500000000 32432752901639 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(561038157/1250000000 : ℝ), (527688483/1250000000 : ℝ), (1055377233/2500000000 : ℝ)] ![(35134504899909/100000000000000 : ℝ), (32432742188387/100000000000000 : ℝ), (32432752901639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(561038157/1250000000 : ℝ)|^2187 ≤ (35134504899909/100000000000000 : ℝ)^1675
        have hw : |(561038157/1250000000 : ℝ)|=(561038157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527688483/1250000000 : ℝ)|^2187 ≤ (32432742188387/100000000000000 : ℝ)^1675
        have hw : |(527688483/1250000000 : ℝ)|=(527688483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055377233/2500000000 : ℝ)|^2187 ≤ (32432752901639/100000000000000 : ℝ)^1675
        have hw : |(1055377233/2500000000 : ℝ)|=(1055377233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_12 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-7384769/39062500 : ℝ)*x 0 + (5468202163/10000000000 : ℝ)*x 1 + (5255174969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7384769/39062500 : ℝ)^2187 ≤ (2272358991451/20000000000000 : ℝ)^1675 := by
    have hnat : (7384769 : ℕ)^2187*20000000000000^1675 ≤ 2272358991451^1675*39062500^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7384769 39062500 2272358991451 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468202163/10000000000 : ℝ)^2187 ≤ (9093709468371/20000000000000 : ℝ)^1675 := by
    have hnat : (5468202163 : ℕ)^2187*20000000000000^1675 ≤ 9093709468371^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468202163 10000000000 9093709468371 20000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255174969/10000000000 : ℝ)^2187 ≤ (69071452297/160000000000 : ℝ)^1675 := by
    have hnat : (5255174969 : ℕ)^2187*160000000000^1675 ≤ 69071452297^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255174969 10000000000 69071452297 160000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7384769/39062500 : ℝ), (5468202163/10000000000 : ℝ), (5255174969/10000000000 : ℝ)] ![(2272358991451/20000000000000 : ℝ), (9093709468371/20000000000000 : ℝ), (69071452297/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7384769/39062500 : ℝ)|^2187 ≤ (2272358991451/20000000000000 : ℝ)^1675
        have hw : |(-7384769/39062500 : ℝ)|=(7384769/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468202163/10000000000 : ℝ)|^2187 ≤ (9093709468371/20000000000000 : ℝ)^1675
        have hw : |(5468202163/10000000000 : ℝ)|=(5468202163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255174969/10000000000 : ℝ)|^2187 ≤ (69071452297/160000000000 : ℝ)^1675
        have hw : |(5255174969/10000000000 : ℝ)|=(5255174969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_13 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378190839/10000000000 : ℝ)*x 0 + (-201351673/1000000000 : ℝ)*x 1 + (1051034961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378190839/10000000000 : ℝ)^2187 ≤ (22246891698059/50000000000000 : ℝ)^1675 := by
    have hnat : (5378190839 : ℕ)^2187*50000000000000^1675 ≤ 22246891698059^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378190839 10000000000 22246891698059 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201351673/1000000000 : ℝ)^2187 ≤ (1233656066267/10000000000000 : ℝ)^1675 := by
    have hnat : (201351673 : ℕ)^2187*10000000000000^1675 ≤ 1233656066267^1675*1000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201351673 1000000000 1233656066267 10000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051034961/2000000000 : ℝ)^2187 ≤ (10792413981653/25000000000000 : ℝ)^1675 := by
    have hnat : (1051034961 : ℕ)^2187*25000000000000^1675 ≤ 10792413981653^1675*2000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051034961 2000000000 10792413981653 25000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378190839/10000000000 : ℝ), (-201351673/1000000000 : ℝ), (1051034961/2000000000 : ℝ)] ![(22246891698059/50000000000000 : ℝ), (1233656066267/10000000000000 : ℝ), (10792413981653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378190839/10000000000 : ℝ)|^2187 ≤ (22246891698059/50000000000000 : ℝ)^1675
        have hw : |(5378190839/10000000000 : ℝ)|=(5378190839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-201351673/1000000000 : ℝ)|^2187 ≤ (1233656066267/10000000000000 : ℝ)^1675
        have hw : |(-201351673/1000000000 : ℝ)|=(201351673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051034961/2000000000 : ℝ)|^2187 ≤ (10792413981653/25000000000000 : ℝ)^1675
        have hw : |(1051034961/2000000000 : ℝ)|=(1051034961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_14 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215127641/400000000 : ℝ)*x 0 + (2627587349/5000000000 : ℝ)*x 1 + (-2013516623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215127641/400000000 : ℝ)^2187 ≤ (22246892702629/50000000000000 : ℝ)^1675 := by
    have hnat : (215127641 : ℕ)^2187*50000000000000^1675 ≤ 22246892702629^1675*400000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215127641 400000000 22246892702629 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627587349/5000000000 : ℝ)^2187 ≤ (21584827389481/50000000000000 : ℝ)^1675 := by
    have hnat : (2627587349 : ℕ)^2187*50000000000000^1675 ≤ 21584827389481^1675*5000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627587349 5000000000 21584827389481 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013516623/10000000000 : ℝ)^2187 ≤ (771034987919/6250000000000 : ℝ)^1675 := by
    have hnat : (2013516623 : ℕ)^2187*6250000000000^1675 ≤ 771034987919^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013516623 10000000000 771034987919 6250000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215127641/400000000 : ℝ), (2627587349/5000000000 : ℝ), (-2013516623/10000000000 : ℝ)] ![(22246892702629/50000000000000 : ℝ), (21584827389481/50000000000000 : ℝ), (771034987919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215127641/400000000 : ℝ)|^2187 ≤ (22246892702629/50000000000000 : ℝ)^1675
        have hw : |(215127641/400000000 : ℝ)|=(215127641/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627587349/5000000000 : ℝ)|^2187 ≤ (21584827389481/50000000000000 : ℝ)^1675
        have hw : |(2627587349/5000000000 : ℝ)|=(2627587349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2013516623/10000000000 : ℝ)|^2187 ≤ (771034987919/6250000000000 : ℝ)^1675
        have hw : |(-2013516623/10000000000 : ℝ)|=(2013516623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1414_box_15 (p : ℝ) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4132929307/10000000000 : ℝ)*x 0 + (175967673/400000000 : ℝ)*x 1 + (35193533/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132929307/10000000000 : ℝ)^2187 ≤ (15773531118159/50000000000000 : ℝ)^1675 := by
    have hnat : (4132929307 : ℕ)^2187*50000000000000^1675 ≤ 15773531118159^1675*10000000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132929307 10000000000 15773531118159 50000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175967673/400000000 : ℝ)^2187 ≤ (34226469884567/100000000000000 : ℝ)^1675 := by
    have hnat : (175967673 : ℕ)^2187*100000000000000^1675 ≤ 34226469884567^1675*400000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175967673 400000000 34226469884567 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35193533/80000000 : ℝ)^2187 ≤ (34226467852897/100000000000000 : ℝ)^1675 := by
    have hnat : (35193533 : ℕ)^2187*100000000000000^1675 ≤ 34226467852897^1675*80000000^2187 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35193533 80000000 34226467852897 100000000000000 2187 1675 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2187/512 : ℝ)) 2187 1675 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132929307/10000000000 : ℝ), (175967673/400000000 : ℝ), (35193533/80000000 : ℝ)] ![(15773531118159/50000000000000 : ℝ), (34226469884567/100000000000000 : ℝ), (34226467852897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132929307/10000000000 : ℝ)|^2187 ≤ (15773531118159/50000000000000 : ℝ)^1675
        have hw : |(4132929307/10000000000 : ℝ)|=(4132929307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175967673/400000000 : ℝ)|^2187 ≤ (34226469884567/100000000000000 : ℝ)^1675
        have hw : |(175967673/400000000 : ℝ)|=(175967673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35193533/80000000 : ℝ)|^2187 ≤ (34226467852897/100000000000000 : ℝ)^1675
        have hw : |(35193533/80000000 : ℝ)|=(35193533/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1414_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62891/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59083/100000 : ℝ) ∧ (16073/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21157/25000 : ℝ) := by
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
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (9070697176664983/100000000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^4373 ≤ (9070697176664983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11309 : ℕ)^4373*100000000000000000000^1024 ≤ 9070697176664983^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 9070697176664983 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (9070697176664983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (4373/1024 : ℝ) ≤ (28196427412575319/100000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^4373 ≤ (28196427412575319/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14749 : ℕ)^4373*100000000000000000000^1024 ≤ 28196427412575319^1024*100000^4373 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 28196427412575319 100000000000000000000 4373 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (28196427412575319/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009070697176664983/50000000000000000000 : ℝ) ≤ (20000849553967/20000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50009070697176664983/50000000000000000000 : ℝ)^1024 ≤ (20000849553967/20000000000000 : ℝ)^4373 := by
      have hnat : (50009070697176664983 : ℕ)^1024*20000000000000^4373 ≤ 20000849553967^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009070697176664983 50000000000000000000 20000849553967 20000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20000849553967/20000000000000 : ℝ)) (X := (50009070697176664983/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018633562294620151/50000000000000000000 : ℝ) ≤ (10000872538098043/10000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50018633562294620151/50000000000000000000 : ℝ)^1024 ≤ (10000872538098043/10000000000000000 : ℝ)^4373 := by
      have hnat : (50018633562294620151 : ℕ)^1024*10000000000000000^4373 ≤ 10000872538098043^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018633562294620151 50000000000000000000 10000872538098043 10000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000872538098043/10000000000000000 : ℝ)) (X := (50018633562294620151/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028196427412575319/50000000000000000000 : ℝ) ≤ (5000660149606293/5000000000000000 : ℝ) ^ (4373/1024 : ℝ) := by
    have hpowers : (50028196427412575319/50000000000000000000 : ℝ)^1024 ≤ (5000660149606293/5000000000000000 : ℝ)^4373 := by
      have hnat : (50028196427412575319 : ℕ)^1024*5000000000000000^4373 ≤ 5000660149606293^4373*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028196427412575319 50000000000000000000 5000660149606293 5000000000000000 1024 4373 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000660149606293/5000000000000000 : ℝ)) (X := (50028196427412575319/50000000000000000000 : ℝ)) (by norm_num) 4373 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9070697176664983/100000000000000000000 : ℝ) ≤ ((399899229906215191/400000000000000000 : ℝ)+2*(447761114543/344000000000000 : ℝ)*(11309/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (399899229906215191/400000000000000000 : ℝ)+2*(447761114543/344000000000000 : ℝ)*(11309/100000 : ℝ)=(20000849553967/20000000000000 : ℝ) by norm_num, show 1+2*(9070697176664983/100000000000000000000 : ℝ)=(50009070697176664983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28196427412575319/100000000000000000000 : ℝ)+(9070697176664983/100000000000000000000 : ℝ) ≤ ((399899229906215191/400000000000000000 : ℝ)+(447761114543/344000000000000 : ℝ)*((14749/100000 : ℝ)+(11309/100000 : ℝ)))^(4373/1024 : ℝ) := by
    rw [show (399899229906215191/400000000000000000 : ℝ)+(447761114543/344000000000000 : ℝ)*((14749/100000 : ℝ)+(11309/100000 : ℝ))=(10000872538098043/10000000000000000 : ℝ) by norm_num, show 1+(28196427412575319/100000000000000000000 : ℝ)+(9070697176664983/100000000000000000000 : ℝ)=(50018633562294620151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28196427412575319/100000000000000000000 : ℝ) ≤ ((399899229906215191/400000000000000000 : ℝ)+2*(447761114543/344000000000000 : ℝ)*(14749/100000 : ℝ))^(4373/1024 : ℝ) := by
    rw [show (399899229906215191/400000000000000000 : ℝ)+2*(447761114543/344000000000000 : ℝ)*(14749/100000 : ℝ)=(5000660149606293/5000000000000000 : ℝ) by norm_num, show 1+2*(28196427412575319/100000000000000000000 : ℝ)=(50028196427412575319/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (399899229906215191/400000000000000000 : ℝ)*(X 1 0+X 2 0)+(447761114543/344000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (399899229906215191/400000000000000000 : ℝ)) (alpha := (447761114543/344000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (399899229906215191/400000000000000000 : ℝ)*(X 0 1+X 2 1)+(447761114543/344000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (399899229906215191/400000000000000000 : ℝ)) (alpha := (447761114543/344000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (399899229906215191/400000000000000000 : ℝ)*(X 0 2+X 1 2)+(447761114543/344000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4373/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (399899229906215191/400000000000000000 : ℝ)) (alpha := (447761114543/344000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-18216091/100000000 : ℝ)*X 0 0+(5386900177/10000000000 : ℝ)*X 0 1+(2693449891/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26429743/50000000 : ℝ)*X 1 0+(-1960240147/10000000000 : ℝ)*X 1 1+(1346724959/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321487003/2500000000 : ℝ)*X 2 0+(5386900049/10000000000 : ℝ)*X 2 1+(-1960240653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4454747341/10000000000 : ℝ)*X 0 0+(1059643593/2500000000 : ℝ)*X 0 1+(4238574673/10000000000 : ℝ)*X 0 2+(4454747341/10000000000 : ℝ)*X 1 0+(1059643593/2500000000 : ℝ)*X 1 1+(4238574673/10000000000 : ℝ)*X 1 2+(4454747341/10000000000 : ℝ)*X 2 0+(1059643593/2500000000 : ℝ)*X 2 1+(4238574673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2147864941/10000000000 : ℝ)*X 0 0+(2633146793/5000000000 : ℝ)*X 0 1+(5266293457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5370406411/10000000000 : ℝ)*X 1 0+(-2009111827/10000000000 : ℝ)*X 1 1+(210651737/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685203217/5000000000 : ℝ)*X 2 0+(1316573419/2500000000 : ℝ)*X 2 1+(-100455573/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((520063083/1250000000 : ℝ)*X 0 0+(438564437/1000000000 : ℝ)*X 0 1+(274102793/625000000 : ℝ)*X 0 2+(520063083/1250000000 : ℝ)*X 1 0+(438564437/1000000000 : ℝ)*X 1 1+(274102793/625000000 : ℝ)*X 1 2+(520063083/1250000000 : ℝ)*X 2 0+(438564437/1000000000 : ℝ)*X 2 1+(274102793/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2079179421/10000000000 : ℝ)*X 0 0+(5182937739/10000000000 : ℝ)*X 0 1+(675110441/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((527615193/1000000000 : ℝ)*X 1 0+(-1954446719/10000000000 : ℝ)*X 1 1+(1350220799/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((329759493/625000000 : ℝ)*X 2 0+(5400883343/10000000000 : ℝ)*X 2 1+(-78177863/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((561038157/1250000000 : ℝ)*X 0 0+(527688483/1250000000 : ℝ)*X 0 1+(1055377233/2500000000 : ℝ)*X 0 2+(561038157/1250000000 : ℝ)*X 1 0+(527688483/1250000000 : ℝ)*X 1 1+(1055377233/2500000000 : ℝ)*X 1 2+(561038157/1250000000 : ℝ)*X 2 0+(527688483/1250000000 : ℝ)*X 2 1+(1055377233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-7384769/39062500 : ℝ)*X 0 0+(5468202163/10000000000 : ℝ)*X 0 1+(5255174969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378190839/10000000000 : ℝ)*X 1 0+(-201351673/1000000000 : ℝ)*X 1 1+(1051034961/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215127641/400000000 : ℝ)*X 2 0+(2627587349/5000000000 : ℝ)*X 2 1+(-2013516623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4132929307/10000000000 : ℝ)*X 0 0+(175967673/400000000 : ℝ)*X 0 1+(35193533/80000000 : ℝ)*X 0 2+(4132929307/10000000000 : ℝ)*X 1 0+(175967673/400000000 : ℝ)*X 1 1+(35193533/80000000 : ℝ)*X 1 2+(4132929307/10000000000 : ℝ)*X 2 0+(175967673/400000000 : ℝ)*X 2 1+(35193533/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1414_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62891/100000 : ℝ) ≤ (-540837013703332674065958796166883/860000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9584019/12500000000000 : ℝ)*(upper0) + (26391033/100000000000000 : ℝ)*(lower1) + (62444981/50000000000000 : ℝ)*(lower2) + (43013877/100000000000000 : ℝ)*(lower3) + (3000302655462197/100000000000000 : ℝ)*(major0) + (3000302655462197/100000000000000 : ℝ)*(major1) + (3000302655462197/100000000000000 : ℝ)*(major2) + (1254122939/50000000000000 : ℝ)*(sp1) + (4117488463267/100000000000 : ℝ)*(sp4) + (257343028672903/6250000000000 : ℝ)*(sp5) + (2058684956474299/50000000000000 : ℝ)*(sp6) + (59502406839431/3125000000000 : ℝ)*(sp7) + (156484083/6250000000000 : ℝ)*(sp8) + (121054063729/100000000000000 : ℝ)*(sp14) + (59502406839431/3125000000000 : ℝ)*(f.failure) + (4117490967012327/100000000000000 : ℝ)*(f.sum) + (45377843670971/17200000000000000000000000000 : ℝ)*base65 + (14987967695556838961/1720000000000000000000000000000000 : ℝ)*base67 + (1657385019003161039/1720000000000000000000000000000000 : ℝ)*base70 + (30255615835076838961/1720000000000000000000000000000000 : ℝ)*base71 + (233602899990629/17200000000000000000000000000 : ℝ)*base74 + (15004763715716838961/1720000000000000000000000000000000 : ℝ)*base75 + (14886482169196838961/1720000000000000000000000000000000 : ℝ)*base77 + (58695455785003161039/1720000000000000000000000000000000 : ℝ)*base80 + (68551320268171/17200000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (2924243/312500000000000000000 : ℝ)*base90 + (2924243/312500000000000000000 : ℝ)*base92 + (2924243/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59083/100000 : ℝ) ≤ (127033879297424454303051985738869/215000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7457429/25000000000000 : ℝ)*(lower0) + (267899007/100000000000000 : ℝ)*(upper2) + (1758861/12500000000000 : ℝ)*(lower4) + (25388341/25000000000000 : ℝ)*(lower5) + (767851441415571/25000000000000 : ℝ)*(major0) + (767851441415571/25000000000000 : ℝ)*(major1) + (767851441415571/25000000000000 : ℝ)*(major2) + (2086956519896611/50000000000000 : ℝ)*(sp0) + (2086955481750719/50000000000000 : ℝ)*(sp1) + (260869705647321/6250000000000 : ℝ)*(sp2) + (974597432068763/50000000000000 : ℝ)*(sp3) + (2163427849/50000000000000 : ℝ)*(sp5) + (3100872513/50000000000000 : ℝ)*(sp7) + (450112783/20000000000000 : ℝ)*(sp12) + (243650133235319/12500000000000 : ℝ)*(f.failure) + (260869705647321/6250000000000 : ℝ)*(f.sum) + (46114025791947/4300000000000000000000000000 : ℝ)*base66 + (852963600440629623/430000000000000000000000000000000 : ℝ)*base67 + (4230920548979370377/430000000000000000000000000000000 : ℝ)*base70 + (5048808147669370377/430000000000000000000000000000000 : ℝ)*base72 + (25883122588947/4300000000000000000000000000 : ℝ)*base74 + (1861460837949370377/430000000000000000000000000000000 : ℝ)*base76 + (4405548337889370377/430000000000000000000000000000000 : ℝ)*base78 + (191644573690629623/430000000000000000000000000000000 : ℝ)*base79 + (10482394886347/4300000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (15187493/1250000000000000000000 : ℝ)*base89 + (15187493/1250000000000000000000 : ℝ)*base91 + (15187493/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16073/20000 : ℝ) ≤ (345581606376595196178964501862271/430000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73656867/100000000000000 : ℝ)*(upper0) + (74168697/100000000000000 : ℝ)*(lower1) + (4817729/25000000000000 : ℝ)*(upper2) + (24934069/12500000000000 : ℝ)*(lower3) + (5213219/10000000000000 : ℝ)*(lower5) + (1690053517610311/50000000000000 : ℝ)*(major0) + (1690053517610311/50000000000000 : ℝ)*(major1) + (1690053517610311/50000000000000 : ℝ)*(major2) + (3865650883/20000000000000 : ℝ)*(sp0) + (48318336819/100000000000000 : ℝ)*(sp3) + (286768364871249/6250000000000 : ℝ)*(sp8) + (2294156583097199/50000000000000 : ℝ)*(sp9) + (2294156583097199/50000000000000 : ℝ)*(sp10) + (134066457131117/6250000000000 : ℝ)*(sp11) + (536277908108673/25000000000000 : ℝ)*(f.failure) + (2294156583097199/50000000000000 : ℝ)*(f.sum) + (32057803771327/8600000000000000000000000000 : ℝ)*base66 + (18695463295020329243/860000000000000000000000000000000 : ℝ)*base67 + (11564103913739670757/860000000000000000000000000000000 : ℝ)*base70 + (10915992783180329243/860000000000000000000000000000000 : ℝ)*base71 + (66201267207527/8600000000000000000000000000 : ℝ)*base74 + (10980525249900329243/860000000000000000000000000000000 : ℝ)*base75 + (4878934438940329243/860000000000000000000000000000000 : ℝ)*base77 + (35057052104359670757/860000000000000000000000000000000 : ℝ)*base80 + (59389234099727/8600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7400131/2500000000000000000000 : ℝ)*base89 + (7400131/2500000000000000000000 : ℝ)*base91 + (7400131/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-21157/25000 : ℝ) ≤ (-9097285667805683005153141839687/10750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1115573/5000000000000 : ℝ)*(lower0) + (2619589/10000000000000 : ℝ)*(lower1) + (1851281/2000000000000 : ℝ)*(lower2) + (42717570714811/1250000000000 : ℝ)*(major0) + (42717570714811/1250000000000 : ℝ)*(major1) + (42717570714811/1250000000000 : ℝ)*(major2) + (744872089/20000000000000 : ℝ)*(sp0) + (136923875499/100000000000000 : ℝ)*(sp5) + (8135958343/6250000000000 : ℝ)*(sp6) + (19743383023/100000000000000 : ℝ)*(sp7) + (4694233833693539/100000000000000 : ℝ)*(sp12) + (2347050317089243/50000000000000 : ℝ)*(sp13) + (293381711420031/6250000000000 : ℝ)*(sp14) + (542190662665589/25000000000000 : ℝ)*(sp15) + (1084391197022689/50000000000000 : ℝ)*(f.failure) + (938847511610797/20000000000000 : ℝ)*(f.sum) + (1848504567747/215000000000000000000000000 : ℝ)*base66 + (209447903077087743/21500000000000000000000000000000 : ℝ)*base67 + (301320525457587743/21500000000000000000000000000000 : ℝ)*base69 + (95061311714587743/21500000000000000000000000000000 : ℝ)*base71 + (4072427976809/107500000000000000000000000 : ℝ)*base73 + (233105518441587743/21500000000000000000000000000000 : ℝ)*base75 + (68614240211087743/21500000000000000000000000000000 : ℝ)*base77 + (1512145620886087743/21500000000000000000000000000000 : ℝ)*base79 + (804615813367/215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (77481117/5000000000000000000000 : ℝ)*base90 + (77481117/5000000000000000000000 : ℝ)*base92 + (77481117/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1414_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62891/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59083/100000 : ℝ) else (16073/20000 : ℝ) ≤ X j i ∧ X j i ≤ (21157/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1414_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1414_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62891/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59083/100000 : ℝ) else (16073/20000 : ℝ) ≤ X j i ∧ X j i ≤ (21157/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1414_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1414_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4373/1024 : ℝ) ≤ p) (hpb : p ≤ (2187/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157572547/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62891/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59083/100000 : ℝ) else (16073/20000 : ℝ) ≤ X j i ∧ X j i ≤ (21157/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1414_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
